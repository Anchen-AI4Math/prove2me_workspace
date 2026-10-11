"""Stage FormalLog base proof node in a Windows-safe short immutable root."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path

import generate_formal_log_truncation_provider as formal
import generate_platform_provider_nodes as node_impl
import plan_formal_log_proof_nodes as plan
import stage_formal_log_base_node as base

TASK, ROOT, V = formal.TASK, formal.ROOT, formal.V
DEST = V / "flp3"
STAGE = DEST / "f1"
KEY = plan.NODE_KEYS["liftSeries_eq_toMvPowerSeries"]
SELF = Path(__file__).resolve()


class ShortDestination:
    """Redirect the generator's one node-directory join to the fixed short path."""
    def __truediv__(self, requested):
        expected = "OAI_PiExponent_FormalLogTruncation_liftSeries_eq_toMvPowerSeries"
        if requested != expected:
            raise ValueError("Unexpected node destination request: " + str(requested))
        return STAGE


def prepare():
    old_dest = node_impl.DEST
    try:
        node_impl.DEST = ShortDestination()
        generator = node_impl.ProviderNodeGenerator()
        generated = generator.generate(KEY)
    finally:
        node_impl.DEST = old_dest
    if (TASK / generated["stage"]).resolve() != STAGE.resolve():
        raise ValueError("Generator did not use the short attempt stage")
    manifest_path = STAGE / "manifest.json"
    manifest = formal.read(manifest_path)
    if manifest["child_nodes"]:
        raise ValueError("The base node must have no child dependency")
    certificates = [plan.certified_definition(row["source_module"], row["platform_module"])
                    for row in manifest["definition_dependency_witnesses"]]
    base_snapshot = STAGE / "SnapshotGenerated.lean"
    refs_output = STAGE / "proof-references.json"
    addon = base.proof_reference_addon(manifest["public_inline_ci_requests"], refs_output).encode()
    with_refs = STAGE / "SnapshotGeneratedWithRefs.lean"
    base.write_exact(with_refs, base_snapshot.read_bytes() + addon)
    certified_inputs_path = STAGE / "certified-inputs.json"
    base.write_exact(certified_inputs_path, {
        "schema_version": 1, "artifact_kind": "formal-log-base-node-certified-inputs",
        "node": KEY, "definition_certificates": certificates, "child_certificates": [],
        "validated_node": False, "Lean_started": False, "submission_ready": False})
    pins = {formal.rel(SELF): formal.sha(SELF), formal.rel(Path(base.__file__)): formal.sha(Path(base.__file__)),
            formal.rel(Path(plan.__file__)): formal.sha(Path(plan.__file__)),
            formal.rel(manifest_path): formal.sha(manifest_path),
            formal.rel(certified_inputs_path): formal.sha(certified_inputs_path)}
    for row in certificates:
        pins[row["certificate"]] = row["certificate_sha256"]
        pins[row["output_olean"]] = row["output_lean_sha256"]
    files = [next(STAGE.glob("Thm_*.lean")), next(STAGE.glob("Sol_*.lean")),
             STAGE / "SnapshotOriginal.lean", with_refs]
    compile_manifests = {}
    for index, source in enumerate(files, 1):
        imports = (["Lean", manifest["source_components"][0]["source_module"]]
                   if source.name == "SnapshotOriginal.lean" else manifest["imports"])
        path = STAGE / f"c{index}.json"
        base.write_exact(path, {"schema_version": 1,
            "artifact_kind": "formal-log-proof-node-file-import-certificate",
            "output": source.relative_to(ROOT).as_posix(), "output_sha256": formal.sha(source),
            "imports": imports, "input_hashes": pins, "runtime_sha256": manifest["runtime_sha256"],
            "node": KEY, "node_validated": False, "timeout_seconds": 300,
            "Lean_started": False, "submission_ready": False})
        compile_manifests[source.name] = {"manifest": formal.rel(path), "manifest_sha256": formal.sha(path)}
    preparation = {**generated, "attempt_root": formal.rel(DEST), "short_stage": formal.rel(STAGE),
        "prior_attempt": "verification/formal-log-proof-nodes-v2/OAI_PiExponent_FormalLogTruncation_liftSeries_eq_toMvPowerSeries",
        "prior_attempt_failure": "Windows MAX_PATH while writing the .lean.preflight.json sidecar after Lean completed",
        "base_snapshot": formal.rel(base_snapshot), "base_snapshot_sha256": formal.sha(base_snapshot),
        "generated_with_refs": formal.rel(with_refs), "generated_with_refs_sha256": formal.sha(with_refs),
        "generated_with_refs_prefix_bytes": base_snapshot.stat().st_size,
        "proof_reference_addon_sha256": base.sha_bytes(addon), "proof_reference_output": formal.rel(refs_output),
        "proof_reference_requests": ["solution", *[x["generated_name"] for x in manifest["public_inline_ci_requests"]]],
        "certified_definition_dependencies": len(certificates), "compile_manifests": compile_manifests,
        "exact_old_snapshot_prefix": True, "pure_python_prepared": True,
        "Lean_started": False, "validated": False, "submission_ready": False}
    base.write_exact(STAGE / "preparation.json", preparation)
    return preparation


def path_budget(preparation):
    paths = []
    for filename in preparation["compile_manifests"]:
        source = (STAGE / filename).resolve()
        paths.extend([source, Path(str(source) + ".preflight.json")])
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
        paths.append((V / "staged-preflight-logs" / (source.stem + "_" + stamp + ".log")).resolve())
    manifest = formal.read(STAGE / "manifest.json")
    output_paths = [ROOT / manifest["inline_type_json_outputs"][side] for side in ("original", "generated")]
    output_paths += [ROOT / manifest["public_inline_type_json_outputs"][side] for side in ("original", "generated")]
    output_paths += [STAGE / "original-type.json", STAGE / "generated-type.json", TASK / preparation["proof_reference_output"]]
    paths.extend(path.resolve() for path in output_paths)
    report = {str(path): len(str(path)) for path in paths}
    if max(report.values()) >= 240:
        raise ValueError("Short-stage compiler artifact exceeds conservative 239-character budget")
    return report


def check():
    preparation = formal.read(STAGE / "preparation.json")
    base_snapshot = TASK / preparation["base_snapshot"]
    extended = TASK / preparation["generated_with_refs"]
    if not extended.read_bytes().startswith(base_snapshot.read_bytes()):
        raise ValueError("Generated-with-refs lost the exact snapshot prefix")
    checked = {}
    for filename, row in preparation["compile_manifests"].items():
        source, mp = STAGE / filename, TASK / row["manifest"]
        if formal.sha(mp) != row["manifest_sha256"]:
            raise ValueError("Compilation manifest changed: " + filename)
        document = formal.read(mp)
        formal.runner.verify_manifest_inputs(document)
        formal.runner.verify_source_certificate(source, document)
        checked[filename] = len(formal.runner.certified_imports(source, document))
    budget = path_budget(preparation)
    return {"node": KEY, "short_stage": formal.rel(STAGE), "exact_snapshot_prefix": True,
            "file_and_import_pins_checked": True, "path_count": len(budget),
            "maximum_absolute_artifact_path_length": max(budget.values()),
            "files_and_import_counts": checked, "Lean_started": False,
            "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare else check(), indent=2))


if __name__ == "__main__":
    main()
