"""Stage the two local FormalLog successors of the proved f1 child.

Pure Python only.  This producer requires the actual imported-child kernel
certificate, but deliberately leaves the platform-parent gate pending: local
compilation is evidence for later publication, not authority to publish.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path

import generate_formal_log_truncation_provider as formal
import generate_platform_provider_nodes as node_impl
import plan_formal_log_proof_nodes as plan
import stage_formal_log_base_node as base
import validate_formal_log_proved_child as childcheck

TASK, ROOT, V = formal.TASK, formal.ROOT, formal.V
SELF = Path(__file__).resolve()
DEST = V / "flp3"

NODES = {
    "f2": plan.NODE_KEYS["logTail_mem_rationalWeightedIdeal"],
    "f3": plan.NODE_KEYS["shiftMap_truncatedFormalJet"],
}
EXPECTED_CHILD = plan.NODE_KEYS["liftSeries_eq_toMvPowerSeries"]
CHILD_STAGE = DEST / "c1"


class ShortDestination:
    def __init__(self, requested_slug, stage):
        self.requested_slug, self.stage = requested_slug, stage

    def __truediv__(self, requested):
        if requested != self.requested_slug:
            raise ValueError("Unexpected successor destination request: " + str(requested))
        return self.stage


def child_certificate():
    result = childcheck.validate_proved_child(CHILD_STAGE)
    data = result["certificate"]["data"]
    required = {
        "validated": True,
        "parent_node": EXPECTED_CHILD,
        "theorem_name": "OAI.PiExponent.FormalLogTruncation.liftSeries_eq_toMvPowerSeries",
        "Std3_only": True,
        "actual_imported_owner": True,
        "exact_certified_solution_rebinding": True,
    }
    if any(data.get(k) != v for k, v in required.items()):
        raise ValueError("The local f1 proved-child certificate is incomplete")
    return result


def repaired_refs_addon(requests, output):
    addon = base.proof_reference_addon(requests, output).encode()
    edits = [(b"def export (", b"def exportProofRefs ("),
             (b"FormalLogProofReferenceSnapshot.export ",
              b"FormalLogProofReferenceSnapshot.exportProofRefs ")]
    for old, new in edits:
        if addon.count(old) != 1 or addon.count(new) != 0:
            raise ValueError("Proof-reference identifier repair is not exact")
        addon = addon.replace(old, new, 1)
    return addon


def prepare(which):
    if which not in NODES:
        raise ValueError("Only f2/f3 are local successors of c1")
    child = child_certificate()
    key, stage = NODES[which], DEST / which
    generator = node_impl.ProviderNodeGenerator()
    theorem = generator.node_name(key)
    old_dest = node_impl.DEST
    try:
        node_impl.DEST = ShortDestination(theorem.replace(".", "_"), stage)
        generated = generator.generate(key)
    finally:
        node_impl.DEST = old_dest
    if (TASK / generated["stage"]).resolve() != stage.resolve():
        raise ValueError("Generator did not use the exact short successor stage")
    manifest_path = stage / "manifest.json"
    manifest = formal.read(manifest_path)
    if set(manifest["child_nodes"]) != {EXPECTED_CHILD}:
        raise ValueError("Successor does not have exactly the certified f1 child")
    if manifest["child_nodes"][EXPECTED_CHILD] != child["certificate"]["data"]["theorem_name"]:
        raise ValueError("Generated child theorem differs from the certified child")
    definitions = [plan.certified_definition(row["source_module"], row["platform_module"])
                   for row in manifest["definition_dependency_witnesses"]]
    base_snapshot = stage / "SnapshotGenerated.lean"
    refs_output = stage / "proof-references.json"
    addon = repaired_refs_addon(manifest["public_inline_ci_requests"], refs_output)
    with_refs = stage / "SnapshotGeneratedWithRefs.lean"
    base.write_exact(with_refs, base_snapshot.read_bytes() + addon)

    child_cert_path = TASK / child["certificate"]["path"]
    child_data = child["certificate"]["data"]
    certified_inputs = stage / "certified-inputs.json"
    child_row = {
        "node": EXPECTED_CHILD,
        "theorem_name": child_data["theorem_name"],
        "module": child_data["module"],
        "certificate": formal.rel(child_cert_path),
        "certificate_sha256": formal.sha(child_cert_path),
        "output_olean": child_data["output_olean"],
        "output_olean_sha256": child_data["output_olean_sha256"],
        "validated": True,
        "proof_axioms": "Std3",
    }
    base.write_exact(certified_inputs, {
        "schema_version": 1,
        "artifact_kind": "formal-log-successor-node-certified-inputs",
        "node": key,
        "definition_certificates": definitions,
        "child_certificates": [child_row],
        "server_parent_pending": True,
        "validated_node": False,
        "Lean_started": False,
        "submission_ready": False,
    })
    pins = {
        formal.rel(SELF): formal.sha(SELF),
        formal.rel(Path(base.__file__)): formal.sha(Path(base.__file__)),
        formal.rel(Path(plan.__file__)): formal.sha(Path(plan.__file__)),
        formal.rel(Path(childcheck.__file__)): formal.sha(Path(childcheck.__file__)),
        formal.rel(manifest_path): formal.sha(manifest_path),
        formal.rel(certified_inputs): formal.sha(certified_inputs),
        child_row["certificate"]: child_row["certificate_sha256"],
        child_row["output_olean"]: child_row["output_olean_sha256"],
    }
    for row in definitions:
        pins[row["certificate"]] = row["certificate_sha256"]
        pins[row["output_olean"]] = row["output_lean_sha256"]
    files = [next(stage.glob("Thm_*.lean")), next(stage.glob("Sol_*.lean")),
             stage / "SnapshotOriginal.lean", with_refs]
    compile_manifests = {}
    for index, source in enumerate(files, 1):
        imports = (["Lean", manifest["source_components"][0]["source_module"]]
                   if source.name == "SnapshotOriginal.lean" else manifest["imports"])
        path = stage / f"c{index}.json"
        base.write_exact(path, {
            "schema_version": 1,
            "artifact_kind": "formal-log-successor-node-file-import-certificate",
            "output": source.relative_to(ROOT).as_posix(),
            "output_sha256": formal.sha(source),
            "imports": imports,
            "input_hashes": pins,
            "runtime_sha256": manifest["runtime_sha256"],
            "node": key,
            "node_validated": False,
            "server_parent_pending": True,
            "timeout_seconds": 300,
            "Lean_started": False,
            "submission_ready": False,
        })
        compile_manifests[source.name] = {
            "manifest": formal.rel(path), "manifest_sha256": formal.sha(path)}
    preparation = {
        **generated,
        "attempt_root": formal.rel(DEST),
        "short_stage": formal.rel(stage),
        "base_snapshot": formal.rel(base_snapshot),
        "base_snapshot_sha256": formal.sha(base_snapshot),
        "generated_with_refs": formal.rel(with_refs),
        "generated_with_refs_sha256": formal.sha(with_refs),
        "generated_with_refs_prefix_bytes": base_snapshot.stat().st_size,
        "proof_reference_addon_sha256": base.sha_bytes(addon),
        "proof_reference_output": formal.rel(refs_output),
        "proof_reference_requests": ["solution", *[x["generated_name"] for x in manifest["public_inline_ci_requests"]]],
        "certified_definition_dependencies": len(definitions),
        "certified_child_dependencies": [child_row],
        "compile_manifests": compile_manifests,
        "exact_old_snapshot_prefix": True,
        "server_parent_pending": True,
        "pure_python_prepared": True,
        "Lean_started": False,
        "validated": False,
        "submission_ready": False,
    }
    base.write_exact(stage / "preparation.json", preparation)
    return preparation


def path_budget(stage, preparation):
    paths = []
    for filename in preparation["compile_manifests"]:
        source = (stage / filename).resolve()
        paths.extend([source, Path(str(source) + ".preflight.json")])
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
        paths.append((V / "staged-preflight-logs" / (source.stem + "_" + stamp + ".log")).resolve())
    manifest = formal.read(stage / "manifest.json")
    for mapping in (manifest["inline_type_json_outputs"], manifest["public_inline_type_json_outputs"]):
        paths.extend((ROOT / mapping[side]).resolve() for side in ("original", "generated"))
    paths.extend((stage / name).resolve() for name in
                 ("original-type.json", "generated-type.json", "proof-references.json"))
    report = {str(path): len(str(path)) for path in paths}
    if max(report.values()) >= 240:
        raise ValueError("Successor compiler artifact exceeds the conservative path budget")
    return report


def check(which):
    child_certificate()
    stage = DEST / which
    preparation = formal.read(stage / "preparation.json")
    if preparation["node"] != NODES[which] or preparation.get("server_parent_pending") is not True:
        raise ValueError("Wrong local successor preparation state")
    base_snapshot = TASK / preparation["base_snapshot"]
    with_refs = TASK / preparation["generated_with_refs"]
    if not with_refs.read_bytes().startswith(base_snapshot.read_bytes()):
        raise ValueError("Generated-with-refs lost the exact snapshot prefix")
    checked = {}
    for filename, row in preparation["compile_manifests"].items():
        source, mp = stage / filename, TASK / row["manifest"]
        if formal.sha(mp) != row["manifest_sha256"]:
            raise ValueError("Compilation manifest changed: " + filename)
        document = formal.read(mp)
        formal.runner.verify_manifest_inputs(document)
        formal.runner.verify_source_certificate(source, document)
        checked[filename] = len(formal.runner.certified_imports(source, document))
    budget = path_budget(stage, preparation)
    return {"node": NODES[which], "short_stage": formal.rel(stage),
            "exact_snapshot_prefix": True, "file_and_import_pins_checked": True,
            "path_count": len(budget), "maximum_absolute_artifact_path_length": max(budget.values()),
            "files_and_import_counts": checked, "server_parent_pending": True,
            "Lean_started": False, "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--node", required=True, choices=sorted(NODES))
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare(args.node) if args.prepare else check(args.node), indent=2))


if __name__ == "__main__":
    main()
