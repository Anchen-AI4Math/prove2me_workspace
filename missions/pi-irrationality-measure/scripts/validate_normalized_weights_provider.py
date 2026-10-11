#!/usr/bin/env python3
"""Bind and validate normalizedLogWeights source/generated kernel evidence.

This consumer is deliberately staged: check-only reconstructs inputs without
Lean; bind-source and bind-generated freeze ordered-first imported OLeans;
validate consumes only already produced bounded-preflight sidecars and kernel
snapshots. It never starts Lean or contacts the platform.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from pathlib import Path
from typing import Any

import generate_platform_bundles as base_generator
import generate_namespace_context_providers as readonly
import generate_platform_provider_bundles as producer
import generate_shared_source_snapshot as base
import structural_kernel_snapshot as kernel
import certify_structural_kernel_source_snapshot as source_certifier
import validate_provider_bundle as ordinary
import preflight_staged_module as preflight
import stage_normalized_weights_provider as stage

TASK, ROOT, V = stage.TASK, stage.ROOT, stage.TASK / "verification"
STAGE_ROOT = V / "ap3"
BATCH = STAGE_ROOT / "s"
PROBES = BATCH / "probes"
DEFINITIONS = BATCH / "Definitions"
DEF = DEFINITIONS / "Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations.lean"
DEF_MANIFEST = DEF.with_suffix(".manifest.json")
SOURCE = PROBES / "SourceStructural.lean"
GENERATED = PROBES / "GeneratedStructural.lean"
SOURCE_UNBOUND = PROBES / "SourceStructural.imports.json"
GENERATED_UNBOUND = PROBES / "GeneratedStructural.imports.json"
SOURCE_BOUND = PROBES / "SourceStructural.bound.imports.json"
GENERATED_BOUND = PROBES / "GeneratedStructural.bound.imports.json"
OWNER_PATH = PROBES / "source-owner.json"
SOURCE_REQUEST = PROBES / "source-request.json"
GENERATED_REQUEST = PROBES / "generated-request.json"
SOURCE_JSONL = PROBES / "source.jsonl"
GENERATED_JSONL = PROBES / "generated.jsonl"
RUNTIME = V / "lean-runtime.json"
PLATFORM = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations"
MAX_SECONDS = 300


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read(path: Path) -> Any:
    if not path.is_file():
        raise ValueError(f"Missing normalizedLogWeights artifact: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def write(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def task_rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def stage_preflight(source: Path, root: Path, manifest: Path, module: str,
                    imports: list[str], mode: str = "modecheck") -> dict[str, Any]:
    return {"source": source.relative_to(V).as_posix(), "root": root.relative_to(V).as_posix(),
            "manifest": manifest, "module": module, "imports": imports,
            "mode": mode, "role": module}


def check_path_budget() -> int:
    paths = [str(path.resolve()) for path in STAGE_ROOT.rglob("*") if path.is_file()]
    paths += [str((TASK / "scripts" / "validate_normalized_weights_provider.py").resolve())]
    longest = max(map(len, paths), default=0)
    require(longest < 240, f"Strict Windows path limit exceeded: {longest}")
    return longest


def reconstruct() -> dict[str, Any]:
    """Re-run the exact provider generator in isolated scratch and rebuild probes."""
    require(STAGE_ROOT.is_dir(), "The isolated ap3 stage root is absent")
    helper = Path(stage.__file__).resolve()
    original_output = producer.OUTPUT
    g = readonly.readonly_generator()
    g.input_hashes[stage.task_relative(helper)] = stage.sha(helper)
    bundle = g.artifact_plan["definition_bundles"].get(stage.MODULE)
    require(isinstance(bundle, dict) and bundle.get("units") == [stage.UNIT]
            and bundle.get("imports") == [], "Provider bundle no longer has the exact singleton plan")
    require(not g.module_name_risk(stage.MODULE), "Provider module has a generator boundary risk")
    owner, basis, excluded = stage.catalog_owner(g)
    require(owner == read(OWNER_PATH), "Sourceowner witness differs from authenticated AST/catalog owner")
    require(sha(DEF) == read(DEF_MANIFEST)["output_sha256"], "Definition provider source hash differs")
    provider_manifest = read(DEF_MANIFEST)
    require(provider_manifest["selected_units"] == [stage.UNIT]
            and provider_manifest["source_commit"] == "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
            and provider_manifest["platform_module"] == PLATFORM,
            "Definition manifest does not bind the expected unit/module/commit")
    require(provider_manifest["input_hashes"].get(stage.task_relative(helper)) == stage.sha(helper),
            "Definition manifest does not pin the generation helper")

    # Re-run the frozen Generator.generate path into an isolated fresh directory.
    scratch_parent = TASK / ".pe"
    scratch_parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="nw-check-", dir=scratch_parent) as scratch:
        producer.OUTPUT = Path(scratch)
        try:
            generated_doc = base_generator.Generator.generate(g, stage.MODULE)
            generated_path = ROOT / generated_doc["output"]
            require(generated_path.read_bytes() == DEF.read_bytes(),
                    "Definition source is not byte-identical to fresh original Generator output")
            for key in ("source_module", "platform_module", "source", "source_sha256", "source_commit",
                        "original_source", "original_source_sha256", "facts", "facts_sha256", "output_sha256",
                        "selected_units", "imports", "elaboration_only_helpers", "renames", "kept_local_instances",
                        "source_skeleton_preserved", "full_definition_proofs_preserved",
                        "independent_byte_reconstruction_equal", "source_unchanged", "edits"):
                require(generated_doc.get(key) == provider_manifest.get(key),
                        "Fresh Generator report differs from staged Definition: " + key)
        finally:
            producer.OUTPUT = original_output

    expected_source = stage.render_probe(read(SOURCE_REQUEST), "OAI.NumberTheory.PiExponent.Main",
                                         SOURCE_JSONL, "structuralSource")
    expected_generated = stage.render_probe(read(GENERATED_REQUEST), PLATFORM,
                                            GENERATED_JSONL, "structuralGenerated")
    require(SOURCE.read_bytes() == expected_source.replace("\n", "\r\n").encode("utf-8"),
            "Source probe differs from exact owner/request/core reconstruction")
    require(GENERATED.read_bytes() == expected_generated.replace("\n", "\r\n").encode("utf-8"),
            "Generated probe differs from exact owner/request/core reconstruction")
    for path, expected_module, expected_name in ((SOURCE_REQUEST, stage.MODULE, stage.NAME),
                                                  (GENERATED_REQUEST, PLATFORM, stage.NAME)):
        req = read(path)
        require(req["expected_module"] == expected_module and req["expected_public_name"] == expected_name,
                "Structural probe request Name/module differs")
        for key, value in (("graph_kind", owner["graph_kind"]), ("decl_graph_sha256", owner["decl_graph_sha256"]),
                           ("decl_graph_row_sha256", owner["decl_graph_row_sha256"]),
                           ("owner_kind", owner["owner_kind"]), ("owner_id", owner["owner_id"]),
                           ("command_unit", owner["command_unit"]), ("family_root", stage.NAME)):
            require(req[key] == value, "Structural request does not match authenticated owner: " + key)
    require(read(SOURCE_UNBOUND)["output_sha256"] == sha(SOURCE)
            and read(GENERATED_UNBOUND)["output_sha256"] == sha(GENERATED),
            "Unbound structural import manifest does not pin exporter bytes")
    return {"owner": owner, "basis": basis, "excluded_subset": excluded,
            "provider": provider_manifest, "input_hashes": g.input_hashes}


def ordered_first_olean(module: str, search_path: list[Path]) -> dict[str, str]:
    relative = Path(*module.split(".")).with_suffix(".olean")
    found = next(((root / relative, root) for root in search_path if (root / relative).is_file()), None)
    require(found is not None, "Cannot resolve actual ordered-first imported OLean: " + module)
    path, root = found
    path, root = path.resolve(), root.resolve()
    require(path.is_file(), "Resolved imported OLean is absent: " + module)
    return {"module": module, "path": str(path), "sha256": sha(path),
            "resolved_search_root": str(root)}


def frozen_manifest(source: Path, original: Path, probe_module: str,
                    imported: list[str], generated_provider_record: Path | None = None) -> dict[str, Any]:
    base_doc = read(original)
    require(base_doc["output_sha256"] == sha(source), "Unbound manifest source pin differs")
    runtime, runtime_sha, _, _, _ = preflight.validate_runtime()
    search_path = preflight.effective_search_path(runtime["environment"]["LEAN_PATH"])
    actual = [ordered_first_olean(module, search_path) for module in imported]
    inputs = dict(base_doc["input_hashes"])
    inputs[task_rel(original)] = sha(original)
    inputs[task_rel(stage_path())] = sha(stage_path())
    inputs[task_rel(Path(__file__).resolve())] = sha(Path(__file__).resolve())
    kernel_path = Path(kernel.__file__).resolve()
    inputs[task_rel(kernel_path)] = sha(kernel_path)
    certifier_path = Path(source_certifier.__file__).resolve()
    inputs[task_rel(certifier_path)] = sha(certifier_path)
    for dep in actual:
        path = Path(dep["path"])
        if path.is_relative_to(TASK.resolve()):
            inputs[task_rel(path)] = dep["sha256"]
    doc = {"schema_version": 2, "artifact_kind": base_doc["artifact_kind"] + "-bound",
           "source_version": 875, "source_commit": base_doc["source_commit"],
           "source_only": base_doc["source_only"], "partial": True, "platform_ready": False,
           "output": base_doc["output"], "output_sha256": base_doc["output_sha256"],
           "imports": base_doc["imports"], "runtime_sha256": runtime_sha,
           "input_hashes": dict(sorted(inputs.items())),
           "snapshot_jsonl": base_doc["snapshot_jsonl"], "request_manifest": base_doc["request_manifest"],
           "owner_witness": base_doc["owner_witness"], "owner_witness_sha256": base_doc["owner_witness_sha256"],
           "full_owner_catalog": base_doc["full_owner_catalog"],
           "full_owner_catalog_sha256": base_doc["full_owner_catalog_sha256"],
           "full_owner_count": 6148, "decl_graph_sha256": base_doc["decl_graph_sha256"],
           "decl_graph_row_sha256": base_doc["decl_graph_row_sha256"],
           "source_module": base_doc["source_module"], "source_name": base_doc["source_name"],
           "command_unit": base_doc["command_unit"], "actual_import_oleans": actual,
           "source174_noncoverage_audit": base_doc["source174_noncoverage_audit"],
           "uses_source174_certificate": False, "validated": False, "lean_started": False, "api_used": False}
    if probe_module == PLATFORM:
        require(generated_provider_record is not None, "Generated probe binding requires provider preflight sidecar")
        provider_stage = {"source": DEF.relative_to(V).as_posix(), "root": BATCH.relative_to(V).as_posix(),
                          "manifest": DEF_MANIFEST, "module": PLATFORM,
                          "imports": read(DEF_MANIFEST)["imports"], "mode": "emit-olean", "role": "provider"}
        evidence = ordinary.verify_preflight_record(provider_stage)
        record = TASK / evidence["record"]
        log = TASK / evidence["log"]
        olean = TASK / evidence["output_olean"]
        require(record.resolve() == generated_provider_record.resolve(),
                "Provider sidecar path is not the exact module preflight record")
        require(evidence["actual_module_identity"] == PLATFORM and olean.is_file(),
                "Provider sidecar does not attest the generated Definition module/OLean")
        provider_dep = next((item for item in actual if item["module"] == PLATFORM), None)
        require(provider_dep is not None and Path(provider_dep["path"]).resolve() == olean.resolve()
                and provider_dep["sha256"] == evidence["output_olean_sha256"],
                "Generated probe import is not the ordered-first actual provider OLean")
        for path in (record, log, olean):
            inputs[task_rel(path)] = sha(path)
        doc["input_hashes"] = dict(sorted(inputs.items()))
        doc["provider_preflight"] = {"record": task_rel(record), "record_sha256": sha(record),
                                     "log": task_rel(log), "log_sha256": sha(log),
                                     "output_olean": task_rel(olean), "output_olean_sha256": sha(olean),
                                     "actual_module_identity": evidence["actual_module_identity"],
                                     "ordered_first_import_matches": True}
    return doc


def archive_unbound(original: Path, history_name: str) -> None:
    history = PROBES / "history" / history_name
    raw = original.read_bytes()
    if history.exists():
        require(history.read_bytes() == raw, "Existing unbound manifest history differs; refusing overwrite")
    else:
        history.parent.mkdir(parents=True, exist_ok=True)
        history.write_bytes(raw)


def archive_bound_before_rewrite(bound: Path, stem: str) -> None:
    if not bound.exists():
        return
    history = PROBES / "history" / f"{stem}-{sha(bound)[:12]}.json"
    require(not history.exists(), "Refusing to overwrite previously archived bound manifest")
    history.parent.mkdir(parents=True, exist_ok=True)
    history.write_bytes(bound.read_bytes())


def bind_source() -> dict[str, Any]:
    reconstruct()
    archive_unbound(SOURCE_UNBOUND, "SourceStructural.imports-unbound.json")
    archive_bound_before_rewrite(SOURCE_BOUND, "SourceStructural.bound-before-rewrite")
    doc = frozen_manifest(SOURCE, SOURCE_UNBOUND, stage.MODULE,
                          read(SOURCE_UNBOUND)["imports"])
    write(SOURCE_BOUND, doc)
    return {"manifest": task_rel(SOURCE_BOUND), "sha256": sha(SOURCE_BOUND),
            "imports": doc["imports"], "actual_import_oleans": doc["actual_import_oleans"],
            "preflight_command": "python scripts/preflight_staged_module.py ap3/s/probes/SourceStructural.lean --root ap3/s/probes --imports-manifest ap3/s/probes/SourceStructural.bound.imports.json --timeout-seconds 300"}


def bind_generated() -> dict[str, Any]:
    reconstruct()
    provider_record = (DEF.with_suffix(DEF.suffix + ".preflight.json")).resolve()
    require(provider_record.is_file(), "Run the Definition emit-olean preflight before binding generated probe")
    archive_unbound(GENERATED_UNBOUND, "GeneratedStructural.imports-unbound.json")
    archive_bound_before_rewrite(GENERATED_BOUND, "GeneratedStructural.bound-before-rewrite")
    doc = frozen_manifest(GENERATED, GENERATED_UNBOUND, PLATFORM,
                          ["Lean", PLATFORM], generated_provider_record=provider_record)
    write(GENERATED_BOUND, doc)
    return {"manifest": task_rel(GENERATED_BOUND), "sha256": sha(GENERATED_BOUND),
            "imports": doc["imports"], "actual_import_oleans": doc["actual_import_oleans"],
            "provider_preflight": doc["provider_preflight"],
            "preflight_command": "python scripts/preflight_staged_module.py ap3/s/probes/GeneratedStructural.lean --root ap3/s/probes --imports-manifest ap3/s/probes/GeneratedStructural.bound.imports.json --timeout-seconds 300"}


def verify_sidecar(source: Path, root: Path, manifest: Path, module: str,
                   imports: list[str], role: str, emit_olean: bool = False) -> dict[str, Any]:
    stage_info = stage_preflight(source, root, manifest, module, imports,
                                 "emit-olean" if emit_olean else "modecheck")
    stage_info["role"] = role
    return ordinary.verify_preflight_record(stage_info)


def check_bound_dependencies(record: dict[str, Any], manifest_path: Path, doc: dict[str, Any]) -> None:
    require(sha(manifest_path) == sha_bytes(manifest_path.read_bytes()), "Manifest read instability")
    actual = doc.get("actual_import_oleans")
    deps = record.get("dependency_oleans")
    require(isinstance(actual, list) and isinstance(deps, list), "Bound OLean evidence is absent")
    by_module = {item["module"]: item for item in actual}
    for dep in deps:
        required = by_module.get(dep["module"])
        require(required is not None and Path(required["path"]).resolve() == Path(dep["path"]).resolve()
                and required["sha256"] == dep["sha256_after"]
                and Path(required["resolved_search_root"]).resolve() == Path(dep["resolved_search_root"]).resolve(),
                "Preflight imported OLean differs from frozen ordered-first binding: " + dep["module"])


def validate() -> dict[str, Any]:
    reconstruction = reconstruct()
    require(SOURCE_BOUND.is_file() and GENERATED_BOUND.is_file(),
            "Both source and generated import manifests must be bound before validation")
    source_doc, generated_doc = read(SOURCE_BOUND), read(GENERATED_BOUND)
    for manifest, source in ((SOURCE_BOUND, SOURCE), (GENERATED_BOUND, GENERATED)):
        require(read(manifest)["output_sha256"] == sha(source), "Bound import manifest output pin changed")
        for rel, expected in read(manifest)["input_hashes"].items():
            p = (TASK / rel).resolve()
            if p.is_relative_to(TASK.resolve()):
                require(p.is_file() and sha(p) == expected, "Bound import input changed: " + rel)
    provider_evidence = verify_sidecar(DEF, BATCH, DEF_MANIFEST, PLATFORM,
                                       read(DEF_MANIFEST)["imports"], "provider", True)
    source_evidence = verify_sidecar(SOURCE, PROBES, SOURCE_BOUND,
                                     "SourceStructural", source_doc["imports"], "source-probe")
    generated_evidence = verify_sidecar(GENERATED, PROBES, GENERATED_BOUND,
                                        "GeneratedStructural", generated_doc["imports"], "generated-probe")
    for evidence, manifest, doc in ((source_evidence, SOURCE_BOUND, source_doc),
                                    (generated_evidence, GENERATED_BOUND, generated_doc)):
        record_path = TASK / evidence["record"]
        raw = read(record_path)
        check_bound_dependencies(raw, manifest, doc)
    rows = []
    owner = read(OWNER_PATH)
    graph, graph_sha = base.load_decl_graph()
    kernel.expression_names = source_certifier.expression_names_safe
    for jsonl, req_path, module in ((SOURCE_JSONL, SOURCE_REQUEST, stage.MODULE),
                                     (GENERATED_JSONL, GENERATED_REQUEST, PLATFORM)):
        raw_rows = [json.loads(line) for line in jsonl.read_text(encoding="utf-8").splitlines() if line.strip()]
        require(len(raw_rows) == 1, "Expected exactly one exported normalizedLogWeights ConstantInfo row")
        row, req = raw_rows[0], read(req_path)
        valid = kernel.validate_row_basic(row, req, owner, graph, graph_sha, expected_module=module)
        require(row["sourceName"] == stage.NAME and row["resolvedName"] == stage.NAME
                and row["graphKind"] == "def" and row["closedValue"] is True
                and row["value"] is not None and set(row["axioms"]) <= kernel.STD3,
                "Kernel row lacks exact public Definition identity, complete value, or Std3")
        rows.append(row)
    kernel.compare_rows(rows[0], rows[1], stage.MODULE, PLATFORM)
    report = {"schema_version": 1, "artifact_kind": "normalizedLogWeights-source-generated-kernel-validation",
              "validated": True, "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
              "proposal_status": "Draft", "source_name": stage.NAME,
              "source_module": stage.MODULE, "generated_module": PLATFORM,
              "provider_preflight": provider_evidence, "source_probe_preflight": source_evidence,
              "generated_probe_preflight": generated_evidence,
              "source_import_manifest": {"path": task_rel(SOURCE_BOUND), "sha256": sha(SOURCE_BOUND)},
              "generated_import_manifest": {"path": task_rel(GENERATED_BOUND), "sha256": sha(GENERATED_BOUND)},
              "source_row_sha256": kernel.canonical_row_sha256(rows[0]),
              "generated_row_sha256": kernel.canonical_row_sha256(rows[1]),
              "exact_public_name": True, "kernel_type_equal": True, "complete_definition_value_equal": True,
              "axioms_equal_and_std3": True, "actual_module_owners_checked": True,
              "owner_mapping": {"source": stage.MODULE, "generated": PLATFORM},
              "only_universe_parameter_display_names_normalized": True,
              "source174_certificate_used": False, "full_owner_catalog_sha256": sha(stage.FULL_CATALOG),
              "lean_started_by_validator": False, "api_used": False}
    out = PROBES / "provider-validation.json"
    write(out, report)
    return {**report, "report": task_rel(out), "report_sha256": sha(out)}


def stage_path() -> Path:
    return Path(stage.__file__).resolve()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--check-only", action="store_true")
    modes.add_argument("--bind-source", action="store_true")
    modes.add_argument("--bind-generated", action="store_true")
    modes.add_argument("--validate-existing", action="store_true")
    args = parser.parse_args()
    if args.check_only:
        result = reconstruct()
        source_command = "python scripts/preflight_staged_module.py ap3/s/probes/SourceStructural.lean --root ap3/s/probes --imports-manifest ap3/s/probes/SourceStructural.bound.imports.json --timeout-seconds 300"
        def_command = "python scripts/preflight_staged_module.py ap3/s/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations.lean --root ap3/s --imports-manifest ap3/s/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations.manifest.json --emit-olean --timeout-seconds 300"
        gen_command = "python scripts/preflight_staged_module.py ap3/s/probes/GeneratedStructural.lean --root ap3/s/probes --imports-manifest ap3/s/probes/GeneratedStructural.bound.imports.json --timeout-seconds 300"
        output = {"checked": True, "lean_started": False, "api_used": False,
                  "definition_actual_module_if_root_ap3_s": DEF.relative_to(BATCH).with_suffix("").as_posix().replace("/", "."),
                  "max_path_length": check_path_budget(), "definition_preflight_command": def_command,
                  "bind_source_command": "python scripts/validate_normalized_weights_provider.py --bind-source",
                  "source_preflight_command": source_command,
                  "bind_generated_command": "python scripts/validate_normalized_weights_provider.py --bind-generated",
                  "generated_preflight_command": gen_command,
                  "consumer_command": "python scripts/validate_normalized_weights_provider.py --validate-existing"}
    elif args.bind_source:
        output = bind_source()
    elif args.bind_generated:
        output = bind_generated()
    else:
        output = validate()
    print(json.dumps(output, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"normalizedLogWeights consumer refused: {exc}", file=os.sys.stderr)
        raise SystemExit(2)
