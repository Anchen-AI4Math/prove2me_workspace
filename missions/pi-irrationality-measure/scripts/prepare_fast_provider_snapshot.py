#!/usr/bin/env python3
"""Stage an exact public-only resolver optimization for NEW provider snapshots.

No Lean or HTTP request is started. Frozen provider generation and existing
snapshot/certificate evidence are never modified. A pending prepare-only stage
has no runnable imports manifest until the actual provider OLean is certified.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
from typing import Any

import generate_platform_provider_bundles as generator

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
VERIFICATION = TASK / "verification"
SELF = Path(__file__).resolve()
COMPONENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z", re.ASCII)

# This is the complete frozen resolver command, not a substring selected by
# inferred line numbers. Changes in the producer require a new explicit review.
OLD_RESOLVER = '''def resolveRequest (env : Environment) (request : ProviderRequest) : MetaM Name := do
  let mut candidates : Array Name := #[]
  for (actualName, _) in env.constants.toList do
    if ownedBy env actualName request.expectedModule then
      if request.sourceWasPrivate then
        if (Lean.privateToUserName? actualName).map Name.toString == some request.expectedUserName then
          candidates := candidates.push actualName
      else if actualName.toString == request.expectedPublicName then
        candidates := candidates.push actualName
  unless candidates.size == 1 do
    throwError "Expected one declaration for source={request.sourceGraphName}, user={request.expectedUserName}, module={request.expectedModule}; found {candidates.size}"
  return candidates[0]!
'''

# The private branch is deliberately the exact old resolver indented once.
# It is not eligible for this helper's authenticated public-only requests.
FAST_RESOLVER = '''def resolveRequest (env : Environment) (request : ProviderRequest) : MetaM Name := do
  if request.sourceWasPrivate then
''' + "".join("  " + line + "\n" for line in OLD_RESOLVER.splitlines()[1:]) + r'''  else
    unless request.expectedKind == "def" || request.expectedKind == "theorem" do
      throwError "Fast public resolver requires an ordinary theorem or definition"
    let parts := request.expectedPublicName.splitOn "."
    unless parts.all (fun part => !part.isEmpty && part.toList.all (fun c =>
        (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
        (c >= '0' && c <= '9') || c == '_' || c == '\'')) do
      throwError "Fast public resolver rejects quoted or ambiguous names"
    let name := parts.foldl Name.str Name.anonymous
    unless name.toString == request.expectedPublicName do
      throwError "Fast public Name construction does not round-trip"
    unless (Lean.privateToUserName? name).isNone do
      throwError "Fast public resolver found a private kernel name"
    let some _ := env.find? name | throwError "Fast public declaration is absent: {name}"
    unless ownedBy env name request.expectedModule do
      throwError "Fast public declaration has a different actual module owner: {name}"
    return name
'''


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def mission_file(value: str) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = TASK / path
    path = path.resolve()
    if not path.is_relative_to(TASK.resolve()) or not path.is_file():
        raise ValueError("Missing/outside mission input: " + str(value))
    return path


def ordinary_public_name(name: Any) -> bool:
    return isinstance(name, str) and bool(name) and all(COMPONENT.fullmatch(p) for p in name.split("."))


def validate_requests(requests, module: str):
    if not isinstance(requests, list) or not requests:
        raise ValueError("Fast snapshot requires a nonempty exact request list")
    names = []
    for row in requests:
        name = row["expected_public_name"]
        if (row["source_was_private"] is not False or row["expected_kind"] not in {"theorem", "def"}
                or not ordinary_public_name(name) or name.startswith("_private.")
                or row["expected_user_name"] != name or row["source_graph_name"] != name
                or row["expected_module"] != module):
            raise ValueError("Fast snapshot only supports exact ordinary ASCII public names: " + str(name))
        names.append(name)
    if len(set(names)) != len(names):
        raise ValueError("Fast snapshot request names are duplicated")


def reconstruct(old_bytes: bytes, old_output: Path, new_output: Path) -> tuple[bytes, dict[str, Any]]:
    """Replace precisely two byte anchors: resolver command and output literal."""
    if b"\r" in old_bytes.replace(b"\r\n", b""):
        raise ValueError("Snapshot contains unsupported bare CR")
    crlf = b"\r\n" in old_bytes
    if crlf and b"\n" in old_bytes.replace(b"\r\n", b""):
        raise ValueError("Snapshot has mixed LF/CRLF line endings")
    newline = "\r\n" if crlf else "\n"
    encode = lambda text: text.replace("\n", newline).encode("utf-8")
    old_anchor = encode(OLD_RESOLVER)
    new_anchor = encode(FAST_RESOLVER)
    if generator.PROVIDER_EXPORTER.count(OLD_RESOLVER) != 1 or old_bytes.count(old_anchor) != 1:
        raise ValueError("Frozen public resolver byte anchor is absent or ambiguous")
    old_call = encode("  exportProviderSnapshotJsonl providerRequests " + generator.lean_string(generator.workspace_relative(old_output)) + "\n")
    new_call = encode("  exportProviderSnapshotJsonl providerRequests " + generator.lean_string(generator.workspace_relative(new_output)) + "\n")
    if old_bytes.count(old_call) != 1:
        raise ValueError("Frozen generated JSONL output anchor is absent or ambiguous")
    changed = old_bytes.replace(old_anchor, new_anchor, 1).replace(old_call, new_call, 1)
    if changed.replace(new_anchor, old_anchor, 1).replace(new_call, old_call, 1) != old_bytes:
        raise ValueError("Optimization changed bytes outside the exact two anchors")
    return changed, {"resolver_old_sha256": digest(old_anchor), "resolver_fast_sha256": digest(new_anchor),
                     "output_call_old_sha256": digest(old_call), "output_call_fast_sha256": digest(new_call),
                     "line_endings": "CRLF" if crlf else "LF", "all_other_bytes_equal": True}


def layout(result):
    stage = mission_file(result["snapshot_dir"] + "/SnapshotGenerated.lean").parent
    return stage, stage/"SnapshotGeneratedFast.lean", stage/"fast-generated.jsonl", stage/"fast-generated-provenance.json", stage/"fast-imports.json"


def reject_existing_ordinary_evidence(result):
    stage, *_ = layout(result)
    provider_root = TASK/result["provider_root"]
    stem = Path(result["manifest"]).name.removesuffix(".manifest.json")
    if ((stage/"SnapshotGenerated.lean.preflight.json").exists() or (stage/"generated.jsonl").exists()
            or (provider_root/result["batch"]/"validation"/stem/"provider-validation.json").exists()):
        raise ValueError("Existing ordinary generated snapshot/certificate is frozen; fast mode is for new candidates only")


def check_base(result):
    reject_existing_ordinary_evidence(result)
    stage, fast, jsonl, provenance, imports_manifest = layout(result)
    bundle = read(mission_file(result["manifest"]))
    plan_path, requests_path = stage/"snapshot-comparison-plan.json", stage/"snapshot-requests.json"
    plan, requests = read(plan_path), read(requests_path)
    validate_requests(requests["generated"], result["platform_module"])
    old = stage/"SnapshotGenerated.lean"
    if sha(old) != plan["generated_exporter_sha256"] or sha(mission_file(result["provider_source"])) != plan["generated_bundle_sha256"]:
        raise ValueError("Base generated snapshot/bundle hash differs")
    core = mission_file(plan["snapshot_core"])
    if sha(core) != plan["snapshot_core_sha256"]:
        raise ValueError("Type-only snapshot core changed")
    expected = generator.render_snapshot(core.read_text(encoding="utf-8"), result["platform_module"], requests["generated"], stage/"generated.jsonl")
    raw = old.read_bytes()
    expected_bytes = expected.replace("\n", "\r\n").encode() if b"\r\n" in raw else expected.encode()
    if raw != expected_bytes:
        raise ValueError("Base generated snapshot cannot be reconstructed exactly from frozen producer")
    generated, edits = reconstruct(raw, stage/"generated.jsonl", jsonl)
    pins = {}
    for relative, expected_sha in bundle["input_hashes"].items():
        path = generator.resolve_recorded_input(relative)
        if not path.resolve().is_relative_to(TASK.resolve()) or sha(path) != expected_sha:
            raise ValueError("Provider selected input pin changed/outside mission: " + relative)
        pins[rel(path)] = expected_sha
    for path in [SELF, Path(generator.__file__), old, plan_path, requests_path, core,
                 mission_file(plan["snapshot_core_lineage"]), mission_file(result["manifest"]),
                 mission_file(result["provider_source"]), VERIFICATION/"lean-runtime.json"]:
        pins[rel(path)] = sha(path)
    return bundle, generated, edits, pins


def provider_evidence(result):
    """Actual bundle compile and first ordered import resolution, never planned availability."""
    import preflight_staged_module as runner
    import validate_provider_bundle as validator
    source = mission_file(result["provider_source"])
    record_path = source.with_suffix(".lean.preflight.json")
    if not record_path.is_file():
        return None
    record = read(record_path)
    stage = {"source":source.relative_to(VERIFICATION).as_posix(), "manifest":mission_file(record["manifest"]),
             "mode":"emit-olean", "module":result["platform_module"], "imports":result["imports"], "role":"provider-bundle"}
    evidence = validator.verify_preflight_record(stage)
    runtime, runtime_sha, *_ = runner.validate_runtime()
    search = runner.effective_search_path(runtime["environment"]["LEAN_PATH"])
    deps = runner.dependency_certificates(["Lean", result["platform_module"]], search, {"SnapshotGeneratedFast"})
    own = deps[1]
    actual = mission_file(evidence["output_olean"])
    if Path(own["path"]).resolve() != actual or own["sha256_before"] != evidence["output_olean_sha256"]:
        raise ValueError("Fast snapshot provider import is not the exact certified provider OLean")
    return {"bundle_preflight":evidence, "runtime_sha256":runtime_sha,
            "actual_import_oleans":[{"module":d["module"], "path":d["path"], "sha256":d["sha256_before"],
                                    "resolved_search_root":d["resolved_search_root"]} for d in deps]}


def expected_provenance(result, generated, edits, pins, evidence):
    stage, fast, jsonl, *_ = layout(result)
    return {"schema_version":1, "strategy":"exact-public-Name-direct-env-lookup", "provider_root":result["provider_root"],
                "batch":result["batch"], "source_module":result["source_module"], "platform_module":result["platform_module"],
                "base_snapshot":rel(stage/"SnapshotGenerated.lean"), "fast_snapshot":rel(fast), "fast_snapshot_sha256":digest(generated),
                "expected_generated_jsonl":rel(jsonl), "input_hashes":pins, "byte_edits":edits,
                "helper":rel(SELF), "helper_sha256":sha(SELF), "actual_provider_evidence":evidence,
                "runnable":evidence is not None, "ordinary_public_requests_only":True, "private_branch_eligible":False,
                "CI_export_unchanged":True, "types_values_axioms_comparison_required":True,
                "validated":False, "submission_ready":False, "lean_started":False}


def expected_imports_manifest(result, bundle, pins, evidence):
    _, fast, _, provenance, _ = layout(result)
    runnable_pins = dict(pins)
    runnable_pins[rel(provenance)] = sha(provenance)
    compiled = evidence["bundle_preflight"]
    for p in [mission_file(compiled["record"]), mission_file(compiled["log"]), mission_file(compiled["output_olean"])]:
        runnable_pins[rel(p)] = sha(p)
    return {"runtime_sha256":evidence["runtime_sha256"], "input_hashes":runnable_pins,
                    "output":generator.workspace_relative(fast), "output_sha256":sha(fast),
                    "source":bundle["source"], "source_sha256":bundle["source_sha256"],
                    "original_source":bundle["original_source"], "original_source_sha256":bundle["original_source_sha256"],
                    "imports":["Lean",result["platform_module"]], "fast_generated_provenance":rel(provenance),
                    "fast_generated_provenance_sha256":sha(provenance), "actual_import_oleans":evidence["actual_import_oleans"]}


def stage_fast_generated_snapshot(result, require_provider_evidence: bool = True):
    stage, fast, jsonl, provenance, imports_manifest = layout(result)
    if fast.with_suffix(".lean.preflight.json").exists() or jsonl.exists():
        return checked_fast_generated_snapshot(result)
    bundle, generated, edits, pins = check_base(result)
    evidence = provider_evidence(result)
    if require_provider_evidence and evidence is None:
        raise ValueError("Actual provider bundle preflight/OLean required before runnable fast snapshot")
    if fast.exists() and fast.read_bytes() != generated:
        raise ValueError("Existing isolated fast snapshot differs; preserve it before restaging")
    fast.write_bytes(generated)
    document = expected_provenance(result, generated, edits, pins, evidence)
    provenance.write_text(json.dumps(document, indent=2)+"\n", encoding="utf-8")
    if evidence is not None:
        manifest = expected_imports_manifest(result, bundle, pins, evidence)
        imports_manifest.write_text(json.dumps(manifest, indent=2)+"\n", encoding="utf-8")
    elif imports_manifest.exists():
        raise ValueError("Pending provider stage unexpectedly has a runnable manifest")
    return checked_fast_generated_snapshot(result, require_provider_evidence=require_provider_evidence)


def checked_fast_generated_snapshot(result, require_provider_evidence: bool = True):
    stage, fast, jsonl, provenance, imports_manifest = layout(result)
    bundle, generated, edits, pins = check_base(result)
    document = read(provenance)
    evidence = provider_evidence(result)
    if document != expected_provenance(result, generated, edits, pins, evidence) or fast.read_bytes() != generated:
        raise ValueError("Fast snapshot exact provenance/source/provider reconstruction mismatch")
    if require_provider_evidence and evidence is None:
        raise ValueError("Fast snapshot actual provider OLean is pending")
    if evidence is not None:
        manifest = read(imports_manifest)
        if manifest != expected_imports_manifest(result, bundle, pins, evidence):
            raise ValueError("Fast snapshot import/source certificate mismatch")
    return {"source":fast.relative_to(VERIFICATION).as_posix(), "root":stage.relative_to(VERIFICATION).as_posix(),
            "manifest":imports_manifest if evidence is not None else None, "module":"SnapshotGeneratedFast",
            "imports":["Lean",result["platform_module"]], "mode":"modecheck", "role":"generated-snapshot",
            "generated_jsonl":jsonl, "fast_generated_provenance":rel(provenance),
            "fast_generated_provenance_sha256":sha(provenance), "runnable":evidence is not None}


def main():
    import validate_provider_bundle as validator
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch", required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--provider-root", default="verification/providers-complete-preview")
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true", help="Stage bytes; missing actual provider OLean remains pending")
    modes.add_argument("--bind-provider", action="store_true", help="Require actual provider compile and write runnable imports manifest")
    modes.add_argument("--check-only", action="store_true", help="Check existing fast stage and actual provider evidence without writing")
    args = parser.parse_args()
    try:
        result = validator.structural_check(args.batch, args.module, args.provider_root)
        outcome = (checked_fast_generated_snapshot(result) if args.check_only else
                   stage_fast_generated_snapshot(result, require_provider_evidence=not args.prepare_only))
        print(json.dumps({k:str(v) if isinstance(v,Path) else v for k,v in outcome.items()}, indent=2))
    except (ValueError, KeyError, FileNotFoundError, TypeError) as error:
        print(json.dumps({"validated":False,"status":"rejected","error":str(error)}))
        raise SystemExit(2)


if __name__ == "__main__":
    main()
