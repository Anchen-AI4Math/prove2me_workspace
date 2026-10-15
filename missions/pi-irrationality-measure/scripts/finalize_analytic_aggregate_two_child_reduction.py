"""Finalize AP19's two-child Open sketch only after genuine data publication.

This is pure filesystem preparation. The five bounded Lean commands are for
the root agent to run; this module never runs Lean or calls the platform API.
"""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path

import stage_analytic_aggregate_two_child_reduction as candidate
import stage_analytic_remainder_data_provider as data
import certify_analytic_remainder_data_auto_ci_v5 as data_certifier


TASK, ROOT, V = candidate.TASK, candidate.ROOT, candidate.V
SELF = Path(__file__).resolve()
STAGE = V / "ap19/analytic-aggregate-two-child-reduction-final"
CANDIDATE = candidate.STAGE
CERTIFICATE = "open-sketch-interface-validation.json"
CONSUMER = TASK / "scripts/certify_analytic_aggregate_two_child_reduction.py"
RUNNER = TASK / "scripts/preflight_staged_module_windows_bounded.py"
RUNTIME = V / "lean-runtime.json"
LOOKUP = CANDIDATE / "exact-name-lookup.json"
LOOKUP_SHA = "11e3f3a8989a7072c2cf6345aaaa123312e73a37b6ec43de387a8cc9ab9d181f"
PUBLICATION = data.STAGE / "publication-v4/publication.json"
PUB_NAME = data.PLATFORM_MODULE.removeprefix("Definitions.Def_")
SOURCE_JSON = "source-types-and-refs.json"
GENERATED_JSON = "generated-types-and-refs.json"
OWNED_JSON = "generated-owned-ci-inventory.json"
PYTHON = "C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe"
_BOUNDARY_CACHE = None

need, read, sha, digest, encode, rel, workspace_rel = (
    candidate.need, candidate.read, candidate.sha, candidate.digest,
    candidate.encode, candidate.rel, candidate.workspace_rel)


def fixed_path(path):
    p = Path(path)
    return p if p.is_absolute() else TASK / p


def pin(pins, path):
    p = Path(path)
    key = str(p.resolve()) if p.is_absolute() and not p.resolve().is_relative_to(TASK.resolve()) else rel(p)
    pins[key] = sha(p)


def gate(pins):
    for name, expected in pins.items():
        need(sha(fixed_path(name)) == expected, "Frozen AP19 boundary changed: " + name)


def boundary():
    global _BOUNDARY_CACHE
    if _BOUNDARY_CACHE is not None:
        pins, report = _BOUNDARY_CACHE
        gate(pins)
        return dict(pins), copy.deepcopy(report)
    candidate.check_only()
    need(LOOKUP.is_file() and sha(LOOKUP) == LOOKUP_SHA,
         "Root's actual fixed-environment child exact-name lookup is missing/different")
    lookup = read(LOOKUP)
    need(lookup["read_only"] is True and lookup["request_methods"] == ["GET"]
         and lookup["environment"] == "0df444a360eaa60ab8c11dca51a86af692955474"
         and [r["theorem_name"] for r in lookup["records"]] == [n for n, *_ in candidate.CHILDREN],
         "Official child lookup names/environment/method differ")
    for row in lookup["records"]:
        need(row["lookup_total"] == 0 and len(row["pages"]) == 1
             and row["matches"] == [] and row["readbacks"] == [],
             "A child exact name exists already or its pagination differs")
        page = row["pages"][0]
        need(page["http_status"] == 200 and page["parsed_body"]["total"] == 0
             and page["parsed_body"]["theorems"] == []
             and digest(page["raw_body_utf8"].encode("utf-8")) == page["raw_body_sha256"],
             "Official raw-byte exact-name result differs")
    need(data.CORE_CERT.is_file() and data_certifier.CERT.is_file()
         and PUBLICATION.is_file(), "Genuine four-Def cert and Published record are pending")
    cert_path = data_certifier.CERT
    cert = read(cert_path)
    pins = {}
    for path in [SELF, CONSUMER, Path(candidate.__file__), Path(data.__file__),
                 Path(data_certifier.__file__), LOOKUP, PUBLICATION, cert_path,
                 data.STAGE / "preparation.json", RUNNER, RUNTIME]:
        pin(pins, path)
    data_prep = read(data.STAGE / "preparation.json")
    pins.update(data_prep["input_hashes"])
    pins.update(cert["implementation_hashes"])
    for name in [data.SOURCE_JSON, data.GENERATED_JSON, data.INVENTORY_JSON]:
        pin(pins, data.STAGE / name)
    pin(pins, data_certifier.probe.STAGE / data_certifier.probe.SOURCE_JSON)
    pin(pins, data_certifier.probe.STAGE / "preparation.json")
    for witness in [*cert["original_preflights"].values(), cert["source_automatic_preflight"]]:
        pins[witness["record"]] = witness["record_sha256"]
        for key in ["source", "manifest", "log"]:
            path = data_certifier.context.file(witness["data"][key])
            pin(pins, path)
        for dep in witness["data"]["dependency_oleans"]:
            need(dep["stable_during_compile"] and dep["sha256_before"] == dep["sha256_after"],
                 "Historical four-Def dependency OLean was unstable")
            pins[str(Path(dep["path"]).resolve())] = dep["sha256_before"]
    pins[cert["original_emitted_provider_olean"]] = cert["original_emitted_provider_olean_sha256"]
    gate(pins)
    actual = data_certifier.validate()
    need(encode(actual) == cert_path.read_bytes() and actual["validated"] is True
         and actual["Std3_only"] is True and actual["provided_names"] == data.NAMES
         and actual["primary_Def_full_types_values_equal"] is True
         and len(actual["actual_source_generated_closed_Prop_autoCI_pairs"]) == 2,
         "First full four-Def mathematical replay differs from genuine certificate")
    publication = read(PUBLICATION)
    body = publication["target_readback"]["body"]
    verdict = publication["last_publish_verdict"]["body"]
    wire = (data.STAGE / data.PROVIDER_FILE).read_bytes().decode("utf-8")
    need(publication["definition_name"] == PUB_NAME
         and publication["definition_id"] == body["theorem_id"] == verdict["theorem_id"]
         and publication["environment"] == body["mathlib_rev"] == "0df444a360eaa60ab8c11dca51a86af692955474"
         and body["status"] == "Definition" and body["visibility"] == "public"
         and body["deprecated_at"] is None and body["theorem_name"] == PUB_NAME
         and body["definition"] == publication["publish_intent"]["payload"]["definition"] == wire
         and verdict["status"] == "PUBLISHED" and verdict["theorem_name"] == PUB_NAME
         and publication["target_readback"]["http_status"] == 200,
         "Actual four-Def Published wire/ID/visibility/environment differs")
    gate(pins)
    report = {"provider_certificate": rel(cert_path), "provider_certificate_sha256": sha(cert_path),
              "provider_olean": cert["original_emitted_provider_olean"],
              "provider_olean_sha256": cert["original_emitted_provider_olean_sha256"],
              "published_definition_id": publication["definition_id"],
              "published_record": rel(PUBLICATION), "published_record_sha256": sha(PUBLICATION),
              "child_exact_name_lookup": rel(LOOKUP), "child_exact_name_lookup_sha256": LOOKUP_SHA}
    _BOUNDARY_CACHE = (dict(pins), copy.deepcopy(report))
    return pins, report


INVENTORY = r'''
namespace AnalyticAggregateOwnedInventory
open Lean Meta
def exportOwnedInventory (owners : Array String) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut found : Array (Name × ConstantInfo) := #[]
  for (name, ci) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | none => env.mainModule.toString
      | some idx => (env.header.moduleNames[idx.toNat]!).toString
    if owners.contains owner then found := found.push (name, ci)
  found := found.qsort (fun a b => a.1.toString < b.1.toString)
  let mut rows : Array Json := #[]
  for (name, ci) in found do
    let owner := match env.getModuleIdxFor? name with
      | none => env.mainModule.toString
      | some idx => (env.header.moduleNames[idx.toNat]!).toString
    let value := match ci with
      | .thmInfo t => some t.value
      | .defnInfo d => some d.value
      | _ => none
    let ax := ((← Lean.collectAxioms name).map Name.toString).qsort (· < ·)
    rows := rows.push <| Json.mkObj [
        ("name", toJson name.toString), ("actualOwner", toJson owner),
        ("privateUserName", toJson ((Lean.privateToUserName? name).map Name.toString)),
        ("kind", toJson (match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other")),
        ("levelParams", toJson (ci.levelParams.map Name.toString)),
        ("type", PiExponentInterfaceSnapshot.exprJson ci.type), ("value", Json.null),
        ("closedType", toJson (!ci.type.hasMVar && !ci.type.hasFVar)),
        ("closedValue", toJson (value.map (fun e => !e.hasMVar && !e.hasFVar))),
        ("isProp", toJson (← isProp ci.type)),
        ("typeRefs", toJson ((ci.type.getUsedConstants.map Name.toString).qsort (· < ·))),
        ("valueRefs", toJson ((value.map (fun e => e.getUsedConstants.map Name.toString) |>.getD #[]).qsort (· < ·))),
      ("axioms", toJson ax)]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("probeMainModule", toJson env.mainModule.toString),
    ("ownerModules", toJson owners), ("rawOwnedCIs", Json.arr rows)]).compress
end AnalyticAggregateOwnedInventory
'''


def final_snapshots(base_files):
    old = workspace_rel(CANDIDATE)
    new = workspace_rel(STAGE)
    source = base_files[candidate.SOURCE_SNAPSHOT].decode("utf-8")
    generated = base_files[candidate.GENERATED_SNAPSHOT].decode("utf-8")
    need(source.count(old) == 1 and generated.count(old) == 1,
         "Candidate snapshot output locator differs")
    source = source.replace(old, new, 1)
    generated = generated.replace(old, new, 1)
    owners = [candidate.theorem_module(n) for n, *_ in candidate.CHILDREN] + [candidate.SOLUTION_MODULE]
    need(generated.count("\nrun_meta do\n") == 1
         and generated.count("  SourceRootGraphSnapshot.exportRows ") == 1,
         "Candidate generated type/ref probe structure differs")
    generated = generated.replace("\nrun_meta do\n", "\n" + INVENTORY + "\nrun_meta do\n", 1)
    early = ("  AnalyticAggregateOwnedInventory.exportOwnedInventory #[" +
             ", ".join(json.dumps(x) for x in owners) + "] " +
             json.dumps(workspace_rel(STAGE / OWNED_JSON)) + "\n")
    generated = generated.replace("  SourceRootGraphSnapshot.exportRows ",
                                  early + "  SourceRootGraphSnapshot.exportRows ", 1)
    return source.encode("utf-8"), generated.encode("utf-8")


def final_files():
    pins, report = boundary()
    base_files = candidate.files()
    output = {k: v for k, v in base_files.items() if k != "pending-preparation.json"}
    source, generated = final_snapshots(base_files)
    output[candidate.SOURCE_SNAPSHOT] = source
    output[candidate.GENERATED_SNAPSHOT] = generated
    for path in base_files:
        pin(pins, CANDIDATE / path)
    target_files = [candidate.theorem_module(n).replace(".", "/") + ".lean"
                    for n, *_ in candidate.CHILDREN]
    files = target_files + [candidate.SOLUTION_FILE,
                            candidate.SOURCE_SNAPSHOT, candidate.GENERATED_SNAPSHOT]
    imports = [[candidate.CANONICAL_MODULE, candidate.CORE_MODULE, candidate.PROVIDER_MODULE]] * 2 + [
        [candidate.CANONICAL_MODULE, candidate.CORE_MODULE, candidate.PROVIDER_MODULE]
        + [candidate.theorem_module(n) for n, *_ in candidate.CHILDREN],
        ["Lean", candidate.SOURCE_MODULE], ["Lean", candidate.SOLUTION_MODULE]]
    modes = ["emit-olean", "emit-olean", "emit-olean", "modecheck", "modecheck"]
    for path in [SELF, CONSUMER, RUNNER, RUNTIME, Path(candidate.__file__),
                 Path(data.__file__), Path(data_certifier.__file__)]:
        pin(pins, path)
    # Bounded preflight accepts mission-local task files only. The complete
    # provenance ledger, including historical external dependency OLeans,
    # remains in preparation and is replayed by boundary(). Actual imports
    # are independently recorded by each compiler sidecar.
    manifest_pins = {name: value for name, value in pins.items()
                     if not Path(name).is_absolute()}
    need(all((TASK / name).resolve().is_relative_to(TASK.resolve())
             for name in manifest_pins), "A manifest input escapes the mission")
    manifest_rows, commands = {}, []
    for i, (name, mode, imported) in enumerate(zip(files, modes, imports, strict=True), 1):
        manifest = f"c{i}.json"
        output[manifest] = encode({
            "schema_version": 1, "artifact_kind": "ap19-analyticAggregate-two-child-bounded-manifest",
            "output": workspace_rel(STAGE / name), "output_sha256": digest(output[name]),
            "imports": imported, "input_hashes": manifest_pins, "runtime_sha256": sha(RUNTIME),
            "mode": mode, "emit_olean": mode == "emit-olean", "timeout_seconds": 300,
            "bounded_runner": rel(RUNNER), "bounded_runner_sha256": sha(RUNNER),
            "validated": False, "submission_ready": False})
        manifest_rows[name] = {"sha256": digest(output[name]), "manifest": manifest,
                               "mode": mode, "imports": imported,
                               "emit_olean": mode == "emit-olean"}
        commands.append("& '" + PYTHON + "' scripts/preflight_staged_module_windows_bounded.py " +
                        "ap19/analytic-aggregate-two-child-reduction-final/" + name +
                        " --root ap19/analytic-aggregate-two-child-reduction-final" +
                        " --imports-manifest ap19/analytic-aggregate-two-child-reduction-final/" + manifest +
                        " --timeout-seconds 300" + (" --emit-olean" if mode == "emit-olean" else ""))
    plan = read(CANDIDATE / "pending-preparation.json")
    plan.update({"artifact_kind": "ap19-analyticAggregate-two-child-Open-sketch-final-preparation",
                 "boundary": report, "input_hashes": pins, "files": manifest_rows,
                 "source_snapshot": candidate.SOURCE_SNAPSHOT,
                 "generated_snapshot": candidate.GENERATED_SNAPSHOT,
                 "source_snapshot_json": SOURCE_JSON, "generated_snapshot_json": GENERATED_JSON,
                 "generated_owned_ci_inventory": OWNED_JSON,
                 "actual_owned_CIs_exported_before_root_classification": True,
                 "compile_commands": commands, "final_compiler_manifests_created": True,
                 "Open_child_sorryAx_expected": True,
                 "source_original_Std3_expected": True,
                 "closed_proof": False, "validated": False, "submission_ready": False})
    output["preparation.json"] = encode(plan)
    output["compile-commands.txt"] = ("\n".join(commands) + "\n").encode()
    return output


def check_only():
    expected = final_files()
    for name, raw in expected.items():
        need((STAGE / name).read_bytes() == raw, "Final Open analytic stage changed: " + name)
    return {"checked_files": len(expected), "five_bounded_contexts": True,
            "Open_sketch_only": True, "closed_proof": False,
            "Lean_started_by_finalizer": False, "API_used": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    flags = parser.add_mutually_exclusive_group(required=True)
    flags.add_argument("--finalize", action="store_true")
    flags.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.finalize:
        for name, raw in final_files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, "Refusing overwrite of final Open analytic stage: " + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
