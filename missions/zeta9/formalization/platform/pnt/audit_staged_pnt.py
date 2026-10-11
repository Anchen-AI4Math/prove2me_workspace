"""Hash-bound type/definition fidelity and explicit Proved-boundary audit."""
from pathlib import Path
import json, hashlib, sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
STANDARD = {"propext","Classical.choice","Quot.sound"}

def load(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))
def sha(data):
    return hashlib.sha256(data).hexdigest()
def records(p):
    return {r["label"]:r for r in [json.loads(x) for x in p.read_text(encoding="utf-8-sig").splitlines() if x.startswith("{")]}
def dump(p,obj):
    p.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")

request = load(OUT/"problems-request.json")
receipt = load(OUT/"staged-compile-receipt.json")
provenance = load(OUT/"integration-provenance.json")
plan = load(OUT/"decl-plan.json")
readback = load(OUT/"medium-pnt-proved-readback.json")
assert readback["status"] == "Proved" and readback["mathlib_rev"] == request["env"]
assert receipt["canonical_solution_bytes_identical_across_modes"] is True
assert receipt["stub_mirror_is_proof"] is False
if "completion" in receipt:
    assert receipt["completion"] == "complete"
receipt_rows = {r["label"]: r for r in receipt["rows"]}
assert len(receipt_rows) == 29, len(receipt_rows)
def verified_exit(row, seen=None):
    if row["exit_code"] == 0:
        return True
    assert row["exit_code"] is None
    assert row["evidence_kind"] in {"retained_build_object", "retained_type_report"}
    seen = set() if seen is None else seen
    assert row["label"] not in seen
    seen.add(row["label"])
    verifier = receipt_rows[row["verification_report"]]
    return verified_exit(verifier, seen)
for row in receipt["rows"]:
    assert verified_exit(row), row
    assert sha((OUT/row["source"]).read_bytes()) == row["source_sha256"], row["source"]
    assert sha((OUT/row["log"]).read_bytes()) == row["log_sha256"], row["log"]
    if row["output"]:
        assert sha(Path(row["output"]).read_bytes()) == row["output_sha256"], row["output"]
for row in plan["source_receipts"]:
    assert sha(Path(row["source"]).read_bytes()) == row["source_sha256"]
    assert sha(Path(row["oracle_input"]).read_bytes()) == row["oracle_input_sha256"]

original = records(OUT/"types-original.log")
native_boundary = records(OUT/"types-boundary-native.log")["MediumPNT"]
stub_boundary = records(OUT/"types-boundary-stub.log")["MediumPNT"]
assert native_boundary["type"] == original["MediumPNT"]["type"] == stub_boundary["type"]
assert set(native_boundary["axioms"]) <= STANDARD
assert set(original["MediumPNT"]["axioms"]) <= STANDARD
assert "sorryAx" in stub_boundary["axioms"]
assert set(stub_boundary["axioms"]) <= STANDARD | {"sorryAx"}
for mode, boundary in [("native", native_boundary), ("stub", stub_boundary)]:
    # The already-complete boundary reports have no retained historical exit
    # code; their records are independently repeated in a fresh Solution import.
    fresh_boundary = records(OUT/f"types-{mode}-0-solution.log")["MediumPNT"]
    assert boundary == fresh_boundary
assert [x for x in provenance["imports"] if x.startswith("Theorems.")] == ["Theorems.Thm_MediumPNT"]
assert plan["native_clearing_proof_inlined"] and plan["unselected_original_global_solution_deleted"]
assert provenance["new_public_definitions"] == []
checks = []
for i,p in enumerate(request["problems"]):
    full = p["theorem_name"]
    nr = records(OUT/f"types-native-{i}-solution.log")
    sr = records(OUT/f"types-stub-{i}-solution.log")
    rr = records(OUT/f"types-{i}-reference.log")
    types = [original[full]["type"],nr[full]["type"],sr[full]["type"],rr[full]["type"]]
    assert len(set(types)) == 1, (full,types)
    assert set(original[full]["axioms"]) <= STANDARD
    assert set(nr[full]["axioms"]) <= STANDARD
    assert "sorryAx" in sr[full]["axioms"]
    assert set(sr[full]["axioms"]) <= STANDARD | {"sorryAx"}
    assert "sorryAx" in rr[full]["axioms"]
    assert set(rr[full]["axioms"]) <= STANDARD | {"sorryAx"}
    for obj in plan["reused_public_definitions"]:
        actual = original[obj]
        for d in [nr[obj],sr[obj],rr[obj]]:
            assert d["type"] == actual["type"], (full,obj,"type")
            assert d["definitionValue"] == actual["definitionValue"], (full,obj,"definitionValue")
            assert set(d["axioms"]) <= STANDARD
    sol = OUT/"staged"/p["local_solution"]
    ref = OUT/"staged"/p["local_reference"]
    target = provenance["targets"][full]
    assert sha(sol.read_bytes()) == target["solution_sha256"]
    assert sha(ref.read_bytes()) == target["reference_sha256"]
    assert sha(p["formal_statement"].encode()) == target["formal_statement_sha256"]
    assert ref.read_text(encoding="utf-8") == p["preamble"]+"\n"+p["formal_statement"]+"\n"
    checks.append({"theorem_name":full,"type_equal_original_native_stub_reference":True,
        "exact_elaborated_type":types[0],"original_axioms":original[full]["axioms"],
        "native_canonical_solution_axioms":nr[full]["axioms"],
        "stub_canonical_solution_axioms":sr[full]["axioms"],
        "reference_axioms":rr[full]["axioms"],
        "stub_solution_is_closed_proof":False,"native_solution_is_closed_proof":True,
        "public_definition_types_and_values_equal":True,
        "solution":p["local_solution"],"solution_sha256":sha(sol.read_bytes()),
        "reference":p["local_reference"],"reference_sha256":sha(ref.read_bytes()),
        "source_fact":target["stage2_declaration_fact"],
        "type_report_paths":["types-original.log",f"types-native-{i}-solution.log",f"types-stub-{i}-solution.log",f"types-{i}-reference.log"]})

audit = {"verdict":"PASS_OFFLINE_MECHANICAL_FIDELITY",
    "four_original_endpoints":True,"type_equality":"exact pp.fullNames=true, pp.universes=false output equality, in separate imported environments",
    "new_pnt_or_harmonic_baseline_assumptions":[],"new_public_definitions":[],
    "only_external_proved_theorem_boundary":{
        "name":"MediumPNT","id":readback["theorem_id"],"status":readback["status"],
        "readback":"medium-pnt-proved-readback.json","readback_sha256":sha((OUT/"medium-pnt-proved-readback.json").read_bytes()),
        "native_and_platform_boundary_type_equal":True,
        "native_axioms":native_boundary["axioms"],"stub_axioms":stub_boundary["axioms"],
        "stub_is_proof":False,"boundary_type_reports":["types-boundary-native.log","types-boundary-stub.log"],
        "source_commits_differ":"Native PNT 55270df807213fc3584523d09e0311d7dc073ff5; saved platform source f55e85551ac10e96d98262a354cfcaac2825f2da; statements and Mathlib environment match, no byte equality claimed."},
    "canonical_stub_build_standard_three_axioms":False,
    "native_identical_canonical_solution_bytes_standard_three_axioms":True,
    "root_formal_build_with_type_only_medium_pnt_mirror_is_closed_proof":False,
    "native_actual_pnt_proof_evidence":"verification/formalization-pnt-dependency-2026-10-02/kernel-replay-receipt.json",
    "independent_original_review":"independent-original-review.json",
    "clear_denominator_full_proof_inline":True,
    "source_position_authority":"Actually executed official Lean declaration graph and sketch oracle, plus parser-span/input-snapshot extension; no regex for source positions.",
    "checks":checks,"staged_compile_receipt":"staged-compile-receipt.json",
    "staged_compile_receipt_sha256":sha((OUT/"staged-compile-receipt.json").read_bytes()),
    "resumption_evidence":{
        "retained_build_objects":sum(r.get("evidence_kind") == "retained_build_object" for r in receipt["rows"]),
        "retained_type_reports":sum(r.get("evidence_kind") == "retained_type_report" for r in receipt["rows"]),
        "fresh_exit_zero_type_reports":sum(r.get("evidence_kind") == "fresh_type_report" and r["exit_code"] == 0 for r in receipt["rows"]),
        "historical_exit_codes_fabricated":False,
        "retained_objects_verified_by_fresh_imports":True,
        "original_type_report_search_path_corrected":True,
        "prior_failed_original_report":"types-original.before-resume.log",
        "prior_failed_original_report_sha256":sha((OUT/"types-original.before-resume.log").read_bytes()) if (OUT/"types-original.before-resume.log").exists() else None,
        "proof_source_rebuilt_during_resumption":False,
        "resume_script":"resume_staged_pnt.py",
        "resume_script_sha256":sha((OUT/"resume_staged_pnt.py").read_bytes())},
    "publisher_gate":{"allowed_proved_boundary_ids":[readback["theorem_id"]],
        "native_standard_three_required":True,"exact_original_solution_reference_type_required":True,
        "unchanged_payload_hash_required":True,"server_proof_acceptance_still_required":True,
        "pending_theorem_boundaries_allowed":False},
    "staged_root_paths":[p[k] for p in request["problems"] for k in ["local_solution","local_reference"]]}
copy_plan = {
    "action": "parent installs only after independent staged review",
    "root_shared_paths_written_by_this_offline_batch": [],
    "canonical_sources": "staged",
    "files": [{"source": str(OUT/"staged"/p[k]), "destination": str(ROOT/p[k]),
               "relative_destination": p[k], "sha256": sha((OUT/"staged"/p[k]).read_bytes()),
               "destination_existed_at_plan_time": (ROOT/p[k]).exists()}
              for p in request["problems"] for k in ["local_solution", "local_reference"]],
    "boundary_mirror": {
        "destination": str(ROOT/"Theorems/Thm_MediumPNT.lean"),
        "stub_source": str(OUT/"boundary-mirror/stub/Theorems/Thm_MediumPNT.lean"),
        "stub_sha256": sha((OUT/"boundary-mirror/stub/Theorems/Thm_MediumPNT.lean").read_bytes()),
        "native_source": str(OUT/"boundary-mirror/native/Theorems/Thm_MediumPNT.lean"),
        "native_sha256": sha((OUT/"boundary-mirror/native/Theorems/Thm_MediumPNT.lean").read_bytes()),
        "destination_existed_at_plan_time": (ROOT/"Theorems/Thm_MediumPNT.lean").exists(),
        "stub_imports_the_platform_proved_boundary": readback["theorem_id"],
        "stub_contains_sorryAx_and_is_not_a_closed_proof": True,
        "native_imports_actual_original_pnt_cache": True,
        "install_policy": "Choose one honest mirror for the intended environment; never overwrite an existing nonidentical root file without reconciling it. A root stub build verifies integration only; the genuine native matrix supplies local closed-proof evidence.",
    },
    "parent_followup": ["Add the eight stable root module paths and boundary ownership to the current task scope only.",
                        "Run python scripts/workspace.py check.",
                        "Run python scripts/workspace.py build zeta9, with dry-run first if needed.",
                        "Report any root stub build as integration verification containing sorryAx.",
                        "Platform acceptance requires the unchanged payload and the existing public Proved MediumPNT boundary."]
}
dump(OUT/"root-copy-plan.json", copy_plan)
audit["root_copy_plan"] = "root-copy-plan.json"
audit["root_copy_plan_sha256"] = sha((OUT/"root-copy-plan.json").read_bytes())
dump(OUT/"integration-audit.json",audit)
manifest = []
frozen = set([OUT/"staged"/x for x in audit["staged_root_paths"]]+[
    OUT/x for x in ["problems-request.json", "integration-provenance.json", "decl-plan.json", "boundary-policy.json",
                    "staged-compile-receipt.json", "integration-audit.json", "medium-pnt-proved-readback.json",
                    "independent-original-review.json", "original-endpoint-types.json", "stage2-extract-receipt.json",
                    "decl-graph.jsonl", "reachable-local-graph.json", "proof-core.lean", "prepare_pnt.py",
                    "compile_staged_pnt.py", "resume_staged_pnt.py", "audit_staged_pnt.py", "root-copy-plan.json"]])
for row in receipt["rows"]:
    frozen.add(OUT/row["source"])
    frozen.add(OUT/row["log"])
    if row["output"]:
        frozen.add(Path(row["output"]))
for row in plan["source_receipts"]:
    frozen.add(Path(row["oracle_input"]))
    frozen.add(OUT/(row["module"].replace(".","_")+"-sketch.jsonl"))
if (OUT/"types-original.before-resume.log").exists():
    frozen.add(OUT/"types-original.before-resume.log")
for p in sorted(frozen):
    manifest.append(sha(p.read_bytes())+"  "+p.relative_to(OUT).as_posix())
(OUT/"SHA256SUMS.txt").write_text("\n".join(manifest)+"\n",encoding="utf-8")
print(json.dumps({"verdict":audit["verdict"],"endpoints":len(checks),"native_standard_three":True,
                  "stub_standard_three":False,"only_allowed_proved_boundary":readback["theorem_id"]},ensure_ascii=False))
