"""Finish the independent offline review after all actual Lean runs succeed."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
HERE = Path(__file__).resolve().parent
BATCH = HERE.parent
TASK = BATCH.parents[2]
ROOT = TASK.parents[1]
PROJECT = HERE / "project"
NS = "ZetaNine.CoefficientMap"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
DEFS = ["numerator", "poleProduct", "actualR", "clearedPoleProduct", "clearedR", "leadingPoleCoefficient", "weightedR", "clearedWeightedR", "weightedLeadingPoleCoefficient"]
TARGETS = ["clear_highest_pole", "leadingPoleCoefficient_eq", "weightedLeadingPoleCoefficient_eq_even"]
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):
    return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(p, s):
    p.write_text(s, encoding="utf-8", newline="\n")

reconstruction = load(HERE / "reconstruction-report.json")
checks = reconstruction["checks"]
def check(name, okay, detail=None):
    checks.append({"name":name,"pass":bool(okay),"evidence":detail})
    assert okay, name

receipt = load(HERE / "compile-receipt.json")
check("independent_fresh_builds_oracles_and_import_reports_all_exit_zero", receipt.get("complete") is True and len(receipt["rows"]) == 22 and all(r["exit_code"] == 0 and sha(HERE / r["log"]) == r["log_sha256"] for r in receipt["rows"]), {"runs":22,"fresh_source_builds":8,"actual_oracles":2,"actual_import_reports":11,"toolchain_probe":1,"one_Lean_process_at_a_time":True,"original_or_staged_olean_cache_borrowed":False,"shared_pinned_Mathlib_dependency_cache_only":True})
version = (HERE / "toolchain.log").read_text(encoding="utf-8-sig")
env = os.environ.copy()
env.pop("LEAN_PATH", None)
rev = subprocess.run(["git","-C",str(ROOT / ".lake/packages/mathlib"),"rev-parse","HEAD"],capture_output=True,env=env)
(HERE / "mathlib-revision.log").write_bytes(rev.stdout + rev.stderr)
check("actual_Lean_4_33_1_and_local_Mathlib_pin_verified", "version 4.33.1" in version and rev.returncode == 0 and rev.stdout.decode().strip() == "0df444a360eaa60ab8c11dca51a86af692955474")

original = {r["label"]:r for r in rows(HERE / "types_original.log")}
labels = ["types_definition"] + [f"types_{i}_{kind}" for i in range(3) for kind in ["solution","reference"]]
reports = {label:{r["label"]:r for r in rows(HERE / (label + ".log"))} for label in labels}
definition_comparisons = []
for name in DEFS:
    full = NS + "." + name
    base = original[full]
    assert base["value"] is not None
    for label,report in reports.items():
        got = report[full]
        definition_comparisons.append({"declaration":full,"context":label,"type_equal":got["type"] == base["type"],"value_equal":got["value"] == base["value"],"axioms":got["axioms"]})
check("all_nine_Def_types_values_match_original_in_every_actual_import_environment", len(definition_comparisons) == 63 and all(r["type_equal"] and r["value_equal"] and set(r["axioms"]) <= STANDARD for r in definition_comparisons), {"definitions":9,"comparison_contexts":7,"exact_full_name_type_and_value_comparisons":63})
target_evidence = []
for i, name in enumerate(TARGETS):
    full = NS + "." + name
    orig = original[full]
    sol = reports[f"types_{i}_solution"][full]
    ref = reports[f"types_{i}_reference"][full]
    target_evidence.append({"theorem":full,"actual_type":orig["type"],"original_axioms":orig["axioms"],"solution_axioms":sol["axioms"],"reference_axioms":ref["axioms"],"original_solution_reference_type_equal":orig["type"] == sol["type"] == ref["type"]})
check("three_original_solution_reference_types_equal_no_extra_hypotheses", all(t["original_solution_reference_type_equal"] for t in target_evidence), target_evidence)
check("three_complete_solution_proofs_exact_standard_three_axioms", all(set(t["solution_axioms"]) == STANDARD and set(t["original_axioms"]) == STANDARD for t in target_evidence), {"allowed_axioms":sorted(STANDARD)})
check("reference_theorems_are_intentional_sorry_stubs_not_used_by_Solutions", all("sorryAx" in t["reference_axioms"] for t in target_evidence) and all("import Theorems." not in (BATCH / "staged" / ("Solutions/Sol_ZetaNine_CoefficientMap_" + n + ".lean")).read_text(encoding="utf-8") for n in TARGETS))
helper_rows = [rows(HERE / f"helpers_{i}.log") for i in range(3)]
check("all_eighteen_original_helpers_and_wrapper_per_solution_no_extra_axioms", all(len(rs) == 19 and all(set(r["axioms"]) <= STANDARD for r in rs) for rs in helper_rows), {"proof_records":57,"includes": "all 18 original inline mathematical proofs and the solution wrapper in each separate imported environment"})

# Author reports are independently cross-checked rather than trusted as proof.
for label in ["types_original"] + labels:
    author_label = label.replace("_","-")
    actual_rows = rows(HERE / (label + ".log"))
    author_rows = rows(BATCH / (author_label + ".log"))
    normal = lambda rs: sorted(json.dumps({**r,"axioms":sorted(r["axioms"])},sort_keys=True,ensure_ascii=False) for r in rs)
    check(label + "_author_report_independently_recomputed", normal(actual_rows) == normal(author_rows))

boundary_command = ["lake","env","lean","BoundaryAudit.lean"]
boundary = subprocess.run(boundary_command,cwd=PROJECT,env=env,capture_output=True)
(HERE / "boundary-audit.log").write_bytes(boundary.stdout + boundary.stderr)
write(HERE / "boundary-audit-exit.txt",str(boundary.returncode) + "\n")
if boundary.returncode:
    print((HERE / "boundary-audit.log").read_text(encoding="utf-8-sig"),flush=True)
boundary_rows = rows(HERE / "boundary-audit.log")
check("independent_actual_statements_denominator_n0_integer_and_W_cancellation_compile", boundary.returncode == 0 and len(boundary_rows) == 8 and all(set(r["axioms"]) <= STANDARD for r in boundary_rows), {"exit_code":boundary.returncode,"records":len(boundary_rows),"counterexample":"n=2,j=1,W=X+C(1) is a nonzero polynomial but its actual weighted highest coefficient is zero"})
write(HERE / "boundary-audit-receipt.json",json.dumps({"command":boundary_command,"working_directory":str(PROJECT),"exit_code":boundary.returncode,"source_sha256":sha(PROJECT / "BoundaryAudit.lean"),"log_sha256":sha(HERE / "boundary-audit.log"),"records":boundary_rows},ensure_ascii=False,indent=2) + "\n")

definition_request = load(BATCH / "definitions-request.json")[0]
problem_request = load(BATCH / "problems-request.json")
definition_fields = {"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"}
problem_fields = {"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("offline_requests_use_only_saved_documented_fields", set(definition_request) <= definition_fields and {"definition_name","definition_title","definition"} <= set(definition_request) and set(problem_request) == {"env","private","problems"} and all(set(p) <= problem_fields and {"theorem_name","theorem_title","formal_statement","natural_language_statement"} <= set(p) and len(p["theorem_title"]) <= 200 and p["formal_statement"].endswith(":= by sorry") for p in problem_request["problems"]), {"document":"formalization/platform/readback-2026-10-03/api-docs/references/contribute.md","definition_file_is_one_local_list_entry_to_be_posted_as_a_single_request":True,"API_called_by_reviewer":False})
check("public_prose_faithful_regular_domain_all_n_and_arbitrary_W_may_vanish", "every rational point" in problem_request["problems"][0]["natural_language_statement"] and "without a parity assumption" in problem_request["problems"][1]["natural_language_statement"] and "including the zero polynomial" in problem_request["problems"][2]["natural_language_statement"] and "can be zero" in problem_request["problems"][2]["natural_language_statement"])

plan = load(BATCH / "root-copy-plan.json")
installed = []
for f in plan["files"]:
    dest = ROOT / f["root_relative_destination"]
    installed.append({"path":f["root_relative_destination"],"exists":dest.exists(),"bytes":dest.stat().st_size if dest.exists() else None,"sha256":sha(dest) if dest.exists() else None,"expected":f["sha256"]})
check("all_seven_installed_root_files_equal_frozen_staged_bytes", all(i["exists"] and i["sha256"] == i["expected"] for i in installed), installed)

# Verify the author freeze again after the complete independent replay.
hashes = {}
for line in (BATCH / "SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines():
    expected, rel = line.split("  ",1)
    p = (BATCH / rel).resolve()
    assert p.is_relative_to(TASK) and sha(p) == expected
    hashes[p.relative_to(TASK).as_posix()] = expected
for p in [TASK / "formalization/CoefficientMap.lean", BATCH / "SHA256SUMS.txt", BATCH / "root-copy-plan.json", TASK / "verification/formalization-coefficient-map-2026-10-03/independent-review.json", TASK / "formalization/platform/readback-2026-10-03/api-docs/references/contribute.md"]:
    hashes[p.relative_to(TASK).as_posix()] = sha(p)
for i in installed:
    hashes[i["path"]] = i["sha256"]
for p in HERE.iterdir():
    if p.is_file():
        hashes[p.relative_to(TASK).as_posix()] = sha(p)
for p in list(PROJECT.glob("*.lean")) + [PROJECT / "lake-manifest.json",PROJECT / "lean-toolchain",PROJECT / "missions/zeta9/formalization/CoefficientMap.lean"] + [PROJECT / f["root_relative_destination"] for f in plan["files"]]:
    hashes[p.relative_to(TASK).as_posix()] = sha(p)
check("author_original_request_stage_and_receipts_remain_hash_unchanged", len(reconstruction["frozen_manifest_members"]) == 96 and sha(BATCH / "author-audit.json") == "f5d04a3297e7c28f233fec3b7db822c8b63570dab1b00c910b0c3286490fc1e6")

limitations = [
    "Finite highest cleared-pole entry only. The coefficient is genuinely defined from n!^7 products and the erased pole-product denominator; the closed binomial formula is a proved identity, never substituted as a definition.",
    "The unweighted highest coefficient is integral and nonzero for every j<=n, including n=0. For even n the selected weighted formula allows arbitrary W in Q[X]; W may cancel the local highest coefficient, including nonzero W=X+1 at n=2,j=1. No weighted nonvanishing is claimed.",
    "The regular-point bridge requires every t+k (0<=k<=n) to be nonzero. Rational division is total in Lean: actualR evaluated at a pole is not used as the coefficient. clearedPoleProduct at -j is independently checked nonzero.",
    "This batch does not establish a full Laurent expansion, lower partial-fraction coefficients, the original aggregated F map, its inverse or invertibility, exact infinite L-sums, a J certificate, or zeta(9) irrationality. Other local jet or injectivity files are not imports or proof boundaries of this batch.",
    "Reference Theorems contain sorryAx intentionally as statements. The three complete Solutions import only the genuine Definition and Mathlib, retain all 18 original proofs, and have exactly the three standard axioms. Offline replay does not assert publication, API acceptance, or a live platform status."
]
result = {"schema_version":1,"review_role":"independent offline mathematical-source integration review","reviewed_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"verdict":"PASS" if all(c["pass"] for c in checks) else "FAIL","checks":checks,"sha256":dict(sorted(hashes.items())),"findings":[],"targets":target_evidence,"definition_comparisons":definition_comparisons,"fresh_compile":{"receipt":"formalization/platform/coefficient-map/independent-review/compile-receipt.json","all_runs_observed_exit_zero":True,"eight_fresh_source_builds":True,"actual_Stage1_Stage2_reexecuted":True,"eleven_import_reports":True,"additional_boundary_audit_exit":boundary.returncode},"review_wrapper_attempt_history":[{"attempt":1,"exit_code":1,"source":"formalization/platform/coefficient-map/independent-review/project/BoundaryAudit-attempt1.lean","log":"formalization/platform/coefficient-map/independent-review/boundary-audit-attempt1.log","errors":"Review wrapper passed an unnecessary hj to the stronger original denominator theorem and omitted coeff_one simplification in the nonzero-polynomial example. Only the independent wrapper was corrected. Original/staged source builds and their eleven import audits all succeeded first try."},{"attempt":2,"exit_code":boundary.returncode,"source":"formalization/platform/coefficient-map/independent-review/project/BoundaryAudit.lean","log":"formalization/platform/coefficient-map/independent-review/boundary-audit.log"}],"source_position_counts":{"Stage1_environment_records":28,"Stage1_source_declarations":27,"compiler_generated_record":"ZetaNine.CoefficientMap.clearedPoleProduct.eq_1","Stage2_decl":27,"Stage2_ref":92,"Stage2_command":45},"installed_root":installed,"limitations":limitations,"reviewer_root_writes":False,"reviewer_scope_writes":False,"reviewer_API_calls":False,"credentials_read":False,"platform_published_claimed":False,"platform_accepted_claimed":False}
destination = BATCH / "independent-integration-review.json"
write(destination,json.dumps(result,ensure_ascii=False,indent=2) + "\n")
summary = """# Independent CoefficientMap integration review

PASS. The independently re-executed Lean declaration and parser/reference oracles match the frozen facts, and an independent byte-span reconstruction reproduces all seven staged files exactly. Stage1 has 28 environment records: 27 actual source declarations plus the generated clearedPoleProduct.eq_1. Stage2 has 27 declarations, 92 references and 45 commands. Nine genuine definition spans move unchanged into the lightweight Definition; eight diagnostic spans are removed; every Solution retains all 18 original mathematical proofs, with only the selected binding and resolved references renamed.

An isolated new project compiled the exact original source, the Definition, all three complete Solutions and all three reference statements. Both oracles, eight original/definition/solution/reference type-value imports and three all-helper imports also exited zero, with one Lean process at a time. No original or staged olean was borrowed. Only pinned Mathlib dependency artifacts were reused. Actual Lean 4.33.1 and the local Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474 were verified.

All nine definition types and values match the original in every imported context (63 exact comparisons). Each solution type is identical to the original and reference type, without extra hypotheses. The three complete solution wrappers have exactly propext, Classical.choice and Quot.sound; all 57 helper/wrapper records have no other axiom. Reference statements intentionally contain sorryAx and are never imported by a Solution.

Eight additional independently compiled statements check the original regular domain, erased denominator nonzero, full unweighted/weighted signatures, unweighted integrality/nonzero, n=0 and W cancellation. A nonzero polynomial W=X+1 cancels the weighted highest coefficient at n=2,j=1. The arbitrary-W theorem correctly permits this.

This batch establishes the finite highest cleared-pole entry. Full Laurent expansion, lower partial fractions, the original aggregated F/inverse/invertibility, exact infinite L-sums, J and irrationality remain outside it. The report verifies all 96 frozen hashes and binds original/request/staged/oracle/build evidence plus all seven parent's installed root files. Reviewer writes are confined to the new review files; frozen author/source/root/scope files are unchanged. No API or credentials were accessed and no platform publication or acceptance is asserted.

Machine-readable result: independent-integration-review.json. Detailed independent compile receipt, reconstructed span report and boundary/type/helper logs: independent-review/. The source-only Definition and three complete proofs are exactly the frozen staged bytes and the installed root bytes.

The first additional boundary-review wrapper attempt had two local invocation/simplification errors. Its source, error log and exit 1 are preserved. The corrected wrapper compiles with exit 0 and standard axioms. The exact original/staged source builds, oracles and eleven type/helper imports all succeeded on their first independent run.
"""
write(BATCH / "independent-integration-review.md",summary)
sum_paths = [destination,BATCH / "independent-integration-review.md"] + [p for p in HERE.iterdir() if p.is_file()]
write(BATCH / "independent-integration-review-SHA256SUMS.txt","".join(sha(p) + "  " + p.relative_to(TASK).as_posix() + "\n" for p in sorted(sum_paths)))
print(json.dumps({"verdict":result["verdict"],"checks":len(checks),"review_sha256":sha(destination),"hash_bindings":len(hashes),"installed_root_files":len(installed),"fresh_main_runs":len(receipt["rows"]),"boundary_exit":boundary.returncode},ensure_ascii=False),flush=True)
