"""Freeze an independent FiniteSum transplant verdict from actual fresh runs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
BATCH = OUT.parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
OLD = TASK / "verification/formalization-coefficient-map-finite-sum-2026-10-03"
NS = "ZetaNine.CoefficientMapFiniteSum"
STANDARD = {"propext","Classical.choice","Quot.sound"}
TARGETS = ["actual_finite_harmonic_identity","actual_grouped_finite_identity","harmonic_difference_eq_shifted"]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p): return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(p,obj): p.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
def index(rs):
    result = {r["declaration"]:r for r in rs}
    assert len(result) == len(rs)
    return result
def standard(r): return set(r["axioms"]) <= STANDARD
def normalize(text):
    for name in TARGETS: text = text.replace(NS+".checked_"+name,NS+"."+name)
    return text
def payload(rs): return {r["label"]:{"type":r["type"],"value":r["value"],"axioms":sorted(r["axioms"])} for r in rs}
mechanical = load(OUT / "mechanical-checks.json")
checks = list(mechanical["checks"])
def check(name,passed,detail=None):
    checks.append({"name":name,"pass":bool(passed),"detail":detail})
    write(OUT / "finalizer-development-checks.json", {"checks":checks,"complete":False})
    assert passed,name

prep,replay = load(OUT/"prepare-compile-receipt.json"),load(OUT/"replay-compile-receipt.json")
invocations = prep["rows"] + replay["rows"]
for row in invocations:
    assert row["exit_code"] == int((OUT/row["exit_file"]).read_text().strip()) == 0
    assert sha(ROOT/row["source_root_relative"]) == row["source_sha256"]
    for field in ["log","exit_file","wrapper","output","stdout_copy"]:
        if row.get(field): assert sha(OUT/row[field]) == row["stdout_sha256" if field == "stdout_copy" else field+"_sha256"]
    wrapper = (OUT/row["wrapper"]).read_text(encoding="utf-8")
    assert (OUT/"cache").as_posix() in wrapper and (BATCH/"project").as_posix() not in wrapper
check("40_fresh_independent_Lean_runs_all_actual_exit_zero",len(prep["rows"]) == 11 and len(replay["rows"]) == 29 and len(invocations) == 40 and prep["complete"] and replay["complete"],
    {"preparation":11,"final_replay":29,"native_staged_objects_borrowed":False,"separate_new_native_and_platform_caches":True})
environment = load(OUT/"actual-environment.json")
check("observed_Lean_4_33_1_and_root_pinned_Mathlib_revision",environment["lean_toolchain"] == "leanprover/lean4:v4.33.1" and
    "4.33.1" in environment["lean_runtime_stdout"] and environment["actual_runtime_exit_code"] == 0 and
    environment["mathlib_manifest_revision"] == "0df444a360eaa60ab8c11dca51a86af692955474" and
    sha(ROOT/"lake-manifest.json") == environment["root_lake_manifest_sha256"] and sha(ROOT/"lean-toolchain") == environment["root_toolchain_sha256"] and
    (OUT/"actual-toolchain-exit.txt").read_text().strip() == "0",{"separate_lightweight_runtime_probe_exit":0})
original = index(rows(OUT/"replay-types_original.log"))
definitions = index(rows(OUT/"replay-types_definition.log"))
assert len(original) == 39 and len(definitions) == 36
contexts = [("definition",definitions)]
solutions,references = [],[]
for i in range(3):
    sol,ref = index(rows(OUT/f"replay-types_{i}_solution.log")),index(rows(OUT/f"replay-types_{i}_reference.log"))
    assert len(sol) == len(ref) == 37
    contexts.extend([(f"solution_{i}",sol),(f"reference_{i}",ref)])
    solutions.append(sol);references.append(ref)
comparisons = []
for context,rs in contexts:
    for name in definitions:
        a,b = original[name],rs[name]
        comparisons.append({"context":context,"declaration":name,"pass":a["type"] == b["type"] and a["value"] == b["value"] and standard(a) and standard(b)})
check("252_actual_definition_types_and_values_exact_across_seven_contexts",len(comparisons) == 252 and all(r["pass"] for r in comparisons),
    {"actual_Defs":36,"Base":9,"Jet":9,"Injectivity":7,"PF":5,"FiniteSum":4,"HarmonicStability":2,"contexts":7})
target_comparisons = []
for i,short in enumerate(TARGETS):
    name = NS+"."+short
    a,b,c = original[name],solutions[i]["solution"],references[i][name]
    assert a["value"] is b["value"] is c["value"] is None
    assert standard(a) and standard(b) and set(a["axioms"]) == set(b["axioms"]) == STANDARD
    assert set(c["axioms"]) == STANDARD|{"sorryAx"}
    target_comparisons.append({"target":name,"original_type":a["type"],"solution_type":b["type"],"reference_type":c["type"],
        "pass":a["type"] == b["type"] == c["type"],"solution_axioms":b["axioms"],"reference_statement_stub_axioms":c["axioms"],"extra_hypotheses":[]})
check("three_original_Sol_reference_types_equal_no_new_premises",all(r["pass"] for r in target_comparisons),{"target_names":TARGETS,"stubs_are_not_proofs":True})
native = index(rows(OUT/"independent-native-required-proofs.log"))
native_count = 7 + len(mechanical["actual_cross_helpers"])
assert len(native) == native_count and all(standard(r) for r in native.values()) and set(native) == set(replay["native_actual_proof_names"])
proof_comparisons = []
for i in range(3):
    hs = rows(OUT/f"replay-helpers_{i}.log")
    assert len(hs) == native_count + 1
    mapped = {normalize(r["declaration"]):r for r in hs if r["declaration"] != "solution"}
    assert set(mapped) == set(native)
    for name,r in mapped.items():
        proof_comparisons.append({"solution_index":i,"declaration":r["declaration"],"native_declaration":name,
            "pass":normalize(r["type"]) == native[name]["type"] and standard(r) and standard(native[name]),"axioms":r["axioms"]})
    wrapper = next(r for r in hs if r["declaration"] == "solution")
    proof_comparisons.append({"solution_index":i,"declaration":"solution","native_declaration":NS+"."+TARGETS[i],
        "pass":wrapper["type"] == original[NS+"."+TARGETS[i]]["type"] and standard(wrapper),"axioms":wrapper["axioms"]})
check("all_actual_Sol_proof_records_match_native_types_and_standard_axioms",len(proof_comparisons) == 3*(native_count+1) and all(r["pass"] for r in proof_comparisons),
    {"per_Sol":native_count+1,"original_FiniteSum_proofs":7,"actual_cross_helpers":len(mechanical["actual_cross_helpers"]),"wrapper":1,"standard_axioms":sorted(STANDARD)})
for name in ["types_original","types_definition"]+[f"types_{i}_{kind}" for i in range(3) for kind in ["solution","reference"]]+[f"helpers_{i}" for i in range(3)]:
    assert payload(rows(OUT/("replay-"+name+".log"))) == payload(rows(BATCH/(name+".log")))
check("eleven_fresh_actual_type_proof_reports_equal_author_frozen_reports",True,{"equality_fields":["label","type","value","axioms_as_set"]})
boundary = index(rows(OUT/"replay-stage-boundary-audit.log"))
old_boundary = index(load(OLD/"independent-boundary-types.json"))
assert len(boundary) == 44
original_boundary = {name:r for name,r in boundary.items() if normalize(name) in old_boundary}
author_new_boundary = {name:r for name,r in boundary.items() if normalize(name) not in old_boundary}
assert len(original_boundary) == 40 and len(author_new_boundary) == 4 and len([n for n in original_boundary if n.startswith("fs_ind_")]) == 27
boundary_comparisons = []
for name,r in original_boundary.items():
    base = old_boundary[normalize(name)]
    boundary_comparisons.append({"declaration":name,"native_declaration":normalize(name),"type":r["type"],"axioms":r["axioms"],
        "pass":normalize(r["type"]) == base["type"] and r["definitionValue"] == base["definitionValue"] and standard(r) and standard(base)})
assert rows(OUT/"replay-stage-boundary-audit.log") == rows(BATCH/"stage-boundary-audit.log")
check("40_staged_boundary_records_and_27_original_exact_boundaries",all(r["pass"] for r in boundary_comparisons),
    {"source_records":13,"closed_boundary_records":27,"original_math_review_sha256":"a4d2cec35a3e9b506aed7a0df0b2afacce4adf07a5b03f42b713b9726b581386"})
check("four_new_frozen_author_boundaries_fresh_recompiled_standard_axioms",all(standard(r) for r in author_new_boundary.values()),
    {"actual_additional_records":list(author_new_boundary.values()),"original_forty_exact_boundary_records_separate":True})
new_boundary = rows(OUT/"independent-new-boundary.log")
check("nine_new_reviewer_boundaries_proven_with_only_standard_axioms",len(new_boundary) == 9 and all(standard(r) for r in new_boundary),
    {"actual_n0_X4_finite_at_two":"3/2","zero_order_tail":"j","empty_finite_sum":"0 without properness","zero_cutoff_tail":"-B without properness","actual_harmonic_definition":"original finite Icc sum"})
required = ["fs_ind_n_zero_X_four_rho_one","fs_ind_n_zero_X_four_actual_finite","fs_ind_n_zero_X_four_no_simple_cancellation","fs_ind_no_simple_without_cancellation_false","fs_ind_shift_s_zero","fs_ind_shift_T_zero","fs_ind_finite_T_zero"]
check("actual_simple_pole_and_empty_zero_order_boundaries_preserved",all(name in boundary for name in required),{"rho1_must_be_retained_without_cancellation":True,"all_order_harmonic_shift_has_no_new_lower_bound":True})

prints = []
for row in invocations:
    text = (OUT/row["log"]).read_text(encoding="utf-8-sig")
    for name,axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text):
        axset = {a.strip() for a in axs.split(',') if a.strip()}
        assert axset <= STANDARD
        prints.append({"invocation":row["label"],"declaration":name,"axioms":sorted(axset)})
check("all_actual_native_and_Sol_printed_axioms_are_standard",len(prints) >= 15,{"prints":len(prints),"reference_sorry_warnings_separate":True})
root_prints = re.findall(r"info: Solutions/Sol_ZetaNine_CoefficientMapFiniteSum_([^.:]+)\.lean:\d+:\d+: 'solution' depends on axioms: \[([^\]]*)\]",(BATCH/"task-build.log").read_text(encoding="utf-8-sig"))
check("parent_task_build_prints_each_new_FiniteSum_Sol_standard_axioms",len(root_prints) == 3 and {n for n,axs in root_prints} == set(TARGETS) and all({a.strip() for a in axs.split(',')} <= STANDARD for n,axs in root_prints),{"new_solution_prints":3,"older_PNT_stub_boundary_not_reviewed":True})
write(OUT/"independent-type-comparisons.json",{"original_actual_definition_records":[original[n] for n in definitions],"definition_comparisons":comparisons,
    "target_comparisons":target_comparisons,"proof_comparisons":proof_comparisons,"boundary_comparisons":boundary_comparisons,"author_new_boundary_records":list(author_new_boundary.values()),"new_boundary_records":new_boundary,"native_proof_records":list(native.values()),"printed_axioms":prints})
scope = "Actual finite weighted rational/harmonic identities under strict properness; full rho1 term retained; harmonic shift identity for every natural order"
findings = [
    {"severity":"informational","code":"EXACT_FINITE_DOMAINS","detail":"First two public endpoints keep actual ProperMultiplier; the harmonic difference endpoint has no properness or s>=1 premise. All7 original FS proofs remain, and the no-simple/odd helpers keep their explicit cancellation premises."},
    {"severity":"informational","code":"ACTUAL_SIMPLE_BOUNDARY","detail":"n0,X4 has actual rho1=1 and finiteL=H_T1; dropping the simple term is false already at T1. New independent control proves actual finiteL at T2 is3/2. Empty intervals and order0 shifts are verified."},
    {"severity":"informational","code":"STATEMENT_STUBS","detail":"Three reference Theorems use sorryAx only as statement stubs. Complete Sol imports use pure Definitions and Mathlib, with no external theorem placeholder. All actual inline proof and boundary records have only standard axioms."},
    {"severity":"informational","code":"RAW_AND_PARSER_INPUT","detail":"The actual HarmonicStability raw CRLF source hash stays fixed. Its separately executed official Parser.mkInputContext snapshot is exactly the CRLF-to-LF normalized input. No arbitrary mathematical source rewrite or author object borrow occurred."},
    {"severity":"informational","code":"SCOPED_ROOT_BUILD","detail":"Supported parent task build exit0 and root7+5 bytes are hash-bound. Workspace check exit1 names only the two pre-existing Tao files. Older MediumPNT statement mirror is outside this review's new-Sol axiom claim."},
    {"severity":"informational","code":"FINITE_SCOPE","detail":"This three-endpoint batch does not claim infinite convergence, actual rho cancellation without its conditions, aggregate F inverse, integer normalization, J or irrationality. Later native developments remain separate."}]
md = "Independent FS platform integration review: PASS.\n\n"+scope+".\n\n"
md += "40 observed fresh source/extraction/audit Lean exits0, plus a separate runtime probe; five actual sources and the pure Harmonic source, five existing pure Def dependencies, six Stage2/parser snapshots and header, and seven staged modules compile.252 actual Def type/value comparisons, three exact original/Sol/reference types, "+str(3*(native_count+1))+" proof records,44 staged boundary records (40 original exact and4 new author controls) and9 new reviewer controls pass.\n\n"
md += "Simple rho1 is retained, including the actual n0,X4 harmonic boundary. The unrestricted finite harmonic shift keeps s0,T0,j0. Harmonic raw source and official normalized parser snapshot are verified separately. No root/scope/API/credential writes or publication occurred during this review.\n"
(OUT/"independent-integration-review.md").write_text(md,encoding="utf-8")
(OUT/"independent-integration-review.log").write_text("PASS\n"+"\n".join(c["name"]+": PASS" for c in checks)+"\n",encoding="utf-8")
paths = set(TASK/r["task_relative"] for r in load(BATCH/"source-manifest.json")["files"])
paths.update(BATCH/n for n in mechanical["author_frozen_controls"])
paths.update(BATCH/n for n in mechanical["root_evidence_sha256"])
paths.update(ROOT/n for n in mechanical["root_paths"])
paths.update(ROOT/n for n in mechanical["old_frozen_manifests"])
paths.update(TASK/("formalization/"+n+".lean") for n in prep["original_sources_sha256"])
paths.update(OLD/n for n in ["independent-review.json","independent-boundary-types.json","independent-boundary-audit.lean","independent-compile-receipt.json"])
paths.update(ROOT/n for n in ["lake-manifest.json","lean-toolchain"])
paths.update(OUT.rglob("*"))
report_path = OUT/"independent-integration-review.json"
files = []
for p in sorted(paths,key=lambda p:p.as_posix()):
    if not p.is_file() or p == report_path: continue
    assert p.is_relative_to(ROOT)
    files.append({"task_relative":p.relative_to(TASK).as_posix() if p.is_relative_to(TASK) else None,"root_relative":p.relative_to(ROOT).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)})
report = {"schema_version":1,"verdict":"PASS","scope_verdict":"PASS_ACTUAL_FINITE_SUM_PLATFORM_INTEGRATION","review_role":"Independent transplant reviewer; not mathematical or platform batch author",
    "checked_at":datetime.now(timezone.utc).isoformat(),"scope":scope,"source_sha256":prep["original_sources_sha256"]["CoefficientMapFiniteSum"],"sources_sha256":prep["original_sources_sha256"],
    "author_frozen_controls":mechanical["author_frozen_controls"],"environment":{"lean_toolchain":"leanprover/lean4:v4.33.1","mathlib_rev":"0df444a360eaa60ab8c11dca51a86af692955474"},
    "checks":checks,"findings":findings,"compile_counts":{"preparation":11,"replay":29,"total":40,"separate_runtime_probe":1,"all_Lean_invocations":41,"actual_nonzero_final_exits":0},
    "audit_counts":{"graph":len(rows(OUT/"native-decl-graph.jsonl")),"new_Def":4,"all_actual_Def":36,"definition_comparisons":252,"exact_targets":3,"native_required_proofs":native_count,"Sol_proof_records":3*(native_count+1),"staged_boundary_records":44,"exact_original_closed_boundaries":27,"new_author_boundary_records":4,"new_reviewer_boundary_records":9},
    "actual_cross_source_helpers":mechanical["actual_cross_helpers"],"new_external_theorem_boundaries":[],"root_module_bytes_verified":True,"parent_task_build_exit_code":0,"workspace_check_exit_code":1,
    "reviewer_root_scope_API_credentials_writes":False,"platform_published_by_reviewer":False,"platform_acceptance_claimed":False,"failed_attempts_excluded_from_success_evidence":True,"stable_files":files,
    "hash_exclusions":["report self","dynamic scope.json","API receipts","API documentation","credentials"]}
write(report_path,report)
assert all(sha(ROOT/r["root_relative"]) == r["sha256"] and (ROOT/r["root_relative"]).stat().st_size == r["bytes"] for r in files)
print("Independent FiniteSum PASS; "+str(len(checks))+" checks; "+str(len(files))+" bindings")
print("review_sha256="+sha(report_path))
