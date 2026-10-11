"""Independent closed type/value/proof, boundary and final evidence audit."""
from pathlib import Path
import hashlib
import json
import re
from datetime import datetime, timezone

OUT = Path(__file__).resolve().parent
BATCH = OUT.parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
NS = "ZetaNine.CoefficientMapPartialFractions"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = ["candidate_local_coefficients", "actual_global_polynomial_partial_fractions", "actual_global_partial_fractions"]
OLD = TASK / "verification/formalization-coefficient-map-partial-fractions-2026-10-03"

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p): return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(p,obj): p.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n",encoding="utf-8")
def index(rs):
    result = {r["declaration"]:r for r in rs}
    assert len(result) == len(rs)
    return result
def standard(r): return set(r["axioms"]) <= STANDARD
def normalize(t):
    for short in TARGETS: t=t.replace(NS + ".checked_" + short, NS + "." + short)
    return t
def payload(rs):
    return {r["label"]: {"type":r["type"], "value":r["value"], "axioms": sorted(r["axioms"])} for r in rs}
def value(r):return r.get("value",r.get("definitionValue"))
mechanical = load(OUT / "mechanical-checks.json")
checks = list(mechanical["checks"])
def check(name,passed,detail):
    checks.append({"name":name,"pass":bool(passed),"detail":detail})
    assert passed,name

# Every invocation has an observed exit and its immutable inputs/outputs bound.
prep = load(OUT / "prepare-compile-receipt.json")
replay = load(OUT / "replay-compile-receipt.json")
native_receipt = load(OUT / "native-helper-compile-receipt.json")
invocations = prep["rows"] + replay["rows"] + [native_receipt]
for r in invocations:
    assert r["exit_code"] == int((OUT/r["exit_file"]).read_text().strip()) == 0
    assert sha(ROOT/r["source_root_relative"]) == r["source_sha256"]
    for field in ["log","exit_file","wrapper","output","stdout_copy"]:
        if r.get(field): assert sha(OUT/r[field]) == r["stdout_sha256" if field=="stdout_copy" else field+"_sha256"]
    wrapper=(OUT/r["wrapper"]).read_text(encoding="utf-8")
    assert str((OUT / "cache").as_posix()) in wrapper
    assert str((BATCH / "build").as_posix()) not in wrapper
check("33_fresh_independent_Lean_invocations_observed_exit_zero",len(prep["rows"])==7 and len(replay["rows"])==25 and
      replay["complete"] and len(invocations)==33,
      {"preparation":7,"final_replay":25,"native_helper_report":1,"author_caches_used":False,
       "native_and_pure_platform_namespaces_use_separate_new_cache_trees":True})

original = index(rows(OUT/"replay-types_original.log"))
definitions = index(rows(OUT/"replay-types_definition.log"))
assert len(original)==33 and len(definitions)==30
contexts=[("definition",definitions)]
solutions=[]
references=[]
for i in range(3):
    sol=index(rows(OUT/f"replay-types_{i}_solution.log"))
    ref=index(rows(OUT/f"replay-types_{i}_reference.log"))
    assert len(sol)==len(ref)==31
    contexts += [(f"solution_{i}",sol),(f"reference_{i}",ref)]
    solutions.append(sol);references.append(ref)
comparisons=[]
for context,rs in contexts:
    for name in definitions:
        base,r=original[name],rs[name]
        equal=base["type"]==r["type"] and base["value"]==r["value"] and standard(base) and standard(r)
        comparisons.append({"context":context,"declaration":name,"pass":equal})
check("210_exact_actual_definition_type_and_value_comparisons",len(comparisons)==210 and all(r["pass"] for r in comparisons),
      {"actual_definitions":30,"contexts":7,"Base":9,"Jet":9,"Injectivity":7,"PF":5,
       "definition_values_are_actual_constructions_not_closed_formula_replacements":True})
target_comparisons=[]
for i,short in enumerate(TARGETS):
    name=NS+"."+short
    orig,sol,ref=original[name],solutions[i]["solution"],references[i][name]
    assert orig["value"] is sol["value"] is ref["value"] is None
    assert standard(orig) and standard(sol)
    assert set(ref["axioms"])==STANDARD|{"sorryAx"}
    target_comparisons.append({"target":name,"original_type":orig["type"],"solution_type":sol["type"],
        "reference_type":ref["type"],"pass":orig["type"]==sol["type"]==ref["type"],
        "solution_axioms":sol["axioms"],"reference_statement_stub_axioms":ref["axioms"],"extra_hypotheses":[]})
check("three_exact_original_solution_reference_types_no_added_hypothesis",all(r["pass"] for r in target_comparisons),
      {"targets":TARGETS,"stub_sorryAx_is_not_used_as_proof":True,"original_types_recorded_in_independent_type_comparisons":True})

native = index(rows(OUT/"types_native_helpers.log"))
assert len(native)==42 and set(native)==set(native_receipt["actual_graph_proof_names"])
proof_comparisons=[]
for i in range(3):
    hs=rows(OUT/f"replay-helpers_{i}.log")
    assert len(hs)==43
    mapped={normalize(r["declaration"]):r for r in hs if r["declaration"]!="solution"}
    assert set(mapped)==set(native)
    for name,r in mapped.items():
        base=native[name]
        proof_comparisons.append({"solution_index":i,"declaration":r["declaration"],"native_declaration":name,
            "pass":normalize(r["type"])==base["type"] and standard(r) and standard(base),"axioms":r["axioms"]})
    wrapper=next(r for r in hs if r["declaration"]=="solution")
    proof_comparisons.append({"solution_index":i,"declaration":"solution","native_declaration":NS+"."+TARGETS[i],
        "pass":wrapper["type"]==original[NS+"."+TARGETS[i]]["type"] and standard(wrapper),"axioms":wrapper["axioms"]})
check("129_real_inline_proof_records_exact_native_types_and_only_standard_axioms",len(proof_comparisons)==129 and
      all(r["pass"] for r in proof_comparisons),
      {"per_Sol":43,"native_source_proofs":27,"actual_cross_source_helpers":15,"final_solution_wrapper":1,
       "new_external_theorem_boundaries":[],"allowed_axioms":sorted(STANDARD)})

for name in ["types_original","types_definition"]+[f"types_{i}_{kind}" for i in range(3) for kind in ["solution","reference"]]+[f"helpers_{i}" for i in range(3)]:
    assert payload(rows(OUT/("replay-"+name+".log"))) == payload(rows(BATCH/(name+".log")))
check("all_11_fresh_import_type_proof_reports_equal_frozen_author_reports",True,
      {"compared_fields":["label","type","value","axioms_as_set"],"reviewer_reports_generated_using_reviewer_cache":True})

boundary=index(rows(OUT/"replay-stage-boundary-audit.log"))
old_boundary=index(load(OLD/"independent-boundary-types.json"))
closed=[n for n in boundary if n.startswith("pf_ind_")]
assert len(boundary)==51 and len(closed)==19
boundary_comparisons=[]
for name in closed:
    r,base=boundary[name],old_boundary[name]
    boundary_comparisons.append({"declaration":name,"type":r["type"],"axioms":r["axioms"],
        "pass":r["type"]==base["type"] and standard(r) and standard(base)})
assert all(standard(r) for r in boundary.values())
assert rows(OUT/"replay-stage-boundary-audit.log") == rows(BATCH/"stage-boundary-audit.log")
check("51_fresh_staged_boundary_records_and_19_original_exact_closed_statements",all(r["pass"] for r in boundary_comparisons),
      {"original_independent_math_review_sha256":"df4d12de4529335fca0070e5d71294f396d8a00ef3fc9045cc74188f187ecea9",
       "source_records":32,"closed_boundary_records":19,"original_boundary_statement_types_exact":True,
       "proof_scripts_adapted_to_staged_public_Defs_and_checked_global_proof_without_new_assumptions":True})
assert sha(OLD/"independent-review.json")=="df4d12de4529335fca0070e5d71294f396d8a00ef3fc9045cc74188f187ecea9"
required=["pf_ind_n_zero_X_four_proper","pf_ind_n_zero_X_four_simple_coefficient","pf_ind_n_zero_X_four_actual_simple_pole",
          "pf_ind_n_zero_X_four_not_two_degree_gap","pf_ind_n_zero_total_simple_coefficient",
          "pf_ind_n_zero_X_five_coefficients_zero","pf_ind_n_zero_X_five_not_proper",
          "pf_ind_n_zero_nonproper_polynomial_failure","pf_ind_n_zero_nonproper_regular_point_failure"]
check("strict_proper_1_over_t_and_nonproper_X5_boundaries_preserved",all(n in boundary for n in required),
      {"n0_X4":"Proper; actualR(t)=1/t at nonzero t; actual simple coefficient and total simple coefficient1; not two-degree gap",
       "n0_X5":"Not Proper; all actual nine jet coefficients zero, candidate numerator0, actual weighted numerator nonzero; actualR(1)=1 while candidate sum0",
       "inferences_not_made":["rho1=0 from strict properness","L convergence from strict properness","global identity without Proper"]})

prints=[]
for r in invocations:
    text=(OUT/r["log"]).read_text(encoding="utf-8-sig")
    for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text):
        aa={a.strip() for a in axioms.split(',') if a.strip()}
        assert aa<=STANDARD
        prints.append({"invocation":r["label"],"declaration":name,"axioms":sorted(aa)})
check("all_actual_native_and_solution_print_axioms_are_standard",len(prints)>=15,
      {"prints":len(prints),"statement_reference_sorry_warnings_separate":True})
root_prints=re.findall(r"info: Solutions/Sol_ZetaNine_CoefficientMapPartialFractions_([^.:]+)\.lean:\d+:\d+: 'solution' depends on axioms: \[([^\]]*)\]",(BATCH/"task-build.log").read_text(encoding="utf-8-sig"))
assert len(root_prints)==3 and {name for name,aa in root_prints}==set(TARGETS) and all({a.strip() for a in aa.split(',')}<=STANDARD for name,aa in root_prints)
check("installed_task_build_prints_each_new_solution_standard_axioms",True,{"solution_prints":len(root_prints)})

# Final evidence artifact contains the actual expanded original types and values.
write(OUT/"independent-type-comparisons.json",{"actual_original_definition_records":[original[n] for n in definitions],
    "definition_comparisons":comparisons,"target_comparisons":target_comparisons,"proof_comparisons":proof_comparisons,
    "boundary_comparisons":boundary_comparisons,"native_proof_records":list(native.values()),"printed_axioms":prints})
findings=[
 {"severity":"information","code":"FINITE_PF_DOMAIN", "detail":"PASS covers actual finite global PF with strict properness and rational regular points. Strict properness permits1/t; no rho1 cancellation, infinite L, prescribed target, five-dimensional aggregate F or inverse conclusion is inferred."},
 {"severity":"information","code":"STATEMENT_STUBS", "detail":"The three Theorems files deliberately contain sorryAx as platform statement stubs; no Sol imports those files. All129 actual Sol proofs and all51 staged boundary records have only standard axioms."},
 {"severity":"information","code":"FROZEN_MEMBER_COUNTS", "detail":"source-manifest lists172 immutable members; SHA256SUMS lists174 = those172 plus author-audit.json and source-manifest.json. All hashes and sizes match."},
 {"severity":"information","code":"PREEXISTING_SCOPE_CHECK", "detail":"Supported task build completed exit0. Workspace check exit1 identifies only the two pre-existing TaoFivePrimes unassigned solutions; all three new PF Solutions are owned by zeta9."},
 {"severity":"information","code":"SCOPED_AXIOM_CLAIM", "detail":"The shared task log also prints four older PNT platform solutions with sorryAx from their explicit MediumPNT statement boundary. This review verifies only the three new PF solutions as standard3, and does not claim every older task proof is axiom-free."},
 {"severity":"information","code":"RETAINED_FAILED_ATTEMPTS", "detail":"Author's first namespace-context wrapper failure remains frozen and excluded from success evidence. Reviewer Python initially assumed174 manifest members and resolved old README paths against task root; corrected only own checks to172 and batch-relative paths. Finalizer's receipt key and overly broad shared-build print selector were corrected locally. No source/Lean proof failure occurred in the33 final fresh independent invocations."}]
scope="Actual global finite partial fractions with real jet coefficients, strict properness and regular rational points only"
md="Independent PF platform integration review: PASS.\n\n"+scope+".\n\n"
md+="Fresh independent evidence:33 observed Lean exits0; actual133 Stage1 records and all four Stage2/header snapshots match; seven staged modules compile;210 actual definition type/value comparisons, three exact original/Sol/reference types,129 proof records and51 boundary records pass. Root7 modules and3 required Definitions match frozen stage; the supported parent task build completes exit0.\n\n"
md+="Theorem files are deliberate statement stubs. Sol proofs import pure Definitions and Mathlib, and use only propext, Classical.choice and Quot.sound. Strict properness admits the n0X4 simple pole1/t; n0X5 remains excluded and demonstrates failure of a global identity without properness. This audit makes no infinite-sum, rho1-zero, aggregate F, inverse or prescribed-target claim.\n\n"
md+="All172 manifest members and174 SHA256SUMS entries match. Workspace check's two errors are pre-existing Tao entries. Retained author namespace trial and corrected reviewer metadata/path assertions are separated from successful evidence. No root/scope/API/credential writes were performed by the reviewer.\n"
(OUT/"independent-integration-review.md").write_text(md,encoding="utf-8")
(OUT/"independent-integration-review.log").write_text("PASS\n"+"\n".join(r["name"]+": PASS" for r in checks)+"\n",encoding="utf-8")

paths=set()
manifest=load(BATCH/"source-manifest.json")
paths.update(TASK/r["task_relative"] for r in manifest["files"])
paths.update(BATCH/n for n in mechanical["author_frozen_controls"])
paths.update(BATCH/n for n in mechanical["root_evidence_sha256"])
paths.update(ROOT/n for n in mechanical["root_paths"])
paths.update(ROOT/n for n in mechanical["old_frozen_manifests"])
paths.update(OLD/n for n in ["independent-review.json","independent-boundary-types.json","independent-boundary-audit.lean","independent-compile-receipt.json"])
paths.update(OUT.rglob("*"))
report_path=OUT/"independent-integration-review.json"
files=[]
for p in sorted(paths,key=lambda p:p.as_posix()):
    if not p.is_file() or p==report_path:continue
    assert p.is_relative_to(ROOT)
    files.append({"task_relative":p.relative_to(TASK).as_posix() if p.is_relative_to(TASK) else None,
        "root_relative":p.relative_to(ROOT).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)})
report={"schema_version":1,"verdict":"PASS","scope_verdict":"PASS_ACTUAL_FINITE_GLOBAL_PF_PLATFORM_INTEGRATION",
    "review_role":"Independent transplant reviewer; not batch author", "checked_at":datetime.now(timezone.utc).isoformat(),
    "scope":scope,"source_sha256":prep["original_sources_sha256"]["CoefficientMapPartialFractions"],
    "sources_sha256":prep["original_sources_sha256"],"author_frozen_controls":mechanical["author_frozen_controls"],
    "environment":{"lean_toolchain":"leanprover/lean4:v4.33.1","mathlib_rev":"0df444a360eaa60ab8c11dca51a86af692955474"},
    "checks":checks,"findings":findings,"compile_counts":{"preparation":7,"replay":25,"native_helper_report":1,"total":33,"actual_nonzero_final_exits":0},
    "audit_counts":{"graph":133,"new_Def":5,"all_actual_Def":30,"definition_comparisons":210,"exact_targets":3,
        "native_required_proofs":42,"Sol_proof_records":129,"staged_boundary_records":51,"exact_original_closed_boundaries":19},
    "actual_cross_source_helpers":mechanical["actual_cross_helpers"],"new_external_theorem_boundaries":[],
    "root_module_bytes_verified":True,"parent_task_build_exit_code":0,"workspace_check_exit_code":1,
    "reviewer_root_scope_API_credentials_writes":False,"platform_published_by_reviewer":False,"platform_acceptance_claimed":False,
    "failed_attempts_excluded_from_success_evidence":True,"stable_files":files,
    "hash_exclusions":["this report self","dynamic scope.json","API receipts","API documentation","credentials"]}
write(report_path,report)
assert all(sha(ROOT/r["root_relative"])==r["sha256"] and (ROOT/r["root_relative"]).stat().st_size==r["bytes"] for r in files)
print("Independent integration PASS; "+str(len(checks))+" checks; "+str(len(files))+" bindings")
print("review_sha256="+sha(report_path))
