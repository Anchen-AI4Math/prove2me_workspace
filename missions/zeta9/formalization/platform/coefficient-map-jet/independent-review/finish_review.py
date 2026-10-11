"""Write the hash-bound independent Jet integration gate after actual replay."""
from pathlib import Path
from fractions import Fraction
from math import factorial
import datetime,hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
HERE=Path(__file__).resolve().parent
BATCH=HERE.parent
TASK=BATCH.parents[2]
ROOT=TASK.parents[1]
PROJECT=HERE / "project"
BASE=TASK / "formalization/platform/coefficient-map"
NS="ZetaNine.CoefficientMapJet"
BNS="ZetaNine.CoefficientMap"
STANDARD={"propext","Classical.choice","Quot.sound"}
DEFS=["shiftedVariable","shiftedNumerator","shiftedClearedDenominator","localU","integerLocalU","clearedSeries","weightedClearedSeries","localCoefficient","weightedLocalCoefficient"]
BASEDEFS=["numerator","poleProduct","actualR","clearedPoleProduct","clearedR","leadingPoleCoefficient","weightedR","clearedWeightedR","weightedLeadingPoleCoefficient"]
TARGETS=["clearedSeries_unique","coefficient_convolution_explicit","integer_coefficient_convolution"]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith("{")]
def write(p,s):p.write_text(s,encoding="utf-8",newline="\n")
reconstruction=load(HERE / "reconstruction-report.json")
checks=reconstruction["checks"]
def check(name,okay,evidence=None):
    checks.append({"name":name,"pass":bool(okay),"evidence":evidence})
    assert okay,name
receipt=load(HERE / "compile-receipt.json")
check("independent_26_actual_main_runs_all_exit_zero_and_logs_bound",receipt.get("complete") is True and len(receipt["rows"])==26 and all(r["exit_code"]==0 and sha(HERE / r["log"])==r["log_sha256"] for r in receipt["rows"]),{"actual_runs":26,"fresh_native_sources":2,"fresh_Base_Definition":1,"fresh_Jet_modules":7,"actual_oracles":4,"actual_import_reports":11,"toolchain_probe":1,"native_or_staged_olean_cache_borrowed":False,"pinned_Mathlib_dependency_artifacts_only":True,"maximum_simultaneous_review_Lean_processes":2})
correction=load(HERE / "stage2-prefix-correction-receipt.json")
check("final_full_cross_module_parser_replay_exit_zero_earlier_narrow_filter_preserved",correction["corrected_Lean_exit_code"]==0 and correction["validation_exit_code"]==1 and correction["final_fact_counts"]=={"decl":28,"ref":141,"command":47} and sha(HERE / "sketch_info.jsonl")==correction["final_facts_sha256"] and sha(HERE / "stage2-extract-corrected.log")==correction["corrected_log_sha256"] and sha(HERE / "sketch_info.jsonl.before-namespace-filter-fix")==correction["initial_fact_sha256"],correction)
env=os.environ.copy();env.pop("LEAN_PATH",None)
revision=subprocess.run(["git","-C",str(ROOT / ".lake/packages/mathlib"),"rev-parse","HEAD"],capture_output=True,env=env)
(HERE / "mathlib-revision.log").write_bytes(revision.stdout+revision.stderr)
check("actual_Lean_4_33_1_and_local_pinned_Mathlib_verified","version 4.33.1" in (HERE / "toolchain.log").read_text(encoding="utf-8-sig") and revision.returncode==0 and revision.stdout.decode().strip()=="0df444a360eaa60ab8c11dca51a86af692955474")
original={r["label"]:r for r in rows(HERE / "types_original.log")}
labels=["types_definition"]+[f"types_{i}_{kind}" for i in range(3) for kind in ["solution","reference"]]
reports={label:{r["label"]:r for r in rows(HERE / (label+".log"))} for label in labels}
comparisons=[]
for full in [BNS+"."+n for n in BASEDEFS]+[NS+"."+n for n in DEFS]:
    baseline=original[full]
    assert baseline["value"] is not None
    for label,rs in reports.items():
        got=rs[full]
        comparisons.append({"declaration":full,"context":label,"type_equal":got["type"]==baseline["type"],"value_equal":got["value"]==baseline["value"],"axioms":got["axioms"]})
check("nine_Jet_plus_nine_Base_actual_Def_types_values_match_in_all_imports",len(comparisons)==126 and all(r["type_equal"] and r["value_equal"] and set(r["axioms"])<=STANDARD for r in comparisons),{"original_actual_definitions":18,"comparison_contexts":7,"exact_full_name_type_value_comparisons":126})
target_evidence=[]
for i,n in enumerate(TARGETS):
    full=NS+"."+n
    orig=original[full];sol=reports[f"types_{i}_solution"][full];ref=reports[f"types_{i}_reference"][full]
    target_evidence.append({"theorem":full,"actual_original_type":orig["type"],"original_solution_reference_type_equal":orig["type"]==sol["type"]==ref["type"],"original_axioms":orig["axioms"],"solution_axioms":sol["axioms"],"reference_axioms":ref["axioms"]})
check("three_original_solution_reference_statements_equal_without_extra_hypotheses",all(t["original_solution_reference_type_equal"] for t in target_evidence),target_evidence)
check("three_complete_solution_proofs_exactly_standard_three_axioms",all(set(t["solution_axioms"])==STANDARD and set(t["original_axioms"])==STANDARD for t in target_evidence),{"axioms":sorted(STANDARD)})
helpers=[rows(HERE / f"helpers_{i}.log") for i in range(3)]
check("each_Solution_all_nineteen_Jet_proofs_Base_nonzero_and_wrapper_no_extra_axioms",all(len(rs)==21 and all(set(r["axioms"])<=STANDARD for r in rs) for rs in helpers),{"actual_proof_records":63,"per_context":"19 original Jet proofs, the genuine Base clearedPoleProduct_ne_zero proof, one solution wrapper"})
check("reference_stubs_intentionally_sorryAx_Solutions_no_theorem_or_mission_import",all("sorryAx" in t["reference_axioms"] for t in target_evidence) and all(not any(line.startswith(("import Theorems.","import Solutions.","import missions.")) for line in (BATCH / "staged" / ("Solutions/Sol_ZetaNine_CoefficientMapJet_"+n+".lean")).read_text(encoding="utf-8").splitlines()) for n in TARGETS))
for label in ["types_original"]+labels:
    actual=rows(HERE / (label+".log"))
    author=rows(BATCH / (label.replace("_","-")+".log"))
    canonical=lambda rs:sorted(json.dumps({**r,"axioms":sorted(r["axioms"])},sort_keys=True,ensure_ascii=False) for r in rs)
    check(label+"_author_PP_type_value_report_independently_recomputed",canonical(actual)==canonical(author))

# A mathematical exact rational check from the actual product definitions,
# deliberately distinguished from an additional Lean theorem.
def mul(a,b):return [a[0]*b[0],a[0]*b[1]+a[1]*b[0]]
n,j=2,0
numerator=[Fraction(factorial(n)**7),Fraction(0)]
for i in range(1,n+1):numerator=mul(numerator,[Fraction(-j-i),Fraction(1)])
for i in range(1,n+1):numerator=mul(numerator,[Fraction(-j+n+i),Fraction(1)])
denominator=[Fraction(1),Fraction(0)]
for k in range(n+1):
    if k!=j:denominator=mul(denominator,[Fraction(-j+k),Fraction(1)])
denominator9=[Fraction(1),Fraction(0)]
for _ in range(9):denominator9=mul(denominator9,denominator)
c0=numerator[0]/denominator9[0]
c1=(numerator[1]-denominator9[1]*c0)/denominator9[0]
arithmetic={"n":n,"j":j,"s":8,"integer_W":"1","actual_N_constant_and_linear":list(map(str,numerator)),"actual_D_constant_and_linear":list(map(str,denominator)),"actual_D9_constant_and_linear":list(map(str,denominator9)),"clearedSeries_coeff_zero":str(c0),"localCoefficient_2_0_8":str(c1),"integer":c1.denominator==1,"identity":"512*c1+6912*6=-2816","source_of_series_identity":"genuine transplanted clearedSeries_denominator_identity, independently imported and standard-axiom checked","check_kind":"mathematical exact rational product/quotient recurrence; not an additional Lean theorem"}
write(HERE / "rational-lower-coefficient-check.json",json.dumps(arithmetic,ensure_ascii=False,indent=2)+"\n")
native_review=load(TASK / "verification/formalization-coefficient-map-jet-2026-10-03/independent-review.json")
check("integer_W_does_not_force_integral_c_actual_product_recurrence_recomputed",numerator==[3072,-2816] and denominator==[2,3] and denominator9==[512,6912] and c0==6 and c1==Fraction(-173,2) and native_review["rational_lower_coefficient_example"]["local_coefficient"]==str(c1),arithmetic)
definition_request=load(BATCH / "definitions-request.json")[0]
problem_request=load(BATCH / "problems-request.json")
definition_fields={"definition_name","definition_title","definition","natural_language_statement","source","tags","env","private"}
problem_fields={"theorem_name","theorem_title","formal_statement","natural_language_statement","preamble","source","tags"}
check("offline_definition_and_problem_payloads_only_documented_fields",set(definition_request)<=definition_fields and {"definition_name","definition_title","definition"}<=set(definition_request) and set(problem_request)=={"env","private","problems"} and all(set(p)<=problem_fields and {"theorem_name","theorem_title","formal_statement","natural_language_statement"}<=set(p) and p["formal_statement"].endswith(":= by sorry") and len(p["theorem_title"])<=200 for p in problem_request["problems"]),{"local_schema":"formalization/platform/readback-2026-10-03/api-docs/references/contribute.md","definition_list_is_one_offline_request_record":True,"API_accessed":False})
check("public_prose_faithful_unique_all_j_convolution_bounds_formal_only_integer_multiplier_scope","any natural numbers" in problem_request["problems"][0]["natural_language_statement"] and "analytic convergence" in problem_request["problems"][0]["natural_language_statement"] and "including zero" in problem_request["problems"][1]["natural_language_statement"] and "need not be integers" in problem_request["problems"][2]["natural_language_statement"] and "integer quartic" in problem_request["problems"][2]["natural_language_statement"])
plan=load(BATCH / "root-copy-plan.json")
installed=[]
for f in plan["files"]:
    p=ROOT / f["root_relative_destination"]
    installed.append({"path":f["root_relative_destination"],"exists":p.exists(),"bytes":p.stat().st_size if p.exists() else None,"sha256":sha(p) if p.exists() else None,"expected":f["sha256"]})
base_required=plan["required_existing_Base_definition"]
check("seven_installed_Jet_root_files_and_required_Base_Def_exact_frozen_bytes",all(f["exists"] and f["sha256"]==f["expected"] for f in installed) and sha(ROOT / base_required["root_relative"])==base_required["sha256"],{"installed_Jet_files":installed,"required_Base_Def":base_required})
check("parent_scoped_build_observed_exit_zero_and_source_install_receipt_present",(BATCH / "task-build-exit.txt").read_text().strip()=="0" and (BATCH / "task-build.log").exists() and (BATCH / "root-install-receipt.json").exists(),{"root_build_is_parent_observed_separate_integration_check":True})
hashes={}
for line in (BATCH / "SHA256SUMS.txt").read_text(encoding="utf-8-sig").splitlines():
    h,rel=line.split("  ",1);p=(BATCH / rel).resolve();assert p.is_relative_to(TASK) and sha(p)==h
    hashes[p.relative_to(TASK).as_posix()]=h
check("111_author_freeze_hashes_unchanged_after_all_independent_runs",len(reconstruction["frozen_manifest_members"])==111 and sha(BATCH / "author-audit.json")=="a2b03ceb4e2ac3d2c4bc062f32cd8dcbac73b68bc0799802e886365eed6f3345")
dependencies=[TASK / "formalization/CoefficientMap.lean",TASK / "formalization/CoefficientMapJet.lean",BATCH / "SHA256SUMS.txt",BATCH / "root-copy-plan.json",BASE / "oracle-input.lean",BASE / "sketch_info.jsonl",BASE / "decl_graph.jsonl",BASE / "author-audit.json",BASE / "staged" / base_required["root_relative"],TASK / "verification/formalization-coefficient-map-jet-2026-10-03/independent-review.json",TASK / "formalization/platform/readback-2026-10-03/api-docs/references/contribute.md",BATCH / "task-build.log",BATCH / "task-build-exit.txt",BATCH / "root-install-receipt.json"]
for p in dependencies:hashes[p.relative_to(TASK).as_posix()]=sha(p)
for f in installed:hashes[f["path"]]=f["sha256"]
hashes[base_required["root_relative"]]=sha(ROOT / base_required["root_relative"])
for p in HERE.iterdir():
    if p.is_file():hashes[p.relative_to(TASK).as_posix()]=sha(p)
for p in list(PROJECT.glob("*.lean"))+[PROJECT / "lake-manifest.json",PROJECT / "lean-toolchain",PROJECT / base_required["root_relative"]]+[PROJECT / f["root_relative_destination"] for f in plan["files"]]+[PROJECT / ("missions/zeta9/formalization/"+n+".lean") for n in ["CoefficientMap","CoefficientMapJet"]]:
    hashes[p.relative_to(TASK).as_posix()]=sha(p)
limits=[
    "These are actual formal Q[[z]] coefficients of the genuine shifted-product quotient. No coefficient array, closed formula, or target endpoint is introduced as an assumed premise. The nonzero constant denominator and actual inverse laws justify existence and uniqueness; all natural n,j are allowed for the uniqueness statement.",
    "The explicit rational/integer convolution needs j<=n and 1<=s<=9 exactly as in the frozen original statement. W is arbitrary and may be zero or cancel local coefficients. Natural 9-s outside that order range is only the total definition convention, not an additional pole-order theorem.",
    "For W in Z[X], only the coefficients of W.comp(integerLocalU) are integers. The genuine local c values remain rational: n=2,j=0,s=8,W=1 yields -173/2 by exact quotient recurrence. This reported example is a mathematical arithmetic check, not an extra Lean theorem.",
    "The formal series is not numerically evaluated at z. No analytic convergence, infinite-series summation, full LaurentSeries/RatFunc embedding, global partial-fraction result or degree/growth condition is established by this batch. Separate later task files are not part of its imports or proof closure.",
    "The original five-dimensional aggregate F map, its inverse/invertibility, exact infinite L identities, J certificate and zeta(9) irrationality remain outside this result. All three Solution proofs are complete standard-axiom proofs; their reference theorem files intentionally contain sorryAx and are never imported by Solutions.",
    "This is an offline source-integration review. Parent installation and scoped build are hash-bound separately, but no platform publication or acceptance is claimed. Author's two early failed attempts and the review's initial narrow-prefix mismatch are preserved with actual logs and exits."
]
author=load(BATCH / "author-audit.json")
result={"schema_version":1,"review_role":"independent offline Jet source integration review","reviewed_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"verdict":"PASS" if all(c["pass"] for c in checks) else "FAIL","checks":checks,"sha256":dict(sorted(hashes.items())),"findings":[],"targets":target_evidence,"definition_comparisons":comparisons,"cross_module_proof_closure":reconstruction["cross_module_core_closure"],"actual_Base_inline_helper":reconstruction["Base_helpers"],"source_position_counts":{"Stage1_environment":65,"Base_source":27,"Base_generated":1,"Jet_source":28,"Jet_defs":9,"Jet_proofs":19,"Jet_generated":9,"Jet_Stage2_decl":28,"Jet_Stage2_ref":141,"Jet_Stage2_command":47,"deleted_print_diagnostics":10},"actual_header_span":reconstruction["header"],"fresh_compile":{"main_observed_successful_runs":26,"corrected_cross_module_parser_observed_exit":0,"fresh_native_sources":2,"fresh_Definitions":2,"fresh_Solutions":3,"fresh_statement_references":3,"type_value_reports":8,"all_proof_helper_reports":3,"proof_records":63,"no_native_or_staged_olean_borrowing":True},"author_retained_failed_attempts":author["retained_failed_attempts"],"independent_parser_filter_correction":correction,"actual_rational_lower_coefficient_example":arithmetic,"installed_root":installed,"required_Base_Definition":base_required,"limitations":limits,"reviewer_root_writes":False,"reviewer_scope_writes":False,"reviewer_frozen_math_source_writes":False,"reviewer_API_calls":False,"credentials_read":False,"platform_publication_claimed":False,"platform_acceptance_claimed":False}
report=BATCH / "independent-integration-review.json"
write(report,json.dumps(result,ensure_ascii=False,indent=2)+"\n")
summary="""# Independent CoefficientMapJet integration review

PASS. Independently replayed actual cross-module declaration, Jet/Base parser/reference and header oracles reconstruct all seven staged modules exactly. Stage1 has 65 environment records: 27 Base source declarations and one generated helper, plus 28 Jet source declarations and nine generated helpers. Jet Stage2 gives 28 declarations, 141 references and 47 commands. Only nine actual Jet definition spans, ten diagnostic spans and the original header are removed; the selected theorem binding and actual references are renamed. Every Solution retains all 19 Jet proofs and the exact genuine Base clearedPoleProduct_ne_zero proof selected from the true cross-module closure. Mathlib.Tactic explicitly restores the original native Base import's transitive tactic dependency. There is no Theorems/Solutions/mission proof boundary.

A new isolated project freshly compiled both exact original sources, both real Definitions, all three complete Solutions and all three statement references. Eight actual type/value imports and three all-helper imports exited zero. All 18 genuine definition types and values match across original, Definition and all Solution/reference contexts (126 comparisons); three root types match exactly without extra hypotheses. The complete Solutions have exactly propext, Classical.choice and Quot.sound. All 63 helper/wrapper records have only standard axioms. Statement references intentionally have sorryAx and are not imported by a Solution. No original/staged olean was borrowed; only the pinned Mathlib dependency cache was reused. Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 were checked.

The quotient and convolution are in formal Q[[z]], without analytic convergence or numerical series evaluation. Integer W gives integer multiplier coefficients, not integral actual local coefficients: at n=2,j=0,s=8,W=1 the exact actual-product quotient recurrence gives -173/2. That counterexample is an exact mathematical arithmetic check, not an additional Lean theorem. W may vanish or cancel. This batch does not establish full Laurent/RatFunc embedding, global partial fractions, the original five-dimensional aggregate F/inverse/invertibility, exact infinite L, J or irrationality.

All 111 author-frozen hashes remain intact, including both early author failures. The independent first parser run used too narrow a namespace filter and omitted eleven Base references; the mismatch and first facts are preserved, and the full ZetaNine filter was re-executed with exit zero and exact fact equality. All native/staged builds succeeded. The machine-readable report binds source/request/staged/oracle/compile evidence plus the parent's seven installed Jet files, required actual Base Definition and successful root scoped-build receipt. Reviewer writes stay in this task's new review files; frozen source, author evidence, root and scope were not changed. No API or credentials were accessed and no platform acceptance is asserted.

Machine-readable result: independent-integration-review.json. Detailed replay receipt, byte-span reconstruction and exact type/helper reports: independent-review/. Own checksum sidecar: independent-integration-review-SHA256SUMS.txt.
"""
write(BATCH / "independent-integration-review.md",summary)
sidecar=[report,BATCH / "independent-integration-review.md"]+[p for p in HERE.iterdir() if p.is_file()]
write(BATCH / "independent-integration-review-SHA256SUMS.txt","".join(sha(p)+"  "+p.relative_to(TASK).as_posix()+"\n" for p in sorted(sidecar)))
print(json.dumps({"verdict":result["verdict"],"checks":len(checks),"hash_bindings":len(hashes),"review_sha256":sha(report),"report_bytes":report.stat().st_size,"installed_Jet":len(installed),"actual_solution_axioms":sorted(STANDARD)},ensure_ascii=False),flush=True)
