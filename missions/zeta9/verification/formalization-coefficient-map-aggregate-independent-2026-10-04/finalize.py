"""Independent Aggregate mathematics gate and stable evidence report."""
from pathlib import Path
import hashlib,json,re
from datetime import datetime,timezone
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parents[1]
AUTHOR=TASK/"verification/formalization-coefficient-map-aggregate-2026-10-04"
PRIOR=TASK/"verification/formalization-coefficient-map-summation-independent-2026-10-04"
STANDARD={"propext","Classical.choice","Quot.sound"}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def rows(p):return [json.loads(s) for s in p.read_text(encoding="utf-8-sig").splitlines() if s.startswith('{')]
def write(p,o):p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
checks=[]
def check(n,p,d):checks.append({"name":n,"pass":bool(p),"detail":d});assert p,n
receipt=load(OUT/"independent-compile-receipt.json");controls=receipt["fixed_controls"]
manifest=[s.split('  ',1) for s in (AUTHOR/"SHA256SUMS.txt").read_text(encoding="utf-8").splitlines() if s.strip()]
check("author_35_frozen_members_and_fixed_controls_unchanged",len(manifest)==35 and all(sha(TASK/n)==h for h,n in manifest) and
 sha(AUTHOR/"compile-receipt.json")==controls['receipt'] and sha(AUTHOR/"SHA256SUMS.txt")==controls['manifest'] and
 sha(TASK/"formalization/CoefficientMapAggregate.lean")==controls['source'],controls)
reuse=load(OUT/"dependency-reuse.json")
check("explicit_prior_independent_Summation_report_and_receipt_reuse",sha(PRIOR/"independent-review.json")==controls['prior_review'] and
 sha(PRIOR/"independent-compile-receipt.json")==controls['prior_receipt'] and not reuse['author_cache_used'] and not reuse['native_root_cache_used'],
 {"seven_actual_native_dependencies":7,"pure_Definitions":1,"not_rebuilt_this_review":True,"prior_review_sha256":controls['prior_review']})
paths={TASK/n for h,n in manifest}|{AUTHOR/"SHA256SUMS.txt",PRIOR/"independent-review.json",PRIOR/"independent-compile-receipt.json"}
for r in reuse['native_dependency_rows']:
 assert r['exit_code']==int((PRIOR/r['exit_file']).read_text().strip())==0
 assert sha(ROOT/r['source_root_relative'])==r['source_sha256'];paths.add(ROOT/r['source_root_relative'])
 for f in ['log','exit_file','wrapper','output']:
  assert sha(PRIOR/r[f])==r[f+'_sha256'];paths.add(PRIOR/r[f])
for r in reuse['byte_identical_cache_copies']:
 assert sha(TASK/r['independent_task_relative'])==sha(TASK/r['prior_task_relative'])==r['sha256']
check("all_eight_reused_source_object_actual_zero_receipts_and_byte_identical_new_cache_copies",len(reuse['native_dependency_rows'])==8 and
 len(reuse['byte_identical_cache_copies'])==8,{"prior_cache_owner":"this independent reviewer","author_objects_never_on_selected_native_import_path":True})
for r in receipt['rows']:
 assert r['exit_code']==int((OUT/r['exit_file']).read_text().strip())==0
 assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 for f in ['log','exit_file','wrapper','output']:
  if r[f]:assert sha(OUT/r[f])==r[f+'_sha256']
check("three_new_actual_Lean_calls_all_exit_zero",len(receipt['rows'])==3,
 {"fresh_Aggregate_source":1,"fresh_author_type_replay":1,"independent_boundaries":1,"actual_exits":[r['exit_code'] for r in receipt['rows']]})
author=rows(OUT/"author-type-replay.log");original=load(AUTHOR/"type-report.json");boundaries=rows(OUT/"independent-boundary-audit.log")
check("32_author_closed_types_and_six_definition_values_replayed_exact",len(author)==32 and author==original,
 {"source_defs":6,"source_proofs":20,"author_boundaries":6,"type_and_definitionValue_exact":True})
check("all_32_author_and_22_independent_records_have_only_standard_axioms",len(boundaries)==22 and
 all(set(r['axioms'])<=STANDARD for r in author+boundaries),{"allowed_axioms":sorted(STANDARD),"sorryAx":False})
source=(TASK/"formalization/CoefficientMapAggregate.lean").read_text(encoding="utf-8-sig")
code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',source,flags=re.S))
declarations=re.findall(r'(?m)^(def|theorem)\s+(\w+)',code)
check("all_six_defs_and_twenty_proofs_covered_no_source_holes",len(declarations)==26 and sum(k=='def' for k,n in declarations)==6 and
 not re.search(r'\b(sorry|admit|axiom|unsafe)\b',code) and {"ZetaNine.CoefficientMapAggregate."+n for k,n in declarations}<=
 {r['declaration'] for r in author},{"complete_source_decl_coverage":True})
check("imports_are_actual_Summation_and_Mathlib_only",source.splitlines()[:3]==[
 "import missions.zeta9.formalization.CoefficientMapSummation","import Mathlib.Algebra.Polynomial.Eval.SMul","import Mathlib.Algebra.Polynomial.BigOperators"],
 {"Theorems_imports":[],"Solutions_imports":[],"assumed_coefficients":[],"proof_input_boundaries":[]})
check("actual_F_uses_negative_finite_B_and_true_rho3_5_7_9",all(n in {r['declaration'] for r in boundaries} for n in
 ['agg_ind_actual_B_negative_harmonic','agg_ind_actual_five_odd_coordinates']),
 "B = negative double finite harmonic sum of actual local coefficients; four remaining coordinates are actual sums of orders3,5,7,9.")
check("linearity_is_proved_from_actual_local_series_not_assumed",all(n in {r['declaration'].split('.')[-1] for r in author} for n in
 ['actual_local_coefficient_add','actual_local_coefficient_smul','actual_constant_add','actual_constant_smul','aggregate_add','aggregate_smul']) and
 'agg_ind_general_rational_linearity' in {r['declaration'] for r in boundaries},"Arbitrary rational W,V and scalar a,b; no properness required for linearity.")
check("all_quartic_coordinates_restore_including_zero_and_nonmonic",all(n in {r['declaration'] for r in boundaries} for n in
 ['agg_ind_roundtrip_zero','agg_ind_roundtrip_nonmonic','agg_ind_basis','agg_ind_quartic_restoration_kernel']),
 "Fin5 coefficients recover every natDegree≤4 polynomial. Coordinate injectivity is proved; aggregate injectivity is separate.")
check("aggregate_zero_implies_all_rho_and_genuine_HasSum_only_with_strong_even_inputs",all(n in {r['declaration'] for r in boundaries} for n in
 ['agg_ind_hasSum_zero_strong_even','agg_ind_all_rho_zero_strong_even']),
 {"required":["Even n","StrongProperMultiplier n W","actual aggregate n W=0"],"conclusion":"actual all-nine rho zero and HasSum of genuine weightedR(k+1) equal0","kernel_triviality_inferred":False})
check("n0_X4_real_nonzero_quartic_kernel_rho1_1_proper_not_strong",all(n in {r['declaration'] for r in boundaries} for n in
 ['agg_ind_n_zero_X_four_F_zero','agg_ind_n_zero_X_four_rho1','agg_ind_n_zero_X_four_proper_not_strong',
  'agg_ind_n_zero_actual_F_not_injective','agg_ind_n_zero_quartic_F_nonzero_kernel']),"Actual quartic input e4/X4 maps to0 while nonzero. rho1=1; strict properness alone cannot eliminate simple poles.")
check("n0_X3_real_five_coordinate_output_and_X4_no_HasSum",all(n in {r['declaration'] for r in boundaries} for n in
 ['agg_ind_n_zero_X_three_output','agg_ind_n_zero_X_four_actual_sequence','agg_ind_n_zero_F_zero_does_not_give_HasSum']),
 "F0(X3)=e1 actual order3 output. F0(X4)=0 but actual sequence1/(k+1) has no HasSum to any real L.")
prints=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(OUT/"native-Aggregate.log").read_text(encoding="utf-8-sig"))
check("six_actual_source_prints_standard_three_axioms",len(prints)==6 and all({a.strip() for a in aa.split(',')}<=STANDARD for n,aa in prints),
 {"prints":6,"object_source_sha256_bound":True})
write(OUT/"independent-original-types.json",author);write(OUT/"independent-boundary-types.json",boundaries)
findings=[{"severity":"information","code":"DOMAIN", "detail":"Actual rational five-dimensional linear F and quartic coordinate recovery only. Aggregate kernel triviality on original even n≥2, inverse and prescribed-target construction remain open in this source."},
 {"severity":"information","code":"NECESSARY_NOT_SUFFICIENT", "detail":"Zero F plus Even/Strong yields all aggregate rho zero and genuine HasSum0; it does not yield every local coefficient zero or W=0. Full local array injectivity cannot be applied to aggregate zeros."},
 {"severity":"information","code":"REUSE", "detail":"Seven previously fresh independent actual sources and one pure Definition are reused by immutable source/object/log/receipt hashes. Byte-identical objects are cloned into this new cache; no author or root native objects are borrowed."},
 {"severity":"information","code":"RETAINED_TRIALS", "detail":"Attempt01 was a partial-cache prefix import error. Attempt02 left a reviewer Pi.single Fin simplification goal, with elaborator sorryAx in that failed log. Both are preserved/excluded; final own boundary22 records allstandard3. Frozen mathematical source was never changed."}]
md="Independent Aggregate mathematical review: PASS.\n\nActual F is (B,rho3,rho5,rho7,rho9), with genuine finite harmonic B and local-series coefficients. All six definitions and twenty proofs are covered;32 author records match exactly and22 independent closed boundaries use standard axioms. Three fresh Lean calls exit0, using eight hash-verified dependencies from the prior independent Summation replay.\n\nQuartic coordinates restore zero and nonmonic polynomials. Actual aggregate linearity holds for arbitrary rational multipliers. StrongProper plus Even plus F=0 yields genuine HasSum0 and all aggregate rho cancellations, without proving W=0.\n\nn0X4 gives a real nonzero quartic kernel vector with rho1=1, proper but not strong; its harmonic sequence admits no HasSum. Original even n≥2 aggregate kernel triviality, inverse and prescribed-target conclusions remain open in this source. Retained failed reviewer trials are excluded. No root/scope/API/credential writes.\n"
(OUT/"independent-review.md").write_text(md,encoding="utf-8")
(OUT/"independent-review.log").write_text("PASS\n"+'\n'.join(c['name']+': PASS' for c in checks)+'\n',encoding="utf-8")
paths.update(p for p in OUT.rglob('*') if p.is_file() and p.name!='independent-review.json')
files=[{"task_relative":p.relative_to(TASK).as_posix() if p.is_relative_to(TASK) else None,"root_relative":p.relative_to(ROOT).as_posix(),
 "bytes":p.stat().st_size,"sha256":sha(p)} for p in sorted(paths,key=lambda p:p.as_posix())]
report={"schema_version":1,"verdict":"PASS","scope_verdict":"PASS_ACTUAL_F_LINEARITY_AND_QUARTIC_COORDINATES_ONLY",
 "review_role":"Independent mathematics reviewer; not Aggregate author","checked_at":datetime.now(timezone.utc).isoformat(),
 "source":"missions/zeta9/formalization/CoefficientMapAggregate.lean","source_sha256":controls['source'],
 "environment":{"lean_toolchain":"leanprover/lean4:v4.33.1","mathlib_rev":"0df444a360eaa60ab8c11dca51a86af692955474"},
 "checks":checks,"findings":findings,"counts":{"fresh_calls":3,"reused_actual_native_sources":7,"reused_pure_Definitions":1,"author_records":32,"independent_boundary_records":22},
 "original_even_n_at_least_two_kernel_triviality_proved_in_source":False,"aggregate_inverse_proved_in_source":False,
 "five_dimensional_aggregate_distinct_from_full_local_array":True,"new_external_proof_assumptions":[],
 "root_scope_API_credentials_writes":False,"failed_trials_excluded_from_success_evidence":True,"stable_files":files,
 "hash_exclusions":["report self","scope/status","API/docs/credentials"]}
write(OUT/"independent-review.json",report)
assert all(sha(ROOT/f['root_relative'])==f['sha256'] for f in files)
print('Aggregate independent PASS '+str(len(checks))+' checks '+str(len(files))+' bindings')
print('report_sha256='+sha(OUT/"independent-review.json"))
