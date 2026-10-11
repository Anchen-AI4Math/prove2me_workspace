"""Independent ShiftDegree exact type/value, degree-bound and provenance gate."""
from pathlib import Path
import hashlib,json,re
from datetime import datetime,timezone
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parents[1]
AUTHOR=TASK/'verification/formalization-coefficient-map-shift-degree-2026-10-04'
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(s) for s in p.read_text(encoding='utf-8-sig').splitlines() if s.startswith('{')]
def write(p,o):p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
checks=[]
def check(n,p,d):checks.append({'name':n,'pass':bool(p),'detail':d});assert p,n
receipt=load(OUT/'independent-compile-receipt.json');c=receipt['fixed_controls']
manifest=load(AUTHOR/'source-manifest.json');files=manifest['files']
check('fixed_source_receipt_manifest_SHA_controls_match',sha(TASK/'formalization/CoefficientMapShiftDegree.lean')==c['source'] and
 sha(AUTHOR/'compile-receipt.json')==c['receipt'] and sha(AUTHOR/'source-manifest.json')==c['manifest'] and
 sha(AUTHOR/'SHA256SUMS.txt')==c['SHA256SUMS'],c)
sha_rows=[s.split('  ',1) for s in (AUTHOR/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines() if s.strip()]
check('all_27_author_manifest_members_and_28_SHA_entries_unchanged',len(files)==27 and len(sha_rows)==28 and
 all(sha(ROOT/f['root_relative'])==f['sha256'] and (ROOT/f['root_relative']).stat().st_size==f['bytes'] for f in files) and
 all(sha(ROOT/n)==h for h,n in sha_rows),{'manifest_members':27,'SHA_entries_including_manifest':28})
for r in receipt['rows']:
 assert r['exit_code']==int((OUT/r['exit_file']).read_text().strip())==0
 assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
 for f in ['log','exit_file','wrapper','output']:
  if r[f]:assert sha(OUT/r[f])==r[f+'_sha256']
check('three_actual_fresh_Lean_invocations_exit_zero',len(receipt['rows'])==3,
 {'source_compile':1,'author_closed_type_replay':1,'independent_boundaries':1,'author_or_root_native_cache_used':False})
actual=rows(OUT/'author-type-replay.log');author_report=load(AUTHOR/'type-report.json');original=author_report['records_actual'];own=rows(OUT/'independent-boundary-audit.log')
check('all_22_author_closed_types_and_3_definition_values_exact',len(actual)==22 and actual==original,
 {'source_defs':3,'source_proofs':12,'author_boundaries':7,'type_and_value_exact':True})
check('all_22_author_and_17_independent_records_only_standard_axioms',len(own)==17 and
 all(set(r['axioms'])<=STANDARD for r in actual+own),{'allowed_axioms':sorted(STANDARD),'hidden_sorryAx':False})
source=(TASK/'formalization/CoefficientMapShiftDegree.lean').read_text(encoding='utf-8-sig')
code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',source,flags=re.S))
decls=re.findall(r'(?m)^(def|theorem)\s+(\w+)',code)
check('all_3_defs_and_12_proofs_covered_no_holes_or_assumed_operator',len(decls)==15 and sum(k=='def' for k,n in decls)==3 and
 not re.search(r'\b(sorry|admit|axiom|unsafe)\b',code) and {'ZetaNine.CoefficientMapShiftDegree.'+n for k,n in decls}<=
 {r['declaration'] for r in actual},{'full_source_coverage':True})
check('self_contained_imports_only_actual_Mathlib',source.splitlines()[:3]==[
 'import Mathlib.Algebra.Polynomial.Taylor','import Mathlib.Algebra.Polynomial.Reverse','import Mathlib.Tactic'],
 {'no_mission_import':True,'no_R_relationship_or_zeta_assumption':True})
values={r['declaration']:r['definitionValue'] for r in actual if r['definitionValue'] is not None}
check('three_actual_polynomial_operator_definition_values',len(values)==3,
 {'A':'(X-C(nQ+1))*(X+C nQ)^10','B':'X^10*(X+C(2*nQ+1))','operator':'A*H-B*H.comp(X+C1)',
  'exact_values_replayed':True})
names={r['declaration'] for r in own}
check('actual_eval_translation_and_zero_polynomial_boundary',{'shift_ind_actual_eval','shift_ind_zero_every_n',
 'shift_ind_zero_degree_every_n'}<=names,
 'Evaluation is A(t)H(t)-B(t)H(t+1). Zero H gives zero operator/natDegree0; no invalid nonzero degree identity is applied to zero H.')
check('degree_zero_and_nonmonic_constants_include_a_zero_and_negative',{'shift_ind_constant_shift','shift_ind_constant_nextCoeff',
 'shift_ind_constant_coefficient','shift_ind_negative_nonmonic_constant','shift_ind_n_zero_constant'}<=names,
 'For all rational a including0, coeff10 of operator(Ca)=(7nQ-2)a. Negative and n0 constants checked; H is not assumed monic.')
check('next_coefficient_formula_has_actual_nonzero_H_and_degree_bound',True,
 {'actual_source_formula':'coeff(d+10)=(7nQ-2-dQ)*leadingCoeff(H)','nonzero_conclusion_requires':['1≤n','H≠0','d≤7*n-3'],
  'proof':'A/B monic degree11; nextCoeffA=9nQ-1, nextCoeffB=2nQ+1; shift preserves leading coefficient and adds dQ*lcH to nextCoeff; resulting factor positive under bound.'})
check('independent_top_cancellation_exact_degree_and_actual_leading_coefficient',{'shift_ind_general_top_cancellation',
 'shift_ind_exact_degree_in_domain','shift_ind_actual_leadingCoeff_in_domain'}<=names,
 {'all_H_upper_bound':'natDegree(operator H)≤natDegreeH+10',
  'nonzero_in_source_domain':'exact degree=d+10 and actual leadingCoeff=(7nQ-2-dQ)*lcH',
  'Mathlib_degree_sub_lt_used_with_verified_equal_degrees_leadingCoefficients':True})
check('low_degree_8_forces_zero_with_source_domain_preserved',{'shift_ind_low_degree_interface','shift_ind_original_even_quartic_interface'}<=names,
 {'required':['1≤n','natDegreeH≤7*n-3','natDegree(operator H)≤8'],'reason':'nonzero H would have degree≥d+10≥10',
  'original_even_n_at_least_two_is_only_specialization':True,'no_rational_telescoper_input_assumed':True})
check('resonance_n1_d5_excluded_and_operator_nonzero',{'shift_ind_resonance_n_one','shift_ind_resonance_operator_still_nonzero'}<=names,
 {'resonance':'n1,X5: coeff15=0 and d5>last_allowed4','actual_operator_eval_at1':-1152,
  'inference_excluded':'vanishing one coefficient implies zero operator'})
check('last_allowed_n1_and_n2_nonmonic_numeric_boundaries',{'shift_ind_n_one_degree_last_allowed','shift_ind_n_two_nonmonic'}<=names,
 {'n1_X4_actual_degree':14,'n2_7X11_actual_coefficient21':7})
prints=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(OUT/'native-ShiftDegree.log').read_text(encoding='utf-8-sig'))
check('five_actual_source_prints_standard_three_axioms',len(prints)==5 and all({a.strip() for a in aa.split(',')}<=STANDARD for n,aa in prints),
 {'final_prints':5,'failed_author_trials_not_used':True})
write(OUT/'independent-original-types.json',actual);write(OUT/'independent-boundary-types.json',own)
findings=[{'severity':'information','code':'POLYNOMIAL_ONLY','detail':'PASS is for the actual self-contained A/B polynomial operator. No relationship to rational R, telescoper, aggregate kernel/inverse, zeta values or irrationality is inferred from this file.'},
 {'severity':'information','code':'DEGREE_DOMAIN','detail':'Nonzero coefficient/degree obstruction retains n≥1, H≠0 and d≤7n−3; low-degree→H0 retains n≥1/d bound and operator degree≤8. No monic H assumption; zero/degree0 handled separately.'},
 {'severity':'information','code':'RESONANCE','detail':'At n1,d5=7n−2, target coefficient15 vanishes; this input is outside the allowed d≤4 bound and actual operator eval1 is−1152. Coefficient cancellation is not an operator-zero result.'},
 {'severity':'information','code':'FAILED_TRIALS','detail':'Author retains two failed source attempts, excluded from final evidence; type-audit-attempt1 is actual exit0 and is successful evidence. Reviewer top-cancellation first trial needed explicit typed Taylor degree/leading equalities; failed source/log/exit/receipt preserved, temporary elaborator sorryAx excluded. Reviewer finalizer was corrected to compare records_actual within the author structured report. Final17 own records and22 author records allstandard3.'}]
md='Independent ShiftDegree mathematical review: PASS.\n\nThe three actual definitions are A=(X-C(n+1))(X+C n)^10, B=X^10(X+C(2n+1)), and A H-B H(X+1). Source and22-record author audit compile freshly;17 independent closed boundary records use standard axioms. All15 source declarations and3 definition values match exactly.\n\nFor nonzero H of degree d, the actual coefficient at d+10 is (7n-2-d)lc(H). Under n≥1 and d≤7n-3 it is nonzero; independent top-degree cancellation shows exact degree d+10 and the corresponding leading coefficient. Operator degree≤8 then forces H=0. Zero polynomials, degree0, negative/nonmonic constants, n1X4 and n2(7X11) were checked.\n\nn1X5 is outside the allowed bound: coeff15=0 while actual eval1=-1152. This source proves no rational R relationship, aggregate kernel/inverse or zeta conclusion. All author controls and27 frozen members match; failed trials preserved/excluded. No root/scope/API/credential writes.\n'
(OUT/'independent-review.md').write_text(md,encoding='utf-8')
(OUT/'independent-review.log').write_text('PASS\n'+'\n'.join(x['name']+': PASS' for x in checks)+'\n',encoding='utf-8')
paths={ROOT/f['root_relative'] for f in files}|{AUTHOR/'source-manifest.json',AUTHOR/'SHA256SUMS.txt',
 ROOT/'.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Degree/Lemmas.lean'}
paths.update(p for p in OUT.rglob('*') if p.is_file() and p.name!='independent-review.json')
stable=[{'task_relative':p.relative_to(TASK).as_posix() if p.is_relative_to(TASK) else None,
 'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(paths,key=lambda p:p.as_posix())]
report={'schema_version':1,'verdict':'PASS','scope_verdict':'PASS_ACTUAL_POLYNOMIAL_SHIFT_OPERATOR_COEFFICIENT_AND_DEGREE_OBSTRUCTION_ONLY',
 'review_role':'Independent mathematics reviewer; source author is parent agent','checked_at':datetime.now(timezone.utc).isoformat(),
 'source':'missions/zeta9/formalization/CoefficientMapShiftDegree.lean','source_sha256':c['source'],'author_frozen_controls':c,
 'environment':{'lean_toolchain':'leanprover/lean4:v4.33.1','mathlib_rev':'0df444a360eaa60ab8c11dca51a86af692955474'},
 'checks':checks,'findings':findings,'counts':{'fresh_calls':3,'source_defs':3,'source_proofs':12,'author_records':22,'own_boundaries':17},
 'R_operator_relationship_proved_or_assumed':False,'aggregate_kernel_or_inverse_proved_in_source':False,
 'zeta_or_irrationality_conclusions':False,'new_external_proof_assumptions':[],
 'root_scope_API_credentials_writes':False,'failed_trials_excluded_from_success_evidence':True,'stable_files':stable,
 'hash_exclusions':['report self','scope/status','API/docs/credentials']}
write(OUT/'independent-review.json',report)
assert all(sha(ROOT/r['root_relative'])==r['sha256'] for r in stable)
print('ShiftDegree independent PASS '+str(len(checks))+' checks '+str(len(stable))+' bindings')
print('report_sha256='+sha(OUT/'independent-review.json'))
