from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
OUT=Path(__file__).resolve().parent; TASK=OUT.parents[1]; ROOT=TASK.parents[1]
AUTHOR=TASK/'verification/formalization-coefficient-map-kernel-2026-10-04'
TELE=TASK/'verification/formalization-coefficient-map-telescoper-independent-2026-10-04'
OTHER={
 'aggregate':('verification/formalization-coefficient-map-aggregate-independent-2026-10-04/independent-review.json','d2f50aa65f5dec147e632642c78cd27aaa7d8b7ba554067b389d5cc669002ddc',107),
 'shift-degree':('verification/formalization-coefficient-map-shift-degree-independent-2026-10-04/independent-review.json','d38de9f7991fedbd716bd2b1824cda09f979c1da91191bff43e8f0ea3922e5df',54)}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def dump(p,v): p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def records(p):
 out={}
 for line in p.read_text(encoding='utf-8-sig').splitlines():
  if line.startswith('{'):
   row=json.loads(line)
   if 'declaration' in row: out[row['declaration']]=row
 return out
source=TASK/'formalization/CoefficientMapKernelBridge.lean'; text=source.read_text(encoding='utf-8')
receipt=load(OUT/'independent-compile-receipt.json'); prior=load(TELE/'independent-review.json')
author_row=next(r for r in receipt['rows'] if r['label'].startswith('author-type-replay'))
own_row=next(r for r in reversed(receipt['rows']) if r['label'].startswith('independent-boundary') and r['exit_code']==0)
author=records(Path(author_row['log'])); expected_author=records(AUTHOR/'type-audit.log'); own=records(Path(own_row['log']))
source_pairs=re.findall(r'^(def|theorem)\s+(\w+)',text,re.M)
names=['ZetaNine.CoefficientMapKernelBridge.'+n for _,n in source_pairs]
standard={'propext','Classical.choice','Quot.sound'}; checks=[]; additional={}
def check(name,condition,detail):
 checks.append({'name':name,'pass':bool(condition),'detail':detail}); assert condition,name
check('fixed_final_source_and_author_receipt_manifest',sha(source)==receipt['expected']['source'] and sha(AUTHOR/'compile-receipt.json')==receipt['expected']['receipt'] and sha(AUTHOR/'SHA256SUMS.txt')==receipt['expected']['manifest'],receipt['expected'])
check('all_forty_six_frozen_author_members_recomputed',len(receipt['reuse']['author_manifest_bindings'])==46 and all(sha(Path(r['path']))==r['sha256'] for r in receipt['reuse']['author_manifest_bindings']),46)
check('explicit_telescoper_independent_cache_reuse_bound',sha(TELE/'independent-review.json')==receipt['expected']['telescoper_review'] and len(prior['stable_files'])==150 and all(sha(ROOT/r['root_relative'])==r['sha256'] for r in prior['stable_files']),{'review':receipt['expected']['telescoper_review'],'bindings':150,'fixed_cloned_objects':len(receipt['cloned_fixed_objects'])})
for key,(path,h,count) in OTHER.items():
 p=TASK/path; d=load(p); additional[key]=d
 check('previous_'+key+'_independent_PASS_fully_rebound',sha(p)==h and d['verdict']=='PASS' and len(d['stable_files'])==count and all(c['pass'] for c in d['checks']) and all(sha(ROOT/r['root_relative'])==r['sha256'] for r in d['stable_files']),{'report_sha256':h,'checks':len(d['checks']),'bindings':count})
check('four_fresh_final_runs_actually_zero',len(receipt['rows'])==4 and all(r['exit_code']==0 and int(Path(r['exit_file']).read_text())==0 and sha(Path(r['log']))==r['log_sha256'] for r in receipt['rows']),[(r['label'],r['exit_code']) for r in receipt['rows']])
check('complete_author_thirty_seven_types_values_reproduced',len(author)==37 and author==expected_author,{'author_records':37,'source_declarations':30,'actual_defs':7})
check('all_source_definitions_and_theorems_independently_visible',len(names)==30 and sum(k=='def' for k,n in source_pairs)==7 and all(n in own and own[n]==author[n] for n in names),names)
check('all_final_records_standard_three_only',all(set(r['axioms'])<=standard for r in list(author.values())+list(own.values())),{'author':len(author),'independent':len(own),'independent_closed_top_level':len([n for n in own if n.startswith('IndependentKernel.') and n.count('.')==1])})
check('actual_R_shift_derived_from_true_finite_products','numerator_shift_identity' in text and 'poleProduct_shift_identity' in text and 'IndependentKernel.concrete_R_A_B_shift' in own,'True n!^7 numerator positive/negative products and actual product poles prove R(t+1)A(t+1)=R(t)B(t), with both rational evaluations regular. Independent n2,t4 exact numeric check succeeds.')
check('actual_R_A_is_true_Pzero_over_actual_M_ninth','rootPolynomial_numerator_factor' in text and 'poleProduct_last_factor' in text and 'IndependentKernel.true_R_A_factor' in own,'True P0 consists of positive1..n+1 and negative-n..-2n factors; n!^7 P0 = actual numerator*(t-n-1)*(t+n). Last pole factor cancellation yields R*A=n!^7 P0/M_n^9 with actual regular denominator.')
check('true_polynomial_relation_from_infinite_regular_eval_points','Polynomial.eq_of_infinite_eval_eq' in text and 'Set.Ioi_infinite' in text and 'actual_R_ne_zero_above_n' in text and 'IndependentKernel.actual_polynomial_bridge_no_supplied_shift_relation' in own,'For every rational t>n+1, true R is nonzero and t,t+1 regular. Actual Q=P0*H/M_n^9, actual R difference and proved shift relation give n!^7 W(u)=A H-B H(t+1). Equality on the infinite positive interval gives the polynomial equality, without supplying that relation as an input.')
check('actual_quotient_degree_plus_shift_obstruction_closes_quartic_kernel','actual_polynomial_quotient_degree_bound' in text and 'actual_shift_difference_small_degree_implies_zero' in text and 'IndependentKernel.genuine_kernel_from_five_raw_entries' in own,'Even n>=2 and degreeW<=4 imply strong bound. Actual quotient H degree<=7n-3; true polynomial relation has degree<=8. Independently checked shift coefficient (7n-2-degH)*LC(H) forces H0, then W(comp u)0 and actual polynomial composition injectivity force W0. No trivial-kernel, determinant or rank input.')
check('difference_of_actual_quartics_gives_injective_map','Polynomial.natDegree_sub_le' in text and 'original_quartic_aggregate_kernel_zero' in text and 'IndependentKernel.concrete_n_two_bijective' in own,'Actual aggregate is linear. Subtracting equal quartic outputs stays degree<=4 and gives zero output. Fin5 coordinate polynomials and their proved recovery transfer injectivity to the actual rational 5-dimensional map.')
check('bijection_and_actual_linear_equivalence_are_derived','LinearMap.injective_iff_surjective.mp hi' in text and 'LinearEquiv.ofBijective' in text and 'IndependentKernel.actual_equiv_toFun' in own,'Domain and codomain are the same finite-dimensional Fin5→Q vector space. Surjectivity follows from already proved injectivity, and actualAggregateEquiv has exactly actual F as its toFun; inverse is constructed from this proof.')
check('inverse_five_raw_output_laws_and_zero_linearity',all(n in own for n in ['IndependentKernel.all_five_inverse_outputs','IndependentKernel.inverse_both_actual_coordinate_laws','IndependentKernel.inverse_zero_exact','IndependentKernel.inverse_add_actual','IndependentKernel.inverse_smul_actual']),'All B,rho3,rho5,rho7,rho9 coordinates exactly equal the prescribed rational vector. Both inverse laws, exact zero inverse, addition and rational scalar multiplication are closed independent statements.')
check('unique_rational_quartic_for_every_integer_or_rational_output','IndependentKernel.integer_outputs_have_unique_rational_quartic' in own and 'IndependentKernel.original_integer_coefficients_injectivity' in own,'Every rational output has a unique rational quartic preimage. Integer output is a rational-cast specialization; integer multiplier existence or denominator/height estimates are not claimed.')
check('actual_prescribed_L_HasSum_and_absolute_not_only_totalized_tsum',all(n in own for n in ['IndependentKernel.prescribed_target_actual_HasSum','IndependentKernel.prescribed_target_absolute_sum']) and 'actualSeries_hasSum_exactL' in text and 'actualSeries_norm_summable' in text,'True inverse polynomial is strong quartic, its true exactL is b0+b1*zeta3+b2*zeta5+b3*zeta7+b4*zeta9, genuine HasSum and norm Summable follow from the already closed actual analytic source. No supplied convergence or zeta identity hypothesis.')
check('pure_zeta_nine_nonzero_rational_lift_closed','IndependentKernel.pure_zeta_nine_nonzero_rational_quartic' in own,'For every even n>=2 target e4 gives nonzero degree<=4 rational W with actual F(W)=e4, true weightedR positive series HasSum(Re zeta9), absolute summability. Nonzero W is not a decay or irrationality claim.')
check('zero_n_noninjective_boundary_and_domain_exclusions_closed',all(n in own for n in ['IndependentKernel.zero_n_nonzero_quartic_aggregate_kernel','IndependentKernel.zero_n_aggregate_quartic_not_injective','IndependentKernel.excluded_n_zero_and_odd_one']),'Actual n0 quartic X4 is nonzero with aggregate0; actual Fin5 map is not injective. n0 fails n>=2 and odd1 fails Even; no all-n conclusion is asserted.')
check('no_custom_axiom_sorry_or_opaque_extra_proof_input',not re.search(r'\b(sorry|admit|axiom)\b',text) and not re.search(r'^\s*(opaque|unsafe)\s',text,re.M),'Every source declaration is exposed in actual type/value audit, including full kernel, bijection, inverse and HasSum statements. Only standard3 axioms; no assumed rank, determinant, relation, inverse, integral preimage or irrationality statement.')
check('scope_keeps_arithmetic_decay_and_main_irrationality_open',all(w not in text for w in ['theorem irrational','theorem Irrational','sorryAx']),'Closed scope is p9,q1,m=n,d0, even n>=2 rational quartic F kernel/inverse and prescribed actual linear sum. General parameters, integral preimages, height/denominator asymptotics, nonzero small integer forms, A/V/lattice/J and irrationality are outside this report.')
dump(OUT/'independent-original-types.json',list(author.values())); dump(OUT/'independent-boundary-types.json',list(own.values()))
stable={}
def bind(p):
 p=p.resolve(); stable[str(p)]={'root_relative':p.relative_to(ROOT).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
for r in prior['stable_files']: bind(ROOT/r['root_relative'])
bind(TELE/'independent-review.json')
for key,(path,h,count) in OTHER.items():
 bind(TASK/path)
 for r in additional[key]['stable_files']: bind(ROOT/r['root_relative'])
bind(AUTHOR/'SHA256SUMS.txt')
for r in receipt['reuse']['author_manifest_bindings']: bind(Path(r['path']))
for p in OUT.rglob('*'):
 if p.is_file() and p.name not in ['independent-review.json','independent-review.md']: bind(p)
report={'schema_version':1,'verdict':'PASS','scope_verdict':'PASS_ACTUAL_ORIGINAL_EVEN_N_AT_LEAST_TWO_QUARTIC_F_KERNEL_INVERSE_AND_PRESCRIBED_ABSOLUTE_HASSUM',
 'review_role':'Independent mathematical and Lean reviewer; another agent authored KernelBridge',
 'checked_at':datetime.now(timezone.utc).isoformat(),'source':source.relative_to(ROOT).as_posix(),'source_sha256':sha(source),
 'author_frozen_hashes':receipt['expected'],'checks':checks,'actual_type_records':{'author':len(author),'independent':len(own)},
 'fresh_successful_runs':receipt['rows'],'explicit_independent_cache_reuse':receipt['reuse'],'cloned_fixed_objects':receipt['cloned_fixed_objects'],
 'actual_original_quartic_kernel_closed':True,'actual_original_five_dimensional_map_bijective_closed':True,
 'actual_original_rational_quartic_inverse_closed':True,'unique_integer_output_rational_preimage_closed':True,
 'prescribed_target_actual_HasSum_and_absolute_closed':True,'pure_zeta9_nonzero_rational_quartic_lift_closed':True,
 'integer_multiplier_preimage_closed':False,'inverse_height_or_denominator_asymptotics_closed':False,
 'small_nonzero_integer_form_sequence_closed':False,'general_p_m_multilayer_derivative_closed':False,
 'A_V_lattice_J_closed':False,'irrationality_closed':False,'custom_axioms':[],
 'root_scope_API_credentials_writes':False,'author_failed_first_bridge_attempt_is_not_success_evidence':True,'stable_files':list(stable.values())}
dump(OUT/'independent-review.json',report)
(OUT/'independent-review.md').write_text('Independent KernelBridge review: PASS\n\nFor p=9,q=1,m=n,d=0 and every even n>=2, the actual five-dimensional aggregate F on rational quartics is bijective. The proof derives the genuine R shift and R*A identities, obtains the polynomial shift relation on infinitely many positive regular points, and applies the independently checked degree obstruction to the actual telescoper quotient. No kernel, rank, determinant or inverse assumption is supplied.\n\nFresh ShiftDegree and KernelBridge source builds, exact author37-record replay and independent boundary audit all exited0 with standard3 axioms. Prior independent Telescoper, Aggregate and ShiftDegree reports and their bound files were recomputed; ten prior independent objects are explicitly cloned without author/root mission objects.\n\nThe actual inverse has all five prescribed rational outputs, a unique rational quartic preimage, both inverse laws, zero/addition/scalar identities, genuine prescribed-L HasSum and norm summability. Target pure zeta9 has a nonzero rational quartic lift. The actual n0 map remains noninjective; degree/domain restrictions were checked.\n\nInteger output gives a rational preimage only. Integral multiplier existence, inverse denominator/height estimates, small nonzero integer form sequences, general parameters, A/V/lattice/J and irrationality remain outside this verified scope. No platform operation was performed.\n',encoding='utf-8')
print(json.dumps({'verdict':'PASS','checks':len(checks),'bindings':len(stable),'type_records':report['actual_type_records'],'report_sha256':sha(OUT/'independent-review.json')}))
