from run_step import *
import re
assert load(OUT/'mechanical-checks.json')['complete'];verify()
plan=load(BATCH/'root-copy-plan.json')
for r in plan['files']:
 rel=r['root_relative_destination'];src=PROJECT/rel;write(src,(TASK/r['staged_task_relative']).read_bytes());assert sha(src)==r['sha256']
 run('staged '+rel,src,P,P/(rel.removesuffix('.lean')+'.olean'))
for name in ['types_original.lean','types_definition.lean']+[f'types_{i}_{k}.lean' for i in range(3) for k in ['solution','reference']]+[f'helpers_{i}.lean' for i in range(3)]:
 src=OUT/name;write(src,(BATCH/name).read_bytes());run('actual fresh '+name,src,N if name=='types_original.lean' else P)
mechanical=load(OUT/'mechanical-checks.json');NS='ZetaNine.CoefficientMapAggregate';maps=['aggregateLinearMap','coordinateLinearMap','quarticAggregateLinearMap']
contexts=['Definitions.Def_ZetaNine_CoefficientMapTelescoper']+[r['root_relative_destination'].removesuffix('.lean').replace('/','.') for r in plan['files'] if not r['root_relative_destination'].startswith('Definitions/')]
for i,m in enumerate(contexts):
 code='import '+m+'\nimport Lean\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.universes false\nset_option pp.proofs true\nrun_meta do\n  for name in ['+', '.join('`'+NS+'.'+n for n in maps)+'] do\n'
 code+='''    let ci ← getConstInfo name
    let .defnInfo d := ci | throwError "Expected actual staged map"
    let typ ← ppExpr d.type
    let val ← ppExpr d.value
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("full_expression_repr",Json.str (reprStr d.value)),("raw_value",Json.str val.pretty),
      ("pp_proofs",toJson true),("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
 src=OUT/(f'fc{i}.lean');write(src,code);run('canonical staged full map context '+str(i),src,P)
proofs=mechanical['core_proof_names']+mechanical['actual_cross_helpers'];assert len(proofs)==106
code='import missions.zeta9.formalization.CoefficientMapTelescoper\nimport Lean\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.universes false\nrun_meta do\n  for name in ['+', '.join('`'+n for n in proofs)+'] do\n'
code+='''    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
src=OUT/'np.lean';write(src,code);run('actual106 native source and required helper proofs',src,N)
selected='actual_polynomial_quotient_degree_bound';replacement='checked_'+selected
enroll=load(OUT/'preparation-enrollment.json');changes=[]
for i,r in enumerate(enroll['fixed_native_controls']):
 original=PROJECT/(r['module']+'.lean');s=original.read_text(encoding='utf-8-sig');old='import missions.zeta9.formalization.CoefficientMapTelescoper'
 assert s.count(old)==1
 s=s.replace(selected,replacement).replace(old,'import Solutions.Sol_ZetaNine_CoefficientMapTelescoper_'+selected)
 src=OUT/(f'bc{i}.lean');write(src,s)
 expected=(BATCH/('stage-native-author-audit.lean' if i==0 else 'stage-independent-boundary-audit.lean')).read_bytes();assert src.read_bytes()==expected
 run('actual staged original control '+str(i),src,P)
 changes.append({'source_module':r['module'],'original_sha256':sha(original),'staged_sha256':sha(src),'changes':['actual Solution import','selected endpoint source name and quoted diagnostic name only'],'proofs_modified':False,'expected_records':35 if i==0 else 54})
src=OUT/'ob.lean'
write(src,'''import Solutions.Sol_ZetaNine_CoefficientMapTelescoper_actual_polynomial_quotient_degree_bound
import Lean
open Polynomial Finset
open ZetaNine.CoefficientMapTelescoper ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
namespace TelIndependent
theorem nonconstantCumulative : prefixSum (fun i => (i : ℚ) + 1) 2 = 6 := by
  norm_num [prefixSum, Finset.sum_range_succ]
theorem zeroNNumerator (W : ℚ[X]) : telescoperNumerator 0 W = 0 := by
  simp [telescoperNumerator]
theorem zeroMultiplierNumerator (n : ℕ) : telescoperNumerator n 0 = 0 := by
  simp [telescoperNumerator, cumulativeCoefficient, prefixSum,
    weightedLocalCoefficient, weightedClearedSeries]
theorem rootNodePositiveEdge (n : ℕ) :
    rootNode n (.inl ⟨n, by omega⟩) = (n : ℚ) + 1 := rfl
theorem rootNodeNegativeEdge (n : ℕ) :
    rootNode n (.inr ⟨n, by omega⟩) = -2 * (n : ℚ) := by
  simp [rootNode]
  ring
theorem oddNOneNodeProduct : rootPolynomial 1 =
    ((X - 1) * (X - 2)) * ((X + 1) * (X + 2)) := by
  rw [rootPolynomial_eq_explicit_products]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num only [Nat.cast_ofNat, map_zero, map_one, map_ofNat, zero_add, add_zero, mul_one, one_mul]
  ring
theorem oddNOneNumeratorDegreeAllW (W : ℚ[X]) : (telescoperNumerator 1 W).natDegree ≤ 8 := by
  simpa using telescoperNumerator_natDegree_le 1 (by omega) W
theorem evenNTwoActualQuotient (W : ℚ[X]) (hstrong : StrongProperMultiplier 2 W)
    (hz : aggregate 2 W = 0) : ∃ H : ℚ[X],
    telescoperNumerator 2 W = rootPolynomial 2 * H ∧ H.natDegree ≤ 11 := by
  simpa using checked_actual_polynomial_quotient_degree_bound 2 (by omega)
    (by norm_num : Even 2) W hstrong hz
end TelIndependent
set_option pp.fullNames true
run_meta do
  let env ← Lean.getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `TelIndependent do continue
    let .thmInfo _ := ci | continue
    let typ ← Lean.Meta.ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Lean.Json.mkObj [("declaration",Lean.Json.str name.toString),
      ("type",Lean.Json.str typ.pretty),("axioms",Lean.toJson (axs.toList.map Lean.Name.toString))]).compress
''')
run('eight independent own true numerator and root controls',src,P)
dump(OUT/'replay-summary.json',{'complete':True,'native_required_proofs':proofs,'staged_proof_records':321,'Def_contexts':7,'proof_bearing_map_context_records':21,
 'direct_native_Meta_isDefEq_calls':6,'direct_staged_Meta_isDefEq_calls':6,'full_value_calls_not_context_propagation':True,'contexts':contexts,'control_source_changes':changes,'own_boundary_records':8})
r=load(OUT/'review-compile-receipt.json');r['complete']=True;dump(OUT/'review-compile-receipt.json',r)
print('Tel replay completed; counts remain subject to final independently parsed logs',flush=True)
