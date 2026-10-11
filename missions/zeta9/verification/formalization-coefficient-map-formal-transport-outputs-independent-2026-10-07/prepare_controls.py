"""Independent complete endpoint, concrete formula, boundary and kernel controls."""
import json,sys
import inspect_prepare as p

PREFIX='''import missions.zeta9.formalization.CoefficientMapFormalTransportOutputs
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
noncomputable section
open scoped BigOperators Matrix
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapFiniteSum
open ZetaNine.CoefficientMapConnection ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapFormalTransportOutputs
'''
FORMULAS='''namespace OutputsIndependentFormula
def connectionPair (n : ℕ) (r : Fin 5) : ℚ[X] × ℚ[X] :=
  if hn : 1 ≤ n then Classical.choose (ZetaNine.CoefficientMapConnection.connection_five_systems_unique n hn r).exists else (0,0)
def connectionP (n : ℕ) (r : Fin 5) : ℚ[X] := (ZetaNine.CoefficientMapFormalTransportData.connectionPair n r).1
def connectionQ (n : ℕ) (r : Fin 5) : ℚ[X] := (ZetaNine.CoefficientMapFormalTransportData.connectionPair n r).2
def connectionGamma (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ := fun r l => (ZetaNine.CoefficientMapFormalTransportData.connectionP n r).coeff l.val
def remainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) * (∏ i ∈ range n, (X - C ((i : ℚ) + 2))) *
    (∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1))) * q.comp (ZetaNine.CoefficientMapConnection.connectionV n)
def shiftedRemainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  (ZetaNine.CoefficientMapFormalTransportData.remainderNumerator n q).comp (X + 1)
def numeratorClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  ((A.comp (ZetaNine.CoefficientMapJet.shiftedVariable j) : ℚ[X]) : PowerSeries ℚ) *
    ((ZetaNine.CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹
def numeratorLocalCoefficient (m j s : ℕ) (A : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries m j A)
def remainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient (n + 1) j s
    (ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator n q)
def extendedOldCoefficient (n j s : ℕ) (P : ℚ[X]) : ℚ :=
  if 1 ≤ j ∧ j ≤ n + 1 then ZetaNine.CoefficientMapJet.weightedLocalCoefficient n (j - 1) s P else 0
def extendedRemainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  if j ≤ n + 1 then ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient n j s q else 0
def previousRemainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  if j = 0 then 0 else ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient n (j - 1) s q
def rho (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W
def constantTerm (n : ℕ) (W : ℚ[X]) : ℚ :=
  -(∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9, ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W * ZetaNine.HarmonicStability.harmonicPower s j)
def aggregate (n : ℕ) (W : ℚ[X]) (i : Fin 5) : ℚ :=
  match i.val with
  | 0 => ZetaNine.CoefficientMapFiniteSum.constantTerm n W
  | 1 => ZetaNine.CoefficientMapFiniteSum.rho n 3 W
  | 2 => ZetaNine.CoefficientMapFiniteSum.rho n 5 W
  | 3 => ZetaNine.CoefficientMapFiniteSum.rho n 7 W
  | _ => ZetaNine.CoefficientMapFiniteSum.rho n 9 W
def aggregateLinearMap (n : ℕ) : ℚ[X] →ₗ[ℚ] (Fin 5 → ℚ) where
  toFun := ZetaNine.CoefficientMapAggregate.aggregate n
  map_add' := ZetaNine.CoefficientMapAggregate.aggregate_add n
  map_smul' := ZetaNine.CoefficientMapAggregate.aggregate_smul n
def quarticAggregateLinearMap (n : ℕ) : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) :=
  (ZetaNine.CoefficientMapAggregate.aggregateLinearMap n).comp ZetaNine.CoefficientMapAggregate.coordinateLinearMap
def actualFMatrix (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => ZetaNine.CoefficientMapAggregate.aggregate n (X ^ i.val) j
end OutputsIndependentFormula
'''
BOUNDARIES='''namespace OutputsIndependentBoundary
theorem minimum_B (r : Fin 5) : constantTerm 3 (X ^ r.val) = constantTerm 1 (connectionP 1 r) :=
  actual_chosen_constantTerm_transport 1 (by decide) r
theorem minimum_all_coordinates (r : Fin 5) : aggregate 3 (X ^ r.val) = aggregate 1 (connectionP 1 r) :=
  actual_chosen_five_output_transport 1 (by decide) r
theorem minimum_LEFT_matrix : actualFMatrix 3 = connectionGamma 1 * actualFMatrix 1 :=
  actual_five_output_matrix_transport 1 (by decide)
theorem even_LEFT_matrix : actualFMatrix 4 = connectionGamma 2 * actualFMatrix 2 :=
  actual_five_output_matrix_transport 2 (by decide)
theorem odd_LEFT_matrix : actualFMatrix 5 = connectionGamma 3 * actualFMatrix 3 :=
  actual_five_output_matrix_transport 3 (by decide)
theorem maximum_remainder_degree :
    (∑ j ∈ range 3, ∑ s ∈ Icc 1 9, remainderCoefficient 1 j s (X ^ 9) / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 :=
  remainder_boundary_sum_zero 1 (by decide) (X ^ 9) (by norm_num)
theorem excluded_zero_parameter : weightedR 0 (1 : ℚ[X]) 1 = 1 := by
  norm_num [weightedR, actualR, numerator, poleProduct]
theorem empty_harmonic_successor (s : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range 0, f j * ZetaNine.HarmonicStability.harmonicPower s (j + 1)) = 0 := by simp
theorem maximum_quartic_degree :
    (∑ j ∈ range 2, ∑ s ∈ Icc 1 9, weightedLocalCoefficient 1 j s (X ^ 4) / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 :=
  weighted_boundary_sum_zero 1 (by decide) (X ^ 4) (by norm_num)
end OutputsIndependentBoundary
'''
BOUNDARY_NAMES=['minimum_B','minimum_all_coordinates','minimum_LEFT_matrix','even_LEFT_matrix','odd_LEFT_matrix',
    'maximum_remainder_degree','excluded_zero_parameter','empty_harmonic_successor','maximum_quartic_degree']
ARGUMENTS=['n hn W','n W hW','n hn W hW','n hn q hq','n s P','n s q','n s q','N s f',
    'n hn r s hs1 hs9','n hn r','n hn r','n hn r','n hn r','n hn','r','']

HELPERS='''import OutputsIndependentAssertionsV1
import IndependentExprDagV3
import Lean
open Lean Meta IndependentLosslessExprDagV1
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
private def standard (n : Name) : MetaM (Array Name) := do
  let axioms ← collectAxioms n
  unless axioms.toList.all (fun a => ([`propext,`Classical.choice,`Quot.sound] : List Name).contains a) do
    throwError "Non-Std3 actual declaration: {n}"
  return axioms
private def closed (n : Name) (ty val : Expr) : MetaM Unit := do
  unless !(ty.hasFVar || ty.hasMVar || val.hasFVar || val.hasMVar) do throwError "Unclosed actual declaration: {n}"
private def full (n : Name) (kind : String) : MetaM Unit := do
  let info ← getConstInfo n
  let val ← match info with
    | .defnInfo actual => pure actual.value
    | .thmInfo actual => pure actual.value
    | .opaqueInfo actual => pure actual.value
    | _ => throwError "Expected actual definition/proof/opaque: {n}"
  closed n info.type val
  let axioms ← standard n
  let payload ← ofExcept (persistedRoundTrip info.type val)
  let (restoredType,restoredValue) ← ofExcept (decode payload)
  let typeKernel ← isDefEq info.type restoredType
  let valueKernel ← isDefEq val restoredValue
  unless typeKernel && valueKernel && Expr.equal info.type restoredType && Expr.equal val restoredValue do
    throwError "Lossless full SOURCE reconstruction failed: {n}"
  IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str n.toString),
    ("closed",toJson true),("axioms",toJson (axioms.toList.map Name.toString)),
    ("complete_type_and_value_expression_dag",payload),("full_type_raw_Expr",Json.str (reprStr info.type)),
    ("all_fields_Expr_equal_roundtrip",toJson true),("type_roundtrip_kernel_equal",toJson typeKernel),
    ("value_roundtrip_kernel_equal",toJson valueKernel)]).compress
private def wholeDefinition (actual expected : Name) : MetaM Unit := do
  let .defnInfo a ← getConstInfo actual | throwError "Actual definition kind differs"
  let .defnInfo e ← getConstInfo expected | throwError "Expected definition kind differs"
  let typeKernel ← isDefEq a.type e.type
  let valueKernel ← isDefEq a.value e.value
  unless typeKernel && valueKernel do throwError "Full type/value kernel mismatch: {actual}"
  IO.println (Json.mkObj [("kind",Json.str "independent_full_definition_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson typeKernel),("value_kernel_equal",toJson valueKernel),
    ("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("value_Expr_equal_diagnostic",toJson (Expr.equal a.value e.value)),
    ("full_actual_type_and_value_dag",← ofExcept (persistedRoundTrip a.type a.value)),
    ("full_expected_type_and_value_dag",← ofExcept (persistedRoundTrip e.type e.value))]).compress
private def wholeType (actual expected : Name) : MetaM Unit := do
  let a ← getConstInfo actual
  let e ← getConstInfo expected
  let same ← isDefEq a.type e.type
  unless same do throwError "Complete original forall type mismatch: {actual}"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_forall_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson same),("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("full_actual_type_raw_Expr",Json.str (reprStr a.type)),("full_expected_type_raw_Expr",Json.str (reprStr e.type))]).compress
private def internalHelpers (modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut found : List Name := []
  for (name,info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[index.toNat]? | continue
    if modules.contains moduleName && (name.isInternal || (privateToUserName? name).isSome || name.toString.endsWith ".eq_1") then
      found := name :: found
      full name "independent_generated_or_internal_helper"
  IO.println (Json.mkObj [("kind",Json.str "independent_actual_helper_inventory"),
    ("modules",toJson (modules.map Name.toString)),("names",toJson (found.map Name.toString))]).compress
run_meta do
'''

def save(module,text):
    path=p.PROJECT/(module+'.lean');assert not path.exists();path.write_text(text,encoding='utf-8')
    snap=p.OUT/path.name;snap.write_bytes(path.read_bytes())
    return dict(module=module,project_relative=path.name,source=p.bind(path),snapshot=p.bind(snap))

def main():
    sys.stdout.reconfigure(encoding='utf-8');author=p.load(p.AUTHOR/'author-audit.json');prep=p.load(p.OUT/'source-preparation.json')
    headers=author['original_exact_headers'];assert len(headers)==len(ARGUMENTS)==16
    definitions=[r['declaration'] for r in author['all_actual_complete_definition_records']];assert len(definitions)==18
    actual_prefix='ZetaNine.CoefficientMapFormalTransportOutputs.'
    actual_source=(p.AUTHOR/'OutputsVerifiedSource.lean').read_text(encoding='utf-8')
    expected='namespace OutputsIndependentExpected\n'
    for row,args in zip(headers,ARGUMENTS):
        assert actual_source.count(row['header']+' :=')+actual_source.count(row['header']+' :=\n')>=1
        expected+=row['header'].replace('theorem '+row['name'],'theorem expected_'+row['name'],1)+' := by\n  exact '+actual_prefix+row['name']+(' '+args if args else '')+'\n\n'
    expected+='end OutputsIndependentExpected\n'
    rfl='namespace OutputsIndependentWhole\n'+''.join('theorem whole_'+name.rsplit('.',1)[-1]+' : '+name+' = OutputsIndependentFormula.'+name.rsplit('.',1)[-1]+' := by rfl\n' for name in definitions)+'end OutputsIndependentWhole\n'
    assertions=save('OutputsIndependentAssertionsV1',PREFIX+FORMULAS+rfl+expected+BOUNDARIES)
    meta=HELPERS
    for row in headers:
        name=actual_prefix+row['name'];ex='OutputsIndependentExpected.expected_'+row['name']
        meta+='  full `'+name+' "independent_actual_original_forall"\n'
        meta+='  full `'+ex+' "independent_expected_original_forall"\n'
        meta+='  wholeType `'+name+' `'+ex+'\n'
    for name in definitions:
        ex='OutputsIndependentFormula.'+name.rsplit('.',1)[-1]
        meta+='  full `'+name+' "independent_actual_related_definition"\n'
        meta+='  full `'+ex+' "independent_expected_related_definition"\n'
        meta+='  wholeDefinition `'+name+' `'+ex+'\n'
        meta+='  full `OutputsIndependentWhole.whole_'+name.rsplit('.',1)[-1]+' "independent_whole_function_rfl"\n'
    meta+=''.join('  full `OutputsIndependentBoundary.'+n+' "independent_typed_boundary"\n' for n in BOUNDARY_NAMES)
    modules=[r['module'] for r in prep['native_sources']]+['OutputsIndependentAssertionsV1']
    meta+='  internalHelpers ['+', '.join('`'+n for n in modules)+']\n'
    audit=save('OutputsIndependentSemanticV1',meta)
    plan=dict(status='PURE_OWN_ORIGINAL_FORALL_CONCRETE_FORMULA_BOUNDARY_CONTROL_PREPARATION',
        assertions=assertions,semantic=audit,original_exact_headers=headers,original_headers_preserved=True,
        related_definition_names=definitions,boundary_names=BOUNDARY_NAMES,helper_modules=modules,
        complete_original_forall_pairs=16,complete_definition_type_value_pairs=18,whole_function_rfl=18,
        typed_boundaries=9,all_full_types_and_values_lossless_dag_roundtripped=True,
        raw_Expr_equal_is_an_honest_diagnostic_not_an_acceptance_requirement=True,
        required_acceptance='Actual SOURCE compiler, closed Std3, complete kernel isDefEq and whole-function rfl',
        finite_scope='finite B, five outputs, LEFT Gamma for all n>=1; excludes HasSum parameter17/J/height/irrationality',
        author_Expectation_SOURCE_or_mathematical_control_reused=False,independent_PASS_claimed=False)
    p.dump(p.OUT/'control-preparation.json',plan);print('Own16 complete original headers,18 formulas and full-function rfl,9 typed boundaries prepared.')
if __name__=='__main__':main()
