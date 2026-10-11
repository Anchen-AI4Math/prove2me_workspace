import re,json,sys
import inspect_prepare as p
ARGS=['n W','n hn','n W','n hn W hW','n hn W hW','n hn2 hn W hW','n hn r','n hn2 hn r','n hn2 hn r','n hn2 hn W hW','n hn2 hn W hW','n hn2 hn b','n hn2 hn b','n hn2 hn r','n hn2 hn b a','n hn2 hn b a','n hn2 hn b a']
PREFIX='''import missions.zeta9.formalization.CoefficientMapParameterSummationTransport
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
noncomputable section
open scoped BigOperators Matrix
open Polynomial ZetaNine
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportBounds ZetaNine.CoefficientMapFormalTransportOutputs
open ZetaNine.CoefficientMapParameterSummationTransport
'''
FORMULA='''namespace ParameterSummationIndependentFormula
def transferMultiplier (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  coordinatePolynomial (fun l : Fin 5 => ∑ i : Fin 5,
    polynomialCoordinates W i * connectionGamma n i l)
end ParameterSummationIndependentFormula
namespace ParameterSummationIndependentWhole
theorem whole_transferMultiplier :
    ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier =
      ParameterSummationIndependentFormula.transferMultiplier := by rfl
end ParameterSummationIndependentWhole
'''
# Author boundary contract was read only to identify these nine required endpoint instantiations.
# Types below are independently instantiated from immutable original theorem headers.
BOUNDARIES=[('n1_exact_r0','actual_chosen_exactL_transport',{'n':'1','hn':'(by decide)','r':'(0 : Fin 5)'},'1 (by decide) (0 : Fin 5)'),('n2_HasSum_r0','actual_chosen_HasSum_transport',{'n':'2','hn2':'(by decide)','hn':'(by decide)','r':'(0 : Fin 5)'},'2 (by decide) (by decide) (0 : Fin 5)'),('n2_HasSum_r4','actual_chosen_HasSum_transport',{'n':'2','hn2':'(by decide)','hn':'(by decide)','r':'(4 : Fin 5)'},'2 (by decide) (by decide) (4 : Fin 5)'),('n2_tsum_r4','actual_chosen_tsum_transport',{'n':'2','hn2':'(by decide)','hn':'(by decide)','r':'(4 : Fin 5)'},'2 (by decide) (by decide) (4 : Fin 5)'),('n2_transfer_r0','chosen_transferMultiplier_eq_connectionP',{'n':'2','hn2':'(by decide)','hn':'(by decide)','r':'(0 : Fin 5)'},'2 (by decide) (by decide) (0 : Fin 5)'),('n2_transfer_r4','chosen_transferMultiplier_eq_connectionP',{'n':'2','hn2':'(by decide)','hn':'(by decide)','r':'(4 : Fin 5)'},'2 (by decide) (by decide) (4 : Fin 5)'),('n2_selected_B','selectedIntegerMultiplier_parameter_HasSum',{'n':'2','hn2':'(by decide)','hn':'(by decide)','b':'(1 : ℤ)','a':'(0 : ℤ)'},'2 (by decide) (by decide) (1 : ℤ) (0 : ℤ)'),('n2_selected_A','selectedIntegerMultiplier_parameter_HasSum',{'n':'2','hn2':'(by decide)','hn':'(by decide)','b':'(0 : ℤ)','a':'(1 : ℤ)'},'2 (by decide) (by decide) (0 : ℤ) (1 : ℤ)'),('n2_selected_tsum','selectedIntegerMultiplier_parameter_tsum',{'n':'2','hn2':'(by decide)','hn':'(by decide)','b':'(1 : ℤ)','a':'(1 : ℤ)'},'2 (by decide) (by decide) (1 : ℤ) (1 : ℤ)')]
META='''import ParameterSummationIndependentAssertionsV1
import IndependentExprDagV3
import Lean
open Lean Meta IndependentLosslessExprDagV1
set_option maxRecDepth 20000
set_option maxHeartbeats 0
private def standard (name : Name) : MetaM (Array Name) := do
  let axioms ← collectAxioms name
  unless axioms.toList.all (fun a => ([`propext,`Classical.choice,`Quot.sound] : List Name).contains a) do
    throwError "Non-Std3 actual declaration: {name}"
  return axioms
private def full (name : Name) (kind : String) : MetaM Unit := do
  let info ← getConstInfo name
  let value ← match info with
    | .thmInfo a => pure a.value
    | .defnInfo a => pure a.value
    | .opaqueInfo a => pure a.value
    | _ => throwError "Actual definition or proof value absent: {name}"
  unless !(info.type.hasFVar || info.type.hasMVar || value.hasFVar || value.hasMVar) do
    throwError "Actual complete type/value is not closed: {name}"
  let axioms ← standard name
  let inferred ← inferType value
  let typed ← isDefEq info.type inferred
  unless typed do throwError "Actual value inferType mismatch: {name}"
  let payload ← ofExcept (persistedRoundTrip info.type value)
  let (rt,rv) ← ofExcept (decode payload)
  let sameType ← isDefEq info.type rt
  let sameValue ← isDefEq value rv
  unless sameType && sameValue && Expr.equal info.type rt && Expr.equal value rv do
    throwError "Lossless whole type/value reconstruction mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str name.toString),
    ("axioms",toJson (axioms.toList.map Name.toString)),("closed_complete_type_and_value",toJson true),
    ("actual_value_inferType_kernel_equal",toJson typed),("actual_inferred_type_raw_Expr",Json.str (reprStr inferred)),
    ("full_type_raw_Expr",Json.str (reprStr info.type)),("complete_type_and_value_expression_dag",payload),
    ("all_fields_Expr_equal_roundtrip",toJson true),("type_roundtrip_kernel_equal",toJson sameType),
    ("value_roundtrip_kernel_equal",toJson sameValue)]).compress
  (← IO.getStdout).flush
private def wholeType (actual expected : Name) : MetaM Unit := do
  let a ← getConstInfo actual
  let e ← getConstInfo expected
  let same ← isDefEq a.type e.type
  unless same do throwError "Complete original forall kernel type differs: {actual}"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_forall_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson same),("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("full_actual_type_raw_Expr",Json.str (reprStr a.type)),("full_expected_type_raw_Expr",Json.str (reprStr e.type))]).compress
private def definitionKernel (actual expected : Name) : MetaM Unit := do
  let .defnInfo a ← getConstInfo actual | throwError "Expected actual definition"
  let .defnInfo e ← getConstInfo expected | throwError "Expected independently defined function"
  let sameType ← isDefEq a.type e.type
  let sameValue ← isDefEq a.value e.value
  unless sameType && sameValue do throwError "Complete actual definition type/value differs: {actual}"
  IO.println (Json.mkObj [("kind",Json.str "independent_full_definition_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson sameType),("value_kernel_equal",toJson sameValue),
    ("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("value_Expr_equal_diagnostic",toJson (Expr.equal a.value e.value)),
    ("full_actual_type_and_value_dag",← ofExcept (persistedRoundTrip a.type a.value)),
    ("full_expected_type_and_value_dag",← ofExcept (persistedRoundTrip e.type e.value))]).compress
'''
GENERATED='''private def completeActualModuleInventory (modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut allNames : List Name := []
  let mut helpers : List Name := []
  for (name,info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[index.toNat]? | continue
    if modules.contains moduleName then
      let axioms ← standard name
      unless !(info.type.hasFVar || info.type.hasMVar) do throwError "Unclosed actual declaration type: {name}"
      allNames := name :: allNames
      IO.println (Json.mkObj [("kind",Json.str "independent_all_actual_declaration_Std3"),
        ("declaration",Json.str name.toString),("module",Json.str moduleName.toString),
        ("axioms",toJson (axioms.toList.map Name.toString)),("closed_complete_type",toJson true)]).compress
      if name.isInternalDetail || (privateToUserName? name).isSome then
        helpers := name :: helpers
        full name "independent_all_generated_complete_type_and_value"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_generated_closure_inventory"),
    ("modules",toJson (modules.map Name.toString)),("all_declarations",toJson (allNames.map Name.toString)),
    ("all_generated_helpers",toJson (helpers.map Name.toString)),
    ("predicate",Json.str "isInternalDetail or actual privateToUserName; covers every public eq_N/match_N/proof_N/omega_N, internal and numbered helper")]).compress
'''
def save(module,text):
 path=p.PROJECT/(module+'.lean');assert not path.exists();path.write_text(text,encoding='utf-8')
 snapshot=p.OUT/path.name;assert not snapshot.exists();snapshot.write_bytes(path.read_bytes())
 return dict(module=module,project_relative=path.name,source=p.bind(path),snapshot=p.bind(snapshot))
def main():
 sys.stdout.reconfigure(encoding='utf-8')
 prep=p.load(p.OUT/'source-preparation.json');headers=prep['original_complete_headers'];assert len(headers)==len(ARGS)==17
 source=(p.TASK/'formalization/CoefficientMapParameterSummationTransport.lean').read_text(encoding='utf-8-sig')
 assert p.sha(p.TASK/'formalization/CoefficientMapParameterSummationTransport.lean')==p.SOURCE_SHA
 expected='namespace ParameterSummationIndependentExpected\n'
 for row,args in zip(headers,ARGS):
  assert source.count(row['header']+' :=')==1
  expected+=row['header'].replace('theorem '+row['name'],'theorem expected_'+row['name'],1)+' := by\n  exact ZetaNine.CoefficientMapParameterSummationTransport.'+row['name']+' '+args+'\n\n'
 expected+='end ParameterSummationIndependentExpected\n'
 byname={x['name']:x['header'] for x in headers};bound='namespace ParameterSummationIndependentBoundary\n'
 for name,endpoint,sub,args in BOUNDARIES:
  header=byname[endpoint];assert header.count(' :\n')==1
  ty=header.split(' :\n')[1]
  for key,value in sub.items():ty=re.sub(r'\b'+key+r'\b',value,ty)
  bound+='theorem '+name+' :\n'+ty+' := by\n  exact ZetaNine.CoefficientMapParameterSummationTransport.'+endpoint+' '+args+'\n\n'
 bound+='end ParameterSummationIndependentBoundary\n'
 assertion=save('ParameterSummationIndependentAssertionsV1',PREFIX+FORMULA+expected+bound)
 semantic=META+'run_meta do\n'
 for row in headers:
  actual='ZetaNine.CoefficientMapParameterSummationTransport.'+row['name'];ex='ParameterSummationIndependentExpected.expected_'+row['name']
  semantic+='  full `'+actual+' "independent_actual_original_forall"\n  full `'+ex+' "independent_expected_original_forall"\n  wholeType `'+actual+' `'+ex+'\n'
 semantic+='  full `ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier "independent_actual_related_definition"\n  full `ParameterSummationIndependentFormula.transferMultiplier "independent_expected_related_definition"\n  definitionKernel `ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier `ParameterSummationIndependentFormula.transferMultiplier\n  full `ParameterSummationIndependentWhole.whole_transferMultiplier "independent_whole_function_rfl"\n'
 for name,_,_,_ in BOUNDARIES:semantic+='  full `ParameterSummationIndependentBoundary.'+name+' "independent_typed_boundary"\n'
 sem=save('ParameterSummationIndependentSemanticV1',semantic)
 modules=[x['module'] for x in prep['native_sources']]+[assertion['module']]
 gen=save('ParameterSummationIndependentGeneratedV1',META+GENERATED+'run_meta do\n  completeActualModuleInventory ['+', '.join('`'+x for x in modules)+']\n')
 p.dump(p.OUT/'control-preparation.json',dict(assertions=assertion,semantic=sem,generated=gen,original_complete_headers=headers,helper_modules=modules,boundary_names=[x[0] for x in BOUNDARIES],whole_definition_names=['ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier'],literal_original_headers_preserved=True,original_definition_value_expected_by_independent_explicit_finite_sum=True,whole_function_rfl_required=True,all_native_generated_helpers_complete_type_value_and_value_inferType_required=True,author_control_SOURCE_or_proof_objects_reused=False,author_boundary_contract_consulted_only_for_nine_endpoint_instantiations=True,independent_PASS_claimed=False))
 print('Own17 complete original headers, independent explicit-sum definition+rfl,9 original endpoints, full generated values/inferType prepared.')
if __name__=='__main__':main()
