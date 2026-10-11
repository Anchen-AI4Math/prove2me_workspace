import ParameterSummationIndependentAssertionsV1
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
run_meta do
  full `ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier_natDegree_le "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_transferMultiplier_natDegree_le "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier_natDegree_le `ParameterSummationIndependentExpected.expected_transferMultiplier_natDegree_le
  full `ZetaNine.CoefficientMapParameterSummationTransport.even_add_two "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_even_add_two "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.even_add_two `ParameterSummationIndependentExpected.expected_even_add_two
  full `ZetaNine.CoefficientMapParameterSummationTransport.exactL_eq_prescribed_actual_output "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_exactL_eq_prescribed_actual_output "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.exactL_eq_prescribed_actual_output `ParameterSummationIndependentExpected.expected_exactL_eq_prescribed_actual_output
  full `ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_five_outputs "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_transfer_actual_five_outputs "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_five_outputs `ParameterSummationIndependentExpected.expected_transfer_actual_five_outputs
  full `ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_exactL "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_transfer_actual_exactL "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_exactL `ParameterSummationIndependentExpected.expected_transfer_actual_exactL
  full `ZetaNine.CoefficientMapParameterSummationTransport.quartic_actual_HasSum_and_absolute "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_quartic_actual_HasSum_and_absolute "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.quartic_actual_HasSum_and_absolute `ParameterSummationIndependentExpected.expected_quartic_actual_HasSum_and_absolute
  full `ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_exactL_transport "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_actual_chosen_exactL_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_exactL_transport `ParameterSummationIndependentExpected.expected_actual_chosen_exactL_transport
  full `ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_HasSum_transport "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_actual_chosen_HasSum_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_HasSum_transport `ParameterSummationIndependentExpected.expected_actual_chosen_HasSum_transport
  full `ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_tsum_transport "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_actual_chosen_tsum_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_tsum_transport `ParameterSummationIndependentExpected.expected_actual_chosen_tsum_transport
  full `ZetaNine.CoefficientMapParameterSummationTransport.quartic_HasSum_transport "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_quartic_HasSum_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.quartic_HasSum_transport `ParameterSummationIndependentExpected.expected_quartic_HasSum_transport
  full `ZetaNine.CoefficientMapParameterSummationTransport.quartic_tsum_transport "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_quartic_tsum_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.quartic_tsum_transport `ParameterSummationIndependentExpected.expected_quartic_tsum_transport
  full `ZetaNine.CoefficientMapParameterSummationTransport.transferred_inverseMultiplier_eq "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_transferred_inverseMultiplier_eq "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.transferred_inverseMultiplier_eq `ParameterSummationIndependentExpected.expected_transferred_inverseMultiplier_eq
  full `ZetaNine.CoefficientMapParameterSummationTransport.inverseMultiplier_coordinates_transport "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_inverseMultiplier_coordinates_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.inverseMultiplier_coordinates_transport `ParameterSummationIndependentExpected.expected_inverseMultiplier_coordinates_transport
  full `ZetaNine.CoefficientMapParameterSummationTransport.chosen_transferMultiplier_eq_connectionP "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_chosen_transferMultiplier_eq_connectionP "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.chosen_transferMultiplier_eq_connectionP `ParameterSummationIndependentExpected.expected_chosen_transferMultiplier_eq_connectionP
  full `ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_transport "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_selectedIntegerMultiplier_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_transport `ParameterSummationIndependentExpected.expected_selectedIntegerMultiplier_transport
  full `ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_HasSum "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_selectedIntegerMultiplier_parameter_HasSum "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_HasSum `ParameterSummationIndependentExpected.expected_selectedIntegerMultiplier_parameter_HasSum
  full `ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_tsum "independent_actual_original_forall"
  full `ParameterSummationIndependentExpected.expected_selectedIntegerMultiplier_parameter_tsum "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_tsum `ParameterSummationIndependentExpected.expected_selectedIntegerMultiplier_parameter_tsum
  full `ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier "independent_actual_related_definition"
  full `ParameterSummationIndependentFormula.transferMultiplier "independent_expected_related_definition"
  definitionKernel `ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier `ParameterSummationIndependentFormula.transferMultiplier
  full `ParameterSummationIndependentWhole.whole_transferMultiplier "independent_whole_function_rfl"
  full `ParameterSummationIndependentBoundary.n1_exact_r0 "independent_typed_boundary"
  full `ParameterSummationIndependentBoundary.n2_HasSum_r0 "independent_typed_boundary"
  full `ParameterSummationIndependentBoundary.n2_HasSum_r4 "independent_typed_boundary"
  full `ParameterSummationIndependentBoundary.n2_tsum_r4 "independent_typed_boundary"
  full `ParameterSummationIndependentBoundary.n2_transfer_r0 "independent_typed_boundary"
  full `ParameterSummationIndependentBoundary.n2_transfer_r4 "independent_typed_boundary"
  full `ParameterSummationIndependentBoundary.n2_selected_B "independent_typed_boundary"
  full `ParameterSummationIndependentBoundary.n2_selected_A "independent_typed_boundary"
  full `ParameterSummationIndependentBoundary.n2_selected_tsum "independent_typed_boundary"
