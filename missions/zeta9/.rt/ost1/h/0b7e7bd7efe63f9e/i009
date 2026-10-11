import missions.zeta9.formalization.CoefficientMapParameterSummationTransport
import IndependentExprDagV3
import Lean
noncomputable section
open scoped BigOperators Matrix
open Polynomial
open ZetaNine
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportBounds ZetaNine.CoefficientMapFormalTransportOutputs
open ZetaNine.CoefficientMapParameterSummationTransport

namespace ParameterSummationAuthorExpected
theorem expected_transferMultiplier_natDegree_le (n : ℕ) (W : ℚ[X]) :
    (transferMultiplier n W).natDegree ≤ 4 := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier_natDegree_le n W

theorem expected_even_add_two (n : ℕ) (hn : Even n) : Even (n + 2) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.even_add_two n hn

theorem expected_exactL_eq_prescribed_actual_output (n : ℕ) (W : ℚ[X]) :
    exactL n W = prescribedL (aggregate n W) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.exactL_eq_prescribed_actual_output n W

theorem expected_transfer_actual_five_outputs (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    aggregate n (transferMultiplier n W) = aggregate (n + 2) W := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_five_outputs n hn W hW

theorem expected_transfer_actual_exactL (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    exactL n (transferMultiplier n W) = exactL (n + 2) W := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_exactL n hn W hW

theorem expected_quartic_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries n W) (exactL n W) ∧
      Summable (fun t : ℕ => ‖actualSeries n W t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.quartic_actual_HasSum_and_absolute n hn2 hn W hW

theorem expected_actual_chosen_exactL_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    exactL (n + 2) (X ^ r.val) = exactL n (connectionP n r) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_exactL_transport n hn r

theorem expected_actual_chosen_HasSum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (r : Fin 5) :
    HasSum (actualSeries (n + 2) (X ^ r.val)) (exactL n (connectionP n r)) ∧
      HasSum (actualSeries n (connectionP n r)) (exactL n (connectionP n r)) ∧
      Summable (fun t : ℕ => ‖actualSeries (n + 2) (X ^ r.val) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries n (connectionP n r) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_HasSum_transport n hn2 hn r

theorem expected_actual_chosen_tsum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (r : Fin 5) :
    (∑' t : ℕ, actualSeries (n + 2) (X ^ r.val) t) =
      ∑' t : ℕ, actualSeries n (connectionP n r) t := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_tsum_transport n hn2 hn r

theorem expected_quartic_HasSum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries (n + 2) W) (exactL (n + 2) W) ∧
      HasSum (actualSeries n (transferMultiplier n W)) (exactL (n + 2) W) ∧
      Summable (fun t : ℕ => ‖actualSeries (n + 2) W t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries n (transferMultiplier n W) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.quartic_HasSum_transport n hn2 hn W hW

theorem expected_quartic_tsum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    (∑' t : ℕ, actualSeries (n + 2) W t) =
      ∑' t : ℕ, actualSeries n (transferMultiplier n W) t := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.quartic_tsum_transport n hn2 hn W hW

theorem expected_transferred_inverseMultiplier_eq (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    transferMultiplier n (inverseMultiplier (n + 2) (by omega) (even_add_two n hn) b) =
      inverseMultiplier n hn2 hn b := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.transferred_inverseMultiplier_eq n hn2 hn b

theorem expected_inverseMultiplier_coordinates_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    polynomialCoordinates (inverseMultiplier (n + 2) (by omega) (even_add_two n hn) b)
        ᵥ* connectionGamma n = polynomialCoordinates (inverseMultiplier n hn2 hn b) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.inverseMultiplier_coordinates_transport n hn2 hn b

theorem expected_chosen_transferMultiplier_eq_connectionP (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (r : Fin 5) :
    transferMultiplier n (X ^ r.val) = connectionP n r := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.chosen_transferMultiplier_eq_connectionP n hn2 hn r

theorem expected_selectedIntegerMultiplier_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b a : ℤ) :
    transferMultiplier n
        (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a) =
      selectedIntegerMultiplier n hn2 hn b a := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_transport n hn2 hn b a

theorem expected_selectedIntegerMultiplier_parameter_HasSum (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    HasSum (actualSeries (n + 2)
        (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a))
      ((b : ℝ) + (a : ℝ) * zetaReal 9) ∧
      HasSum (actualSeries n (selectedIntegerMultiplier n hn2 hn b a))
        ((b : ℝ) + (a : ℝ) * zetaReal 9) ∧
      Summable (fun t : ℕ => ‖actualSeries (n + 2)
        (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries n (selectedIntegerMultiplier n hn2 hn b a) t‖) := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_HasSum n hn2 hn b a

theorem expected_selectedIntegerMultiplier_parameter_tsum (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    (∑' t : ℕ, actualSeries (n + 2)
      (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a) t) =
      ∑' t : ℕ, actualSeries n (selectedIntegerMultiplier n hn2 hn b a) t := by
  exact ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_tsum n hn2 hn b a

end ParameterSummationAuthorExpected
open Lean Meta
set_option maxHeartbeats 0
set_option maxRecDepth 20000
run_meta do
  for (actual,expected) in [(`ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier_natDegree_le, `ParameterSummationAuthorExpected.expected_transferMultiplier_natDegree_le), (`ZetaNine.CoefficientMapParameterSummationTransport.even_add_two, `ParameterSummationAuthorExpected.expected_even_add_two), (`ZetaNine.CoefficientMapParameterSummationTransport.exactL_eq_prescribed_actual_output, `ParameterSummationAuthorExpected.expected_exactL_eq_prescribed_actual_output), (`ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_five_outputs, `ParameterSummationAuthorExpected.expected_transfer_actual_five_outputs), (`ZetaNine.CoefficientMapParameterSummationTransport.transfer_actual_exactL, `ParameterSummationAuthorExpected.expected_transfer_actual_exactL), (`ZetaNine.CoefficientMapParameterSummationTransport.quartic_actual_HasSum_and_absolute, `ParameterSummationAuthorExpected.expected_quartic_actual_HasSum_and_absolute), (`ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_exactL_transport, `ParameterSummationAuthorExpected.expected_actual_chosen_exactL_transport), (`ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_HasSum_transport, `ParameterSummationAuthorExpected.expected_actual_chosen_HasSum_transport), (`ZetaNine.CoefficientMapParameterSummationTransport.actual_chosen_tsum_transport, `ParameterSummationAuthorExpected.expected_actual_chosen_tsum_transport), (`ZetaNine.CoefficientMapParameterSummationTransport.quartic_HasSum_transport, `ParameterSummationAuthorExpected.expected_quartic_HasSum_transport), (`ZetaNine.CoefficientMapParameterSummationTransport.quartic_tsum_transport, `ParameterSummationAuthorExpected.expected_quartic_tsum_transport), (`ZetaNine.CoefficientMapParameterSummationTransport.transferred_inverseMultiplier_eq, `ParameterSummationAuthorExpected.expected_transferred_inverseMultiplier_eq), (`ZetaNine.CoefficientMapParameterSummationTransport.inverseMultiplier_coordinates_transport, `ParameterSummationAuthorExpected.expected_inverseMultiplier_coordinates_transport), (`ZetaNine.CoefficientMapParameterSummationTransport.chosen_transferMultiplier_eq_connectionP, `ParameterSummationAuthorExpected.expected_chosen_transferMultiplier_eq_connectionP), (`ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_transport, `ParameterSummationAuthorExpected.expected_selectedIntegerMultiplier_transport), (`ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_HasSum, `ParameterSummationAuthorExpected.expected_selectedIntegerMultiplier_parameter_HasSum), (`ZetaNine.CoefficientMapParameterSummationTransport.selectedIntegerMultiplier_parameter_tsum, `ParameterSummationAuthorExpected.expected_selectedIntegerMultiplier_parameter_tsum)] do
    let .thmInfo a ← getConstInfo actual | throwError "Not a source theorem: {actual}"
    let .thmInfo b ← getConstInfo expected | throwError "Not an expected theorem: {expected}"
    let equal ← isDefEq a.type b.type
    unless equal do throwError "Complete expected type mismatch: {actual}"
    let aa ← collectAxioms actual
    let ba ← collectAxioms expected
    let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
    unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
      throwError "Nonstandard axiom: {actual}"
    let ad ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    let bd ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_source_expected_type"),
      ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
      ("full_source_type_and_proof_expression_dag",ad),
      ("full_expected_type_and_proof_expression_dag",bd),
      ("type_kernel_equal",toJson equal),("all_fields_Expr_equal_roundtrip",toJson true),
      ("source_axioms",toJson (aa.toList.map Name.toString)),
      ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
