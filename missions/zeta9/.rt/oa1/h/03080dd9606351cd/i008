import missions.zeta9.formalization.CoefficientMapFormalTransportOutputs
import IndependentExprDagV3
import Lean
noncomputable section
open scoped BigOperators Matrix
open Finset Polynomial
open ZetaNine
open ZetaNine.HarmonicStability ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapFiniteSum
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapFormalTransportBounds
open ZetaNine.CoefficientMapFormalTransportOutputs

namespace OutputsAuthorExpected
theorem expected_weightedR_eval_one_zero (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) :
    weightedR n W 1 = 0 := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.weightedR_eval_one_zero n hn W

theorem expected_quartic_properMultiplier (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    ProperMultiplier n W := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.quartic_properMultiplier n W hW

theorem expected_weighted_boundary_sum_zero (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      weightedLocalCoefficient n j s W / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.weighted_boundary_sum_zero n hn W hW

theorem expected_remainder_boundary_sum_zero (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) :
    (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
      remainderCoefficient n j s q / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.remainder_boundary_sum_zero n hn q hq

theorem expected_sum_extendedOldCoefficient_harmonic (n s : ℕ) (P : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedOldCoefficient n j s P * harmonicPower s j) =
      ∑ j ∈ range (n + 1), weightedLocalCoefficient n j s P * harmonicPower s (j + 1) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedOldCoefficient_harmonic n s P

theorem expected_sum_extendedRemainderCoefficient_harmonic (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedRemainderCoefficient n j s q * harmonicPower s j) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q * harmonicPower s j := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedRemainderCoefficient_harmonic n s q

theorem expected_sum_previousRemainderCoefficient_harmonic (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), previousRemainderCoefficient n j s q * harmonicPower s j) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q * harmonicPower s (j + 1) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.sum_previousRemainderCoefficient_harmonic n s q

theorem expected_sum_harmonic_succ (N s : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range N, f j * harmonicPower s (j + 1)) =
      (∑ j ∈ range N, f j * harmonicPower s j) +
        ∑ j ∈ range N, f j / (((j + 1 : ℕ) : ℚ) ^ s) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.sum_harmonic_succ N s f

theorem expected_actual_chosen_harmonic_order_transport (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    (∑ j ∈ range (n + 3), weightedLocalCoefficient (n + 2) j s (X ^ r.val) * harmonicPower s j) =
      (∑ j ∈ range (n + 1), weightedLocalCoefficient n j s (connectionP n r) * harmonicPower s j) +
      (∑ j ∈ range (n + 1), weightedLocalCoefficient n j s (connectionP n r) /
        (((j + 1 : ℕ) : ℚ) ^ s)) -
      (∑ j ∈ range (n + 2), remainderCoefficient n j s (connectionQ n r) /
        (((j + 1 : ℕ) : ℚ) ^ s)) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_harmonic_order_transport n hn r s hs1 hs9

theorem expected_actual_chosen_constantTerm_correction (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r) -
      (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s (connectionP n r) / (((j + 1 : ℕ) : ℚ) ^ s)) +
      (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
        remainderCoefficient n j s (connectionQ n r) / (((j + 1 : ℕ) : ℚ) ^ s)) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_correction n hn r

theorem expected_actual_chosen_constantTerm_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport n hn r

theorem expected_actual_chosen_five_output_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    aggregate (n + 2) (X ^ r.val) = aggregate n (connectionP n r) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport n hn r

theorem expected_actual_chosen_Gamma_row_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    aggregate n (connectionP n r) = connectionGamma n r ᵥ* actualFMatrix n := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_Gamma_row_transport n hn r

theorem expected_actual_five_output_matrix_transport (n : ℕ) (hn : 1 ≤ n) :
    actualFMatrix (n + 2) = connectionGamma n * actualFMatrix n := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport n hn

theorem expected_n_one_five_output_transport (r : Fin 5) :
    aggregate 3 (X ^ r.val) = aggregate 1 (connectionP 1 r) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.n_one_five_output_transport r

theorem expected_n_one_matrix_transport :
    actualFMatrix 3 = connectionGamma 1 * actualFMatrix 1 := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.n_one_matrix_transport 

end OutputsAuthorExpected
open Lean Meta
set_option maxHeartbeats 0
set_option maxRecDepth 20000
run_meta do
  for (actual,expected) in [(`ZetaNine.CoefficientMapFormalTransportOutputs.weightedR_eval_one_zero, `OutputsAuthorExpected.expected_weightedR_eval_one_zero), (`ZetaNine.CoefficientMapFormalTransportOutputs.quartic_properMultiplier, `OutputsAuthorExpected.expected_quartic_properMultiplier), (`ZetaNine.CoefficientMapFormalTransportOutputs.weighted_boundary_sum_zero, `OutputsAuthorExpected.expected_weighted_boundary_sum_zero), (`ZetaNine.CoefficientMapFormalTransportOutputs.remainder_boundary_sum_zero, `OutputsAuthorExpected.expected_remainder_boundary_sum_zero), (`ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedOldCoefficient_harmonic, `OutputsAuthorExpected.expected_sum_extendedOldCoefficient_harmonic), (`ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedRemainderCoefficient_harmonic, `OutputsAuthorExpected.expected_sum_extendedRemainderCoefficient_harmonic), (`ZetaNine.CoefficientMapFormalTransportOutputs.sum_previousRemainderCoefficient_harmonic, `OutputsAuthorExpected.expected_sum_previousRemainderCoefficient_harmonic), (`ZetaNine.CoefficientMapFormalTransportOutputs.sum_harmonic_succ, `OutputsAuthorExpected.expected_sum_harmonic_succ), (`ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_harmonic_order_transport, `OutputsAuthorExpected.expected_actual_chosen_harmonic_order_transport), (`ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_correction, `OutputsAuthorExpected.expected_actual_chosen_constantTerm_correction), (`ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport, `OutputsAuthorExpected.expected_actual_chosen_constantTerm_transport), (`ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport, `OutputsAuthorExpected.expected_actual_chosen_five_output_transport), (`ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_Gamma_row_transport, `OutputsAuthorExpected.expected_actual_chosen_Gamma_row_transport), (`ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport, `OutputsAuthorExpected.expected_actual_five_output_matrix_transport), (`ZetaNine.CoefficientMapFormalTransportOutputs.n_one_five_output_transport, `OutputsAuthorExpected.expected_n_one_five_output_transport), (`ZetaNine.CoefficientMapFormalTransportOutputs.n_one_matrix_transport, `OutputsAuthorExpected.expected_n_one_matrix_transport)] do
    let .thmInfo a ← getConstInfo actual | throwError "Actual declaration is not a theorem: {actual}"
    let .thmInfo b ← getConstInfo expected | throwError "Expected declaration is not a theorem: {expected}"
    let same ← isDefEq a.type b.type
    unless same do throwError "Original complete type mismatch: {actual}"
    let aa ← collectAxioms actual
    let ba ← collectAxioms expected
    let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
    unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
      throwError "Nonstandard theorem axioms: {actual}"
    let sourceDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    let expectedDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_source_expected_type"),
      ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
      ("full_source_type_and_proof_expression_dag",sourceDag),
      ("full_expected_type_and_proof_expression_dag",expectedDag),
      ("all_fields_Expr_equal_roundtrip",toJson true),("type_kernel_equal",toJson same),
      ("source_axioms",toJson (aa.toList.map Name.toString)),
      ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
