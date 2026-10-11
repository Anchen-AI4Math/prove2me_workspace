import missions.zeta9.formalization.CoefficientMapFormalTransportOutputs
import IndependentExprDagV3
import Lean
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine
open ZetaNine.HarmonicStability ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapFiniteSum
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapFormalTransportBounds
open ZetaNine.CoefficientMapFormalTransportOutputs

namespace OutputsAuthorBoundary
theorem n_one_B (r : Fin 5) :
    constantTerm 3 (X ^ r.val) = constantTerm 1 (connectionP 1 r) := by
  exact actual_chosen_constantTerm_transport 1 (by decide) r

theorem n_one_all_five (r : Fin 5) :
    aggregate 3 (X ^ r.val) = aggregate 1 (connectionP 1 r) := by
  exact actual_chosen_five_output_transport 1 (by decide) r

theorem n_one_F : actualFMatrix 3 = connectionGamma 1 * actualFMatrix 1 := by
  exact actual_five_output_matrix_transport 1 (by decide)

theorem n_two_F : actualFMatrix 4 = connectionGamma 2 * actualFMatrix 2 := by
  exact actual_five_output_matrix_transport 2 (by decide)

theorem n_three_F : actualFMatrix 5 = connectionGamma 3 * actualFMatrix 3 := by
  exact actual_five_output_matrix_transport 3 (by decide)

theorem n_one_arbitrary_remainder (q : ℚ[X]) (hq : q.natDegree ≤ 9) :
    (∑ j ∈ range 3, ∑ s ∈ Icc 1 9,
      remainderCoefficient 1 j s q / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 := by
  exact remainder_boundary_sum_zero 1 (by decide) q hq

theorem n_zero_weighted_boundary_counterexample : weightedR 0 (1 : ℚ[X]) 1 = 1 := by
  norm_num [weightedR, actualR, numerator, poleProduct]

theorem empty_harmonic_successor (s : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range 0, f j * harmonicPower s (j + 1)) = 0 := by
  simp

theorem n_one_B_correction (r : Fin 5) :
    constantTerm 3 (X ^ r.val) = constantTerm 1 (connectionP 1 r) -
      (∑ j ∈ range 2, ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient 1 j s (connectionP 1 r) / (((j + 1 : ℕ) : ℚ) ^ s)) +
      (∑ j ∈ range 3, ∑ s ∈ Icc 1 9,
        remainderCoefficient 1 j s (connectionQ 1 r) / (((j + 1 : ℕ) : ℚ) ^ s)) := by
  exact actual_chosen_constantTerm_correction 1 (by decide) r

end OutputsAuthorBoundary
open Lean Meta
set_option maxHeartbeats 0
run_meta do
  for actual in [`OutputsAuthorBoundary.n_one_B, `OutputsAuthorBoundary.n_one_all_five, `OutputsAuthorBoundary.n_one_F, `OutputsAuthorBoundary.n_two_F, `OutputsAuthorBoundary.n_three_F, `OutputsAuthorBoundary.n_one_arbitrary_remainder, `OutputsAuthorBoundary.n_zero_weighted_boundary_counterexample, `OutputsAuthorBoundary.empty_harmonic_successor, `OutputsAuthorBoundary.n_one_B_correction] do
    let .thmInfo a ← getConstInfo actual | throwError "Boundary declaration is not a theorem"
    let aa ← collectAxioms actual
    unless aa.toList.all (fun n => [`propext,`Classical.choice,`Quot.sound].contains n) do
      throwError "Nonstandard boundary axioms"
    let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_closed_boundary"),
      ("declaration",Json.str actual.toString),("complete_type_and_proof_expression_dag",payload),
      ("all_fields_Expr_equal_roundtrip",toJson true),
      ("axioms",toJson (aa.toList.map Name.toString))]).compress
