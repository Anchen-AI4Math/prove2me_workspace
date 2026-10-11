import missions.zeta9.formalization.CoefficientMapFormalTransportJets
import IndependentExprDagV3
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000
noncomputable section
open scoped BigOperators
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportNumerators
open ZetaNine.CoefficientMapNumeratorPartialFractions
open ZetaNine.CoefficientMapFormalTransportJets

namespace JetsIndependentBoundary

theorem upper_new_right_zero (m s : ℕ) (A : ℚ[X]) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    numeratorLocalCoefficient (m + 1) (m + 1) s
      ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) = 0 := by
  simpa using upper_all_actual_jets m (m + 1) s A (le_refl _) h1 h9

theorem lower_new_left_zero (m s : ℕ) (A : ℚ[X]) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    numeratorLocalCoefficient (m + 1) 0 s (X ^ 9 * A.comp (X + 1)) = 0 := by
  simpa using lower_all_actual_jets m 0 s A (by omega) h1 h9

theorem double_left_zero (n s : ℕ) (A : ℚ[X]) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    numeratorLocalCoefficient (n + 2) 0 s
      (X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1)) = 0 := by
  simpa using double_all_actual_jets n 0 s A (by omega) h1 h9

theorem double_right_zero (n s : ℕ) (A : ℚ[X]) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    numeratorLocalCoefficient (n + 2) (n + 2) s
      (X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1)) = 0 := by
  simpa using double_all_actual_jets n (n + 2) s A (le_refl _) h1 h9

theorem double_all_interior (n j s : ℕ) (A : ℚ[X])
    (hj1 : 1 ≤ j) (hjN : j ≤ n + 1) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    numeratorLocalCoefficient (n + 2) j s
      (X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1)) =
        numeratorLocalCoefficient n (j - 1) s A := by
  simpa [hj1, hjN] using double_all_actual_jets n j s A (by omega) h1 h9

theorem m0_upper_whole_series (A : ℚ[X]) :
    numeratorClearedSeries 1 0 ((X + 1) ^ 9 * A) = numeratorClearedSeries 0 0 A := by
  simpa using upper_whole_actual_series 0 0 A (le_refl _)

theorem m0_lower_whole_series (A : ℚ[X]) :
    numeratorClearedSeries 1 1 (X ^ 9 * A.comp (X + 1)) = numeratorClearedSeries 0 0 A := by
  simpa using lower_whole_actual_series 0 1 A (le_refl _) (le_refl _)

theorem upper_order_one (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m + 1) :
    numeratorLocalCoefficient (m + 1) j 1 ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
      if j ≤ m then numeratorLocalCoefficient m j 1 A else 0 := by
  exact upper_all_actual_jets m j 1 A hj (le_refl _) (by norm_num)

theorem lower_order_nine (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m + 1) :
    numeratorLocalCoefficient (m + 1) j 9 (X ^ 9 * A.comp (X + 1)) =
      if j = 0 then 0 else numeratorLocalCoefficient m (j - 1) 9 A := by
  exact lower_all_actual_jets m j 9 A hj (by norm_num) (le_refl _)

theorem m0_arbitrary_improper_multiple (B : ℚ[X]) (s : ℕ) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    numeratorLocalCoefficient 0 0 s ((X : ℚ[X]) ^ 9 * B) = 0 := by
  apply local_zero_of_shift_X_nine 0 0 s (X ^ 9 * B) h1 h9
  refine ⟨B, ?_⟩
  simp [shiftedVariable]

theorem n1_all_local_orders_rows (r : Fin 5) (j s : ℕ)
    (hj : j ≤ 3) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    weightedLocalCoefficient 3 j s (X ^ r.val) =
      extendedOldCoefficient 1 j s (connectionP 1 r) +
      extendedRemainderCoefficient 1 j s (connectionQ 1 r) -
      previousRemainderCoefficient 1 j s (connectionQ 1 r) := by
  simpa using actual_chosen_all_local_coefficients_transport 1 (le_refl _) r j s hj h1 h9

theorem n1_left_order_one (r : Fin 5) :
    weightedLocalCoefficient 3 0 1 (X ^ r.val) = remainderCoefficient 1 0 1 (connectionQ 1 r) := by
  simpa using actual_chosen_left_boundary_coefficient 1 (le_refl _) r 1 (le_refl _) (by norm_num)

theorem n1_left_order_nine (r : Fin 5) :
    weightedLocalCoefficient 3 0 9 (X ^ r.val) = remainderCoefficient 1 0 9 (connectionQ 1 r) := by
  simpa using actual_chosen_left_boundary_coefficient 1 (le_refl _) r 9 (by norm_num) (le_refl _)

theorem n1_right_order_one (r : Fin 5) :
    weightedLocalCoefficient 3 3 1 (X ^ r.val) = -remainderCoefficient 1 2 1 (connectionQ 1 r) := by
  simpa using actual_chosen_right_boundary_coefficient 1 (le_refl _) r 1 (le_refl _) (by norm_num)

theorem n1_right_order_nine (r : Fin 5) :
    weightedLocalCoefficient 3 3 9 (X ^ r.val) = -remainderCoefficient 1 2 9 (connectionQ 1 r) := by
  simpa using actual_chosen_right_boundary_coefficient 1 (le_refl _) r 9 (by norm_num) (le_refl _)

theorem n1_rho_one (r : Fin 5) :
    CoefficientMapFiniteSum.rho 3 1 (X ^ r.val) =
      CoefficientMapFiniteSum.rho 1 1 (connectionP 1 r) := by
  simpa using actual_chosen_all_rho_transport 1 (le_refl _) r 1 (le_refl _) (by norm_num)

theorem n1_rho_nine (r : Fin 5) :
    CoefficientMapFiniteSum.rho 3 9 (X ^ r.val) =
      CoefficientMapFiniteSum.rho 1 9 (connectionP 1 r) := by
  simpa using actual_chosen_all_rho_transport 1 (le_refl _) r 9 (by norm_num) (le_refl _)

theorem n1_all_nine_rhos (r : Fin 5) (s : ℕ) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    CoefficientMapFiniteSum.rho 3 s (X ^ r.val) =
      CoefficientMapFiniteSum.rho 1 s (connectionP 1 r) := by
  simpa using actual_chosen_all_rho_transport 1 (le_refl _) r s h1 h9

theorem n2_left_all_orders (r : Fin 5) (s : ℕ) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    weightedLocalCoefficient 4 0 s (X ^ r.val) = remainderCoefficient 2 0 s (connectionQ 2 r) := by
  simpa using actual_chosen_left_boundary_coefficient 2 (by norm_num) r s h1 h9

theorem n3_odd_all_rhos (r : Fin 5) (s : ℕ) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    CoefficientMapFiniteSum.rho 5 s (X ^ r.val) =
      CoefficientMapFiniteSum.rho 3 s (connectionP 3 r) := by
  simpa using actual_chosen_all_rho_transport 3 (by norm_num) r s h1 h9

theorem n0_upper_padding (f : ℕ → ℚ) :
    (∑ j ∈ range 2, if j ≤ 0 then f j else 0) = ∑ j ∈ range 1, f j := by
  simpa using sum_upper_zero_extension 0 f

theorem n0_lower_padding (f : ℕ → ℚ) :
    (∑ j ∈ range 2, if j = 0 then 0 else f (j - 1)) = ∑ j ∈ range 1, f j := by
  simpa using sum_lower_zero_extension 0 f

theorem arbitrary_negative_scalar (m j s : ℕ) (A : ℚ[X]) :
    numeratorLocalCoefficient m j s ((-3 : ℚ) • A) =
      (-3 : ℚ) * numeratorLocalCoefficient m j s A := by
  exact numeratorLocalCoefficient_smul m j s (-3) A

theorem arbitrary_order_linearity (m j s : ℕ) (A B : ℚ[X]) :
    numeratorLocalCoefficient m j s (A + B) =
      numeratorLocalCoefficient m j s A + numeratorLocalCoefficient m j s B := by
  exact numeratorLocalCoefficient_add m j s A B

theorem remainder_padding_cancellation (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedRemainderCoefficient n j s q) -
      (∑ j ∈ range (n + 3), previousRemainderCoefficient n j s q) = 0 := by
  rw [sum_extendedRemainderCoefficient, sum_previousRemainderCoefficient, sub_self]

theorem n1_signed_endpoint_pair (r : Fin 5) (s : ℕ) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    weightedLocalCoefficient 3 0 s (X ^ r.val) = remainderCoefficient 1 0 s (connectionQ 1 r) ∧
    weightedLocalCoefficient 3 3 s (X ^ r.val) = -remainderCoefficient 1 2 s (connectionQ 1 r) := by
  constructor
  · simpa using actual_chosen_left_boundary_coefficient 1 (le_refl _) r s h1 h9
  · simpa using actual_chosen_right_boundary_coefficient 1 (le_refl _) r s h1 h9

theorem n1_row_zero_all_orders (j s : ℕ) (hj : j ≤ 3) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    weightedLocalCoefficient 3 j s (X ^ (0 : Fin 5).val) =
      extendedOldCoefficient 1 j s (connectionP 1 (0 : Fin 5)) +
      extendedRemainderCoefficient 1 j s (connectionQ 1 (0 : Fin 5)) -
      previousRemainderCoefficient 1 j s (connectionQ 1 (0 : Fin 5)) := by
  exact n1_all_local_orders_rows (0 : Fin 5) j s hj h1 h9

theorem n1_row_four_all_rhos (s : ℕ) (h1 : 1 ≤ s) (h9 : s ≤ 9) :
    CoefficientMapFiniteSum.rho 3 s (X ^ (4 : Fin 5).val) =
      CoefficientMapFiniteSum.rho 1 s (connectionP 1 (4 : Fin 5)) := by
  exact n1_all_nine_rhos (4 : Fin 5) s h1 h9

-- These are exact scope boundaries, not claimed counterexamples to transport.
theorem chosen_n0_excluded : ¬ ((1 : ℕ) ≤ 0) := by decide
theorem jet_order_ten_excluded : ¬ ((10 : ℕ) ≤ 9) := by decide
theorem n1_pole_four_excluded : ¬ ((4 : ℕ) ≤ 3) := by decide

end JetsIndependentBoundary

open Lean Meta
run_meta do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if (`JetsIndependentBoundary).isPrefixOf name then
      let .thmInfo a := ci | throwError "Boundary is not theorem: {name}"
      unless !(a.type.hasMVar || a.type.hasFVar || a.value.hasMVar || a.value.hasFVar) do
        throwError "Unclosed boundary: {name}"
      let axs ← Lean.collectAxioms name
      unless axs.toList.all (fun n => ([`propext, `Classical.choice, `Quot.sound] : List Name).contains n) do
        throwError "Unexpected boundary axiom: {name}"
      let dag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
      IO.println (Json.mkObj [("kind", Json.str "independent_closed_boundary"),
        ("declaration", Json.str name.toString), ("closed", toJson true),
        ("axioms", toJson (axs.toList.map Name.toString)), ("complete_type_proof_DAG", dag)]).compress
      count := count + 1
  unless count == 31 do throwError "Expected 31 own boundary proofs, got {count}"
