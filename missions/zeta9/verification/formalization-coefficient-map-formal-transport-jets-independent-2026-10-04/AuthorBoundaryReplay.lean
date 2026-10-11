import missions.zeta9.formalization.CoefficientMapFormalTransportJets
import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportJets

namespace JetsAuthorBoundary

theorem n1_all_actual_jets (r : Fin 5) (j s : ℕ) (hj : j ≤ 3)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient 3 j s (X ^ r.val) =
      extendedOldCoefficient 1 j s (connectionP 1 r) +
        extendedRemainderCoefficient 1 j s (connectionQ 1 r) -
        previousRemainderCoefficient 1 j s (connectionQ 1 r) := by
  simpa using actual_chosen_all_local_coefficients_transport 1 (by norm_num) r j s hj hs1 hs9

theorem n1_left_endpoint (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient 3 0 s (X ^ r.val) = remainderCoefficient 1 0 s (connectionQ 1 r) := by
  simpa using actual_chosen_left_boundary_coefficient 1 (by norm_num) r s hs1 hs9

theorem n1_right_endpoint (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient 3 3 s (X ^ r.val) = -remainderCoefficient 1 2 s (connectionQ 1 r) := by
  simpa using actual_chosen_right_boundary_coefficient 1 (by norm_num) r s hs1 hs9

theorem n1_all_rho (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    ZetaNine.CoefficientMapFiniteSum.rho 3 s (X ^ r.val) =
      ZetaNine.CoefficientMapFiniteSum.rho 1 s (connectionP 1 r) := by
  simpa using actual_chosen_all_rho_transport 1 (by norm_num) r s hs1 hs9

theorem n2_right_endpoint (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient 4 4 s (X ^ r.val) = -remainderCoefficient 2 3 s (connectionQ 2 r) := by
  simpa using actual_chosen_right_boundary_coefficient 2 (by norm_num) r s hs1 hs9

theorem n2_four_requested_rhos (r : Fin 5) :
    ZetaNine.CoefficientMapFiniteSum.rho 4 3 (X ^ r.val) =
      ZetaNine.CoefficientMapFiniteSum.rho 2 3 (connectionP 2 r) ∧
    ZetaNine.CoefficientMapFiniteSum.rho 4 5 (X ^ r.val) =
      ZetaNine.CoefficientMapFiniteSum.rho 2 5 (connectionP 2 r) ∧
    ZetaNine.CoefficientMapFiniteSum.rho 4 7 (X ^ r.val) =
      ZetaNine.CoefficientMapFiniteSum.rho 2 7 (connectionP 2 r) ∧
    ZetaNine.CoefficientMapFiniteSum.rho 4 9 (X ^ r.val) =
      ZetaNine.CoefficientMapFiniteSum.rho 2 9 (connectionP 2 r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using actual_chosen_all_rho_transport 2 (by norm_num) r 3 (by norm_num) (by norm_num)
  · simpa using actual_chosen_all_rho_transport 2 (by norm_num) r 5 (by norm_num) (by norm_num)
  · simpa using actual_chosen_all_rho_transport 2 (by norm_num) r 7 (by norm_num) (by norm_num)
  · simpa using actual_chosen_all_rho_transport 2 (by norm_num) r 9 (by norm_num) (by norm_num)

theorem m0_upper_left_arbitrary (A : ℚ[X]) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient 1 0 s ((X + 1) ^ 9 * A) = numeratorLocalCoefficient 0 0 s A := by
  simpa using upper_all_actual_jets 0 0 s A (by norm_num) hs1 hs9

theorem m0_upper_right_arbitrary (A : ℚ[X]) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient 1 1 s ((X + 1) ^ 9 * A) = 0 := by
  simpa using upper_all_actual_jets 0 1 s A (by norm_num) hs1 hs9

theorem m0_lower_left_arbitrary (A : ℚ[X]) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient 1 0 s (X ^ 9 * A.comp (X + 1)) = 0 := by
  simpa using lower_all_actual_jets 0 0 s A (by norm_num) hs1 hs9

theorem m0_lower_right_arbitrary (A : ℚ[X]) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient 1 1 s (X ^ 9 * A.comp (X + 1)) = numeratorLocalCoefficient 0 0 s A := by
  simpa using lower_all_actual_jets 0 1 s A (by norm_num) hs1 hs9

theorem m0_double_left_arbitrary (A : ℚ[X]) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient 2 0 s (X ^ 9 * (X + C (2 : ℚ)) ^ 9 * A.comp (X + 1)) = 0 := by
  simpa using double_all_actual_jets 0 0 s A (by norm_num) hs1 hs9

theorem m0_double_middle_arbitrary (A : ℚ[X]) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient 2 1 s (X ^ 9 * (X + C (2 : ℚ)) ^ 9 * A.comp (X + 1)) =
      numeratorLocalCoefficient 0 0 s A := by
  simpa using double_all_actual_jets 0 1 s A (by norm_num) hs1 hs9

theorem m0_double_right_arbitrary (A : ℚ[X]) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient 2 2 s (X ^ 9 * (X + C (2 : ℚ)) ^ 9 * A.comp (X + 1)) = 0 := by
  simpa using double_all_actual_jets 0 2 s A (by norm_num) hs1 hs9

theorem m0_improper_X9_nine_jets (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient 0 0 s (X ^ 9 : ℚ[X]) = 0 := by
  apply local_zero_of_shift_X_nine 0 0 s (X ^ 9) hs1 hs9
  refine ⟨1, ?_⟩
  simp [shiftedVariable]

theorem any_n_highest_order (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) (j : ℕ) (hj : j ≤ n + 2) :
    weightedLocalCoefficient (n + 2) j 9 (X ^ r.val) =
      extendedOldCoefficient n j 9 (connectionP n r) +
        extendedRemainderCoefficient n j 9 (connectionQ n r) -
        previousRemainderCoefficient n j 9 (connectionQ n r) := by
  exact actual_chosen_all_local_coefficients_transport n hn r j 9 hj (by norm_num) (le_refl _)

end JetsAuthorBoundary

open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  for name in [
    `JetsAuthorBoundary.n1_all_actual_jets, `JetsAuthorBoundary.n1_left_endpoint,
    `JetsAuthorBoundary.n1_right_endpoint, `JetsAuthorBoundary.n1_all_rho,
    `JetsAuthorBoundary.n2_right_endpoint, `JetsAuthorBoundary.n2_four_requested_rhos,
    `JetsAuthorBoundary.m0_upper_left_arbitrary, `JetsAuthorBoundary.m0_upper_right_arbitrary,
    `JetsAuthorBoundary.m0_lower_left_arbitrary, `JetsAuthorBoundary.m0_lower_right_arbitrary,
    `JetsAuthorBoundary.m0_double_left_arbitrary, `JetsAuthorBoundary.m0_double_middle_arbitrary,
    `JetsAuthorBoundary.m0_double_right_arbitrary, `JetsAuthorBoundary.m0_improper_X9_nine_jets,
    `JetsAuthorBoundary.any_n_highest_order] do
    let .thmInfo ci ← getConstInfo name | throwError "Not an actual closed boundary theorem: {name}"
    let axs ← Lean.collectAxioms name
    unless axs.toList.all (fun n => ([`propext, `Classical.choice, `Quot.sound] : List Name).contains n) do
      throwError "Unexpected boundary axioms: {name}"
    IO.println (Json.mkObj [("kind",Json.str "actual_closed_boundary"),
      ("declaration",Json.str name.toString),("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
