import missions.zeta9.formalization.CoefficientMapFormalTransportOutputs

/-!
UNCOMPILED PURE CANDIDATE, prepared 2026-10-07; no Lean invocation yet.
The next private SOURCE rebuild must install the Outputs AUTHOR export
8b2fc477c10a698f9b5bef004531861c392d93da0377a2874965c8ce470d2fa6
and its genuine Jets dependency ccef5eaf...4c02 at their stable module paths.
The unchanged shared initial Outputs source f16dc8be...f09d is not that export.

The finite five-output theorem supplies the parameter transport. The existing
actual absolute-convergence and HasSum theorem supplies the infinite sum.
Even n is used only for the existing odd-zeta exactL formula; n >= 2 also
permits the genuine inverseMultiplier uniqueness conclusions. No transport,
partial-fraction existence, HasSum, zeta independence or desired conclusion
is supplied as an assumption. This file does not prove integrality, heights,
the J condition or irrationality of zeta(9).
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix
open Polynomial

namespace ZetaNine.CoefficientMapParameterSummationTransport

open CoefficientMapAggregate CoefficientMapMatrix CoefficientMapKernelBridge
open CoefficientMapReflection CoefficientMapSummation
open CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapFormalTransportOutputs

/-- Transfer a higher-parameter quartic to the actual old quartic coordinates. -/
def transferMultiplier (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  coordinatePolynomial (polynomialCoordinates W ᵥ* connectionGamma n)

theorem transferMultiplier_natDegree_le (n : ℕ) (W : ℚ[X]) :
    (transferMultiplier n W).natDegree ≤ 4 :=
  coordinatePolynomial_natDegree_le _

theorem even_add_two (n : ℕ) (hn : Even n) : Even (n + 2) := by
  obtain ⟨k, hk⟩ := hn
  exact ⟨k + 1, by omega⟩

theorem exactL_eq_prescribed_actual_output (n : ℕ) (W : ℚ[X]) :
    exactL n W = prescribedL (aggregate n W) := rfl

theorem transfer_actual_five_outputs (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    aggregate n (transferMultiplier n W) = aggregate (n + 2) W := by
  calc
    aggregate n (transferMultiplier n W) =
        quarticAggregateLinearMap n (polynomialCoordinates W ᵥ* connectionGamma n) := rfl
    _ = (polynomialCoordinates W ᵥ* connectionGamma n) ᵥ* actualFMatrix n :=
      quarticAggregate_eq_row_vector n _
    _ = polynomialCoordinates W ᵥ* (connectionGamma n * actualFMatrix n) :=
      Matrix.vecMul_vecMul _ _ _
    _ = polynomialCoordinates W ᵥ* actualFMatrix (n + 2) := by
      rw [← actual_five_output_matrix_transport n hn]
    _ = quarticAggregateLinearMap (n + 2) (polynomialCoordinates W) :=
      (quarticAggregate_eq_row_vector (n + 2) _).symm
    _ = aggregate (n + 2) W := by
      rw [quartic_aggregate_is_actual, polynomial_restore W hW]

theorem transfer_actual_exactL (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    exactL n (transferMultiplier n W) = exactL (n + 2) W := by
  rw [exactL_eq_prescribed_actual_output, exactL_eq_prescribed_actual_output,
    transfer_actual_five_outputs n hn W hW]

theorem quartic_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries n W) (exactL n W) ∧
      Summable (fun t : ℕ => ‖actualSeries n W t‖) := by
  have hstrong := quartic_is_strong_proper n (by omega) W hW
  exact ⟨actualSeries_hasSum_exactL n hn W hstrong,
    actualSeries_norm_summable n W hstrong⟩

theorem actual_chosen_exactL_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    exactL (n + 2) (X ^ r.val) = exactL n (connectionP n r) := by
  rw [exactL_eq_prescribed_actual_output, exactL_eq_prescribed_actual_output,
    actual_chosen_five_output_transport n hn r]

theorem actual_chosen_HasSum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (r : Fin 5) :
    HasSum (actualSeries (n + 2) (X ^ r.val)) (exactL n (connectionP n r)) ∧
      HasSum (actualSeries n (connectionP n r)) (exactL n (connectionP n r)) ∧
      Summable (fun t : ℕ => ‖actualSeries (n + 2) (X ^ r.val) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries n (connectionP n r) t‖) := by
  have hr : (X ^ r.val : ℚ[X]).natDegree ≤ 4 := by
    rw [natDegree_X_pow]
    have := r.isLt
    omega
  have hnew := quartic_actual_HasSum_and_absolute (n + 2) (by omega)
    (even_add_two n hn) (X ^ r.val) hr
  have hold := quartic_actual_HasSum_and_absolute n hn2 hn (connectionP n r)
    (connectionP_natDegree_le n (by omega) r)
  rw [actual_chosen_exactL_transport n (by omega) r] at hnew
  exact ⟨hnew.1, hold.1, hnew.2, hold.2⟩

theorem actual_chosen_tsum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (r : Fin 5) :
    (∑' t : ℕ, actualSeries (n + 2) (X ^ r.val) t) =
      ∑' t : ℕ, actualSeries n (connectionP n r) t := by
  have h := actual_chosen_HasSum_transport n hn2 hn r
  exact h.1.tsum_eq.trans h.2.1.tsum_eq.symm

theorem quartic_HasSum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries (n + 2) W) (exactL (n + 2) W) ∧
      HasSum (actualSeries n (transferMultiplier n W)) (exactL (n + 2) W) ∧
      Summable (fun t : ℕ => ‖actualSeries (n + 2) W t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries n (transferMultiplier n W) t‖) := by
  have hnew := quartic_actual_HasSum_and_absolute (n + 2) (by omega)
    (even_add_two n hn) W hW
  have hold := quartic_actual_HasSum_and_absolute n hn2 hn (transferMultiplier n W)
    (transferMultiplier_natDegree_le n W)
  rw [transfer_actual_exactL n (by omega) W hW] at hold
  exact ⟨hnew.1, hold.1, hnew.2, hold.2⟩

theorem quartic_tsum_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    (∑' t : ℕ, actualSeries (n + 2) W t) =
      ∑' t : ℕ, actualSeries n (transferMultiplier n W) t := by
  have h := quartic_HasSum_transport n hn2 hn W hW
  exact h.1.tsum_eq.trans h.2.1.tsum_eq.symm

theorem transferred_inverseMultiplier_eq (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    transferMultiplier n (inverseMultiplier (n + 2) (by omega) (even_add_two n hn) b) =
      inverseMultiplier n hn2 hn b := by
  apply inverseMultiplier_unique n hn2 hn b
    (transferMultiplier n (inverseMultiplier (n + 2) (by omega) (even_add_two n hn) b))
    (transferMultiplier_natDegree_le n _)
  rw [transfer_actual_five_outputs n (by omega) _
    (inverseMultiplier_natDegree_le (n + 2) (by omega) (even_add_two n hn) b),
    inverseMultiplier_actual_aggregate]

theorem inverseMultiplier_coordinates_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    polynomialCoordinates (inverseMultiplier (n + 2) (by omega) (even_add_two n hn) b)
        ᵥ* connectionGamma n = polynomialCoordinates (inverseMultiplier n hn2 hn b) := by
  have h := congrArg polynomialCoordinates (transferred_inverseMultiplier_eq n hn2 hn b)
  simpa only [transferMultiplier, coordinates_restore] using h

theorem chosen_transferMultiplier_eq_connectionP (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (r : Fin 5) :
    transferMultiplier n (X ^ r.val) = connectionP n r := by
  have hr : (X ^ r.val : ℚ[X]).natDegree ≤ 4 := by
    rw [natDegree_X_pow]
    have := r.isLt
    omega
  apply original_quartic_aggregate_injective n hn2 hn
    (transferMultiplier n (X ^ r.val)) (connectionP n r)
    (transferMultiplier_natDegree_le n _) (connectionP_natDegree_le n (by omega) r)
  rw [transfer_actual_five_outputs n (by omega) _ hr,
    actual_chosen_five_output_transport n (by omega) r]

theorem selectedIntegerMultiplier_transport (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b a : ℤ) :
    transferMultiplier n
        (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a) =
      selectedIntegerMultiplier n hn2 hn b a := by
  simpa only [selectedIntegerMultiplier] using
    transferred_inverseMultiplier_eq n hn2 hn (selectedIntegerOutput b a)

theorem selectedIntegerMultiplier_parameter_HasSum (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    HasSum (actualSeries (n + 2)
        (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a))
      ((b : ℝ) + (a : ℝ) * zetaReal 9) ∧
      HasSum (actualSeries n (selectedIntegerMultiplier n hn2 hn b a))
        ((b : ℝ) + (a : ℝ) * zetaReal 9) ∧
      Summable (fun t : ℕ => ‖actualSeries (n + 2)
        (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries n (selectedIntegerMultiplier n hn2 hn b a) t‖) := by
  have h := quartic_HasSum_transport n hn2 hn
    (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a)
    (selectedIntegerMultiplier_natDegree_le (n + 2) (by omega) (even_add_two n hn) b a)
  rw [selectedIntegerMultiplier_transport n hn2 hn b a,
    selectedIntegerMultiplier_actual_exact_L] at h
  exact h

theorem selectedIntegerMultiplier_parameter_tsum (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    (∑' t : ℕ, actualSeries (n + 2)
      (selectedIntegerMultiplier (n + 2) (by omega) (even_add_two n hn) b a) t) =
      ∑' t : ℕ, actualSeries n (selectedIntegerMultiplier n hn2 hn b a) t := by
  have h := selectedIntegerMultiplier_parameter_HasSum n hn2 hn b a
  exact h.1.tsum_eq.trans h.2.1.tsum_eq.symm

end ZetaNine.CoefficientMapParameterSummationTransport
