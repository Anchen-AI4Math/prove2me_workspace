import missions.zeta9.formalization.CoefficientMapKernelBridge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
The actual round-seven F matrix uses monomial rows and formal-output columns.
The inverse coefficients are rational, including for integer output targets.
This source is prepared offline and awaits its first actual Lean compilation.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Matrix
open Polynomial

namespace ZetaNine.CoefficientMapMatrix

open CoefficientMapAggregate CoefficientMapKernelBridge

def actualFMatrix (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => aggregate n (X ^ i.val) j

theorem quarticAggregate_eq_row_vector (n : ℕ) (c : Fin 5 → ℚ) :
    quarticAggregateLinearMap n c = c ᵥ* actualFMatrix n := by
  classical
  calc
    quarticAggregateLinearMap n c =
        aggregateLinearMap n (∑ i : Fin 5, c i • (X ^ i.val : ℚ[X])) := by
      simp only [quartic_aggregate_is_actual, coordinatePolynomial, smul_eq_C_mul]
      rfl
    _ = ∑ i : Fin 5, c i • aggregateLinearMap n (X ^ i.val : ℚ[X]) := by
      rw [map_sum]
      simp only [map_smul]
    _ = c ᵥ* actualFMatrix n := by
      rw [Matrix.vecMul_eq_sum]
      rfl

theorem coordinatePolynomial_single_one (i : Fin 5) :
    coordinatePolynomial (Pi.single i 1) = (X : ℚ[X]) ^ i.val := by
  classical
  simp [coordinatePolynomial, Pi.single_apply]

/-- Mathlib's standard column-action matrix is the transpose of the paper's F. -/
theorem column_action_matrix_is_transpose (n : ℕ) :
    LinearMap.toMatrix' (quarticAggregateLinearMap n) = (actualFMatrix n)ᵀ := by
  ext i j
  rw [LinearMap.toMatrix'_apply, quartic_aggregate_is_actual, coordinatePolynomial_single_one]
  rfl

theorem actualFMatrix_row_action_bijective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Bijective (actualFMatrix n).vecMul := by
  have heq : (actualFMatrix n).vecMul = quarticAggregateLinearMap n := by
    funext c
    exact (quarticAggregate_eq_row_vector n c).symm
  rw [heq]
  exact original_five_dimensional_map_bijective n hn2 hn

theorem actualFMatrix_det_isUnit (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    IsUnit (actualFMatrix n).det := by
  have hunit : IsUnit (actualFMatrix n) := Matrix.vecMul_surjective_iff_isUnit.mp
    (actualFMatrix_row_action_bijective n hn2 hn).surjective
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit

theorem actualFMatrix_det_ne_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    (actualFMatrix n).det ≠ 0 := (actualFMatrix_det_isUnit n hn2 hn).ne_zero

theorem inverseMultiplier_coordinates_eq_row_inverse (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    polynomialCoordinates (inverseMultiplier n hn2 hn b) = b ᵥ* (actualFMatrix n)⁻¹ := by
  have hrow : polynomialCoordinates (inverseMultiplier n hn2 hn b) ᵥ* actualFMatrix n = b := by
    rw [← quarticAggregate_eq_row_vector, quartic_aggregate_is_actual,
      polynomial_restore _ (inverseMultiplier_natDegree_le n hn2 hn b),
      inverseMultiplier_actual_aggregate]
  have h := congrArg (fun c : Fin 5 → ℚ => c ᵥ* (actualFMatrix n)⁻¹) hrow
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (actualFMatrix_det_isUnit n hn2 hn),
    Matrix.vecMul_one] using h

theorem inverseMultiplier_eq_coordinatePolynomial_row_inverse (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b : Fin 5 → ℚ) :
    inverseMultiplier n hn2 hn b = coordinatePolynomial (b ᵥ* (actualFMatrix n)⁻¹) := by
  rw [← inverseMultiplier_coordinates_eq_row_inverse n hn2 hn b,
    polynomial_restore _ (inverseMultiplier_natDegree_le n hn2 hn b)]

/-- The genuine two selected output directions are B and rho9. -/
def selectionMatrix : Matrix (Fin 2) (Fin 5) ℚ :=
  fun i j => if i = 0 then (if j = 0 then 1 else 0) else (if j = 4 then 1 else 0)

def selectedIntegerPair (b a : ℤ) : Fin 2 → ℚ :=
  fun i => if i = 0 then (b : ℚ) else (a : ℚ)

def selectedIntegerOutput (b a : ℤ) : Fin 5 → ℚ :=
  fun j => if j = 0 then (b : ℚ) else if j = 4 then (a : ℚ) else 0

theorem selectedIntegerPair_mul_selection (b a : ℤ) :
    selectedIntegerPair b a ᵥ* selectionMatrix = selectedIntegerOutput b a := by
  have h04 : (0 : Fin 5) ≠ 4 := by decide
  ext j
  fin_cases j <;>
    norm_num [Matrix.vecMul_apply_eq_sum, selectionMatrix, selectedIntegerPair,
      selectedIntegerOutput, Fin.sum_univ_succ, h04]

def selectedIntegerMultiplier (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) : ℚ[X] :=
  inverseMultiplier n hn2 hn (selectedIntegerOutput b a)

theorem selectedIntegerMultiplier_coordinates (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    polynomialCoordinates (selectedIntegerMultiplier n hn2 hn b a) =
      (selectedIntegerPair b a ᵥ* selectionMatrix) ᵥ* (actualFMatrix n)⁻¹ := by
  rw [selectedIntegerMultiplier, inverseMultiplier_coordinates_eq_row_inverse,
    selectedIntegerPair_mul_selection]

theorem selectedIntegerMultiplier_coordinates_product (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    polynomialCoordinates (selectedIntegerMultiplier n hn2 hn b a) =
      selectedIntegerPair b a ᵥ* (selectionMatrix * (actualFMatrix n)⁻¹) := by
  rw [selectedIntegerMultiplier_coordinates, Matrix.vecMul_vecMul]

theorem selectedIntegerMultiplier_natDegree_le (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    (selectedIntegerMultiplier n hn2 hn b a).natDegree ≤ 4 :=
  inverseMultiplier_natDegree_le n hn2 hn (selectedIntegerOutput b a)

theorem selectedIntegerMultiplier_actual_output (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    aggregate n (selectedIntegerMultiplier n hn2 hn b a) = selectedIntegerOutput b a :=
  inverseMultiplier_actual_aggregate n hn2 hn (selectedIntegerOutput b a)

theorem selectedIntegerMultiplier_five_actual_coordinates (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    CoefficientMapFiniteSum.constantTerm n (selectedIntegerMultiplier n hn2 hn b a) = (b : ℚ) ∧
      CoefficientMapFiniteSum.rho n 3 (selectedIntegerMultiplier n hn2 hn b a) = 0 ∧
      CoefficientMapFiniteSum.rho n 5 (selectedIntegerMultiplier n hn2 hn b a) = 0 ∧
      CoefficientMapFiniteSum.rho n 7 (selectedIntegerMultiplier n hn2 hn b a) = 0 ∧
      CoefficientMapFiniteSum.rho n 9 (selectedIntegerMultiplier n hn2 hn b a) = (a : ℚ) := by
  have h := selectedIntegerMultiplier_actual_output n hn2 hn b a
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  exact ⟨by simpa [aggregate, selectedIntegerOutput] using h0,
    by simpa [aggregate, selectedIntegerOutput] using h1,
    by simpa [aggregate, selectedIntegerOutput] using h2,
    by simpa [aggregate, selectedIntegerOutput] using h3,
    by simpa [aggregate, selectedIntegerOutput] using h4⟩

theorem selected_prescribed_L (b a : ℤ) :
    prescribedL (selectedIntegerOutput b a) =
      (b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9 := by
  norm_num [prescribedL, selectedIntegerOutput, Fin.ext_iff]

theorem selectedIntegerMultiplier_actual_exact_L (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    CoefficientMapSummation.exactL n (selectedIntegerMultiplier n hn2 hn b a) =
      (b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9 := by
  rw [selectedIntegerMultiplier, inverseMultiplier_exact_L, selected_prescribed_L]

theorem selectedIntegerMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ))
        ((b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖) := by
  simpa only [selectedIntegerMultiplier, selected_prescribed_L] using
    inverseMultiplier_actual_HasSum_and_absolute n hn2 hn (selectedIntegerOutput b a)

end ZetaNine.CoefficientMapMatrix
