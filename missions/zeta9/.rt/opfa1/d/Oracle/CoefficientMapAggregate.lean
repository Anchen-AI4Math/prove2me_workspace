import Oracle.CoefficientMapSummation
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.BigOperators

/-!
The genuine five-dimensional formal map, separate from the full local array.
Its entries use the actual finite harmonic constant and actual local series.
No determinant, rank, kernel triviality or inverse-map conclusion is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace OutputsPlatformOracle.CoefficientMapAggregate

open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection

def aggregate (n : ℕ) (W : ℚ[X]) (i : Fin 5) : ℚ :=
  match i.val with
  | 0 => CoefficientMapFiniteSum.constantTerm n W
  | 1 => CoefficientMapFiniteSum.rho n 3 W
  | 2 => CoefficientMapFiniteSum.rho n 5 W
  | 3 => CoefficientMapFiniteSum.rho n 7 W
  | _ => CoefficientMapFiniteSum.rho n 9 W

def coordinatePolynomial (a : Fin 5 → ℚ) : ℚ[X] :=
  ∑ i : Fin 5, C (a i) * X ^ i.val

def polynomialCoordinates (W : ℚ[X]) (i : Fin 5) : ℚ := W.coeff i.val

theorem actual_local_coefficient_add (n j s : ℕ) (W V : ℚ[X]) :
    weightedLocalCoefficient n j s (W + V) =
      weightedLocalCoefficient n j s W + weightedLocalCoefficient n j s V := by
  simp [weightedLocalCoefficient, weightedClearedSeries, add_comp, mul_add]

theorem actual_local_coefficient_smul (n j s : ℕ) (a : ℚ) (W : ℚ[X]) :
    weightedLocalCoefficient n j s (a • W) = a * weightedLocalCoefficient n j s W := by
  simp [weightedLocalCoefficient, weightedClearedSeries, smul_comp, smul_eq_mul]

theorem actual_rho_add (n s : ℕ) (W V : ℚ[X]) :
    CoefficientMapFiniteSum.rho n s (W + V) =
      CoefficientMapFiniteSum.rho n s W + CoefficientMapFiniteSum.rho n s V := by
  simp [CoefficientMapFiniteSum.rho, actual_local_coefficient_add, Finset.sum_add_distrib]

theorem actual_rho_smul (n s : ℕ) (a : ℚ) (W : ℚ[X]) :
    CoefficientMapFiniteSum.rho n s (a • W) = a * CoefficientMapFiniteSum.rho n s W := by
  simp [CoefficientMapFiniteSum.rho, actual_local_coefficient_smul, Finset.mul_sum]

theorem actual_constant_add (n : ℕ) (W V : ℚ[X]) :
    CoefficientMapFiniteSum.constantTerm n (W + V) =
      CoefficientMapFiniteSum.constantTerm n W + CoefficientMapFiniteSum.constantTerm n V := by
  simp only [CoefficientMapFiniteSum.constantTerm, actual_local_coefficient_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem actual_constant_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
    CoefficientMapFiniteSum.constantTerm n (a • W) = a * CoefficientMapFiniteSum.constantTerm n W := by
  simp [CoefficientMapFiniteSum.constantTerm, actual_local_coefficient_smul, mul_assoc,
    Finset.mul_sum]

theorem aggregate_add (n : ℕ) (W V : ℚ[X]) :
    aggregate n (W + V) = aggregate n W + aggregate n V := by
  funext i
  fin_cases i <;> simp [aggregate, actual_constant_add, actual_rho_add]

theorem aggregate_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
    aggregate n (a • W) = a • aggregate n W := by
  funext i
  fin_cases i <;> simp [aggregate, actual_constant_smul, actual_rho_smul, smul_eq_mul]

def aggregateLinearMap (n : ℕ) : ℚ[X] →ₗ[ℚ] (Fin 5 → ℚ) where
  toFun := aggregate n
  map_add' := aggregate_add n
  map_smul' := aggregate_smul n

theorem coordinatePolynomial_add (a b : Fin 5 → ℚ) :
    coordinatePolynomial (a + b) = coordinatePolynomial a + coordinatePolynomial b := by
  simp [coordinatePolynomial, C_add, add_mul, Finset.sum_add_distrib]

theorem coordinatePolynomial_smul (c : ℚ) (a : Fin 5 → ℚ) :
    coordinatePolynomial (c • a) = c • coordinatePolynomial a := by
  simp [coordinatePolynomial, smul_eq_mul, C_mul, mul_assoc, smul_eq_C_mul,
    Finset.mul_sum]

def coordinateLinearMap : (Fin 5 → ℚ) →ₗ[ℚ] ℚ[X] where
  toFun := coordinatePolynomial
  map_add' := coordinatePolynomial_add
  map_smul' := coordinatePolynomial_smul

def quarticAggregateLinearMap (n : ℕ) : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) :=
  (aggregateLinearMap n).comp coordinateLinearMap

theorem coordinatePolynomial_coeff (a : Fin 5 → ℚ) (i : Fin 5) :
    (coordinatePolynomial a).coeff i.val = a i := by
  classical
  simp only [coordinatePolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have h : i.val ≠ j.val := by intro he; exact hji (Fin.ext he.symm)
    simp [h]
  · simp

theorem coordinatePolynomial_coeff_above (a : Fin 5 → ℚ) (k : ℕ) (hk : 5 ≤ k) :
    (coordinatePolynomial a).coeff k = 0 := by
  classical
  simp only [coordinatePolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro i hi
  have h : k ≠ i.val := by have := i.isLt; omega
  simp [h]

theorem coordinatePolynomial_natDegree_le (a : Fin 5 → ℚ) :
    (coordinatePolynomial a).natDegree ≤ 4 := by
  unfold coordinatePolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have h : (C (a i) * X ^ i.val : ℚ[X]).natDegree ≤
      (C (a i) : ℚ[X]).natDegree + (X ^ i.val : ℚ[X]).natDegree := natDegree_mul_le
  simp only [natDegree_C, natDegree_X_pow, zero_add] at h
  exact h.trans (by have := i.isLt; omega)

theorem coordinates_restore (a : Fin 5 → ℚ) :
    polynomialCoordinates (coordinatePolynomial a) = a := by
  funext i
  exact coordinatePolynomial_coeff a i

theorem polynomial_restore (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    coordinatePolynomial (polynomialCoordinates W) = W := by
  ext k
  by_cases hk : k < 5
  · exact coordinatePolynomial_coeff (polynomialCoordinates W) ⟨k, hk⟩
  · rw [coordinatePolynomial_coeff_above _ k (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem coordinatePolynomial_injective : Function.Injective coordinatePolynomial := by
  intro a b hab
  simpa only [coordinates_restore] using congrArg polynomialCoordinates hab

theorem quartic_aggregate_is_actual (n : ℕ) (a : Fin 5 → ℚ) :
    quarticAggregateLinearMap n a = aggregate n (coordinatePolynomial a) := rfl

theorem aggregate_zero_iff (n : ℕ) (W : ℚ[X]) :
    aggregate n W = 0 ↔ CoefficientMapFiniteSum.constantTerm n W = 0 ∧
      CoefficientMapFiniteSum.rho n 3 W = 0 ∧ CoefficientMapFiniteSum.rho n 5 W = 0 ∧
      CoefficientMapFiniteSum.rho n 7 W = 0 ∧ CoefficientMapFiniteSum.rho n 9 W = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3, congrFun h 4⟩
  · rintro ⟨hB, h3, h5, h7, h9⟩
    funext i
    fin_cases i <;> simp [aggregate, hB, h3, h5, h7, h9]

theorem aggregate_zero_all_rho (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) : CoefficientMapFiniteSum.rho n s W = 0 := by
  obtain ⟨hB, h3, h5, h7, h9⟩ := (aggregate_zero_iff n W).mp hzero
  have h1 : CoefficientMapFiniteSum.rho n 1 W = 0 := rho_one_zero_of_strong_proper n W hstrong
  have h2 : CoefficientMapFiniteSum.rho n 2 W = 0 := rho_even_order_zero n 2 hn W (by omega) (by omega) (by norm_num)
  have h4 : CoefficientMapFiniteSum.rho n 4 W = 0 := rho_even_order_zero n 4 hn W (by omega) (by omega) (by norm_num)
  have h6 : CoefficientMapFiniteSum.rho n 6 W = 0 := rho_even_order_zero n 6 hn W (by omega) (by omega) (by norm_num)
  have h8 : CoefficientMapFiniteSum.rho n 8 W = 0 := rho_even_order_zero n 8 hn W (by omega) (by omega) (by norm_num)
  interval_cases s <;> assumption

theorem aggregate_zero_exactL (n : ℕ) (W : ℚ[X]) (hzero : aggregate n W = 0) :
    CoefficientMapSummation.exactL n W = 0 := by
  obtain ⟨hB, h3, h5, h7, h9⟩ := (aggregate_zero_iff n W).mp hzero
  simp [CoefficientMapSummation.exactL, hB, h3, h5, h7, h9]

end OutputsPlatformOracle.CoefficientMapAggregate

#print axioms OutputsPlatformOracle.CoefficientMapAggregate.aggregateLinearMap
#print axioms OutputsPlatformOracle.CoefficientMapAggregate.coordinateLinearMap
#print axioms OutputsPlatformOracle.CoefficientMapAggregate.quarticAggregateLinearMap
#print axioms OutputsPlatformOracle.CoefficientMapAggregate.coordinates_restore
#print axioms OutputsPlatformOracle.CoefficientMapAggregate.polynomial_restore
#print axioms OutputsPlatformOracle.CoefficientMapAggregate.aggregate_zero_all_rho
