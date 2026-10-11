import Oracle.CoefficientMapTelescoper
import Oracle.CoefficientMapShiftDegree
import Mathlib.Order.Interval.Set.Infinite

/-!
The genuine P0, R*A and shift identities linking the actual telescoper quotient
to a polynomial difference. No polynomial difference or trivial-kernel input is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace OutputsPlatformOracle.CoefficientMapKernelBridge

open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper

def positiveProduct (n : ℕ) (t : ℚ) : ℚ := ∏ k ∈ range n, (t - ((k : ℚ) + 1))

def negativeProduct (n : ℕ) (t : ℚ) : ℚ := ∏ k ∈ range n, (t + (n : ℚ) + ((k : ℚ) + 1))

def aValue (n : ℕ) (t : ℚ) : ℚ := (t - (n : ℚ) - 1) * (t + (n : ℚ)) ^ 10

def bValue (n : ℕ) (t : ℚ) : ℚ := t ^ 10 * (t + 2 * (n : ℚ) + 1)

theorem finite_product_shift_identity (n : ℕ) (f : ℕ → ℚ) :
    (∏ k ∈ range n, f (k + 1)) * f 0 = (∏ k ∈ range n, f k) * f n := by
  have h := Finset.prod_range_succ' f n
  rw [Finset.prod_range_succ] at h
  simpa only [mul_comm] using h.symm

theorem positiveProduct_shift (n : ℕ) (t : ℚ) :
    positiveProduct n (t + 1) * (t - (n : ℚ)) = t * positiveProduct n t := by
  have h := finite_product_shift_identity n (fun k => t - (k : ℚ))
  have he : positiveProduct n (t + 1) = ∏ k ∈ range n, (t - (k : ℚ)) := by
    unfold positiveProduct
    apply Finset.prod_congr rfl
    intro k hk
    ring
  rw [he]
  simpa only [positiveProduct, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, mul_comm] using h.symm

theorem negativeProduct_shift (n : ℕ) (t : ℚ) :
    negativeProduct n (t + 1) * (t + (n : ℚ) + 1) =
      negativeProduct n t * (t + 2 * (n : ℚ) + 1) := by
  have h := finite_product_shift_identity n (fun k => t + (n : ℚ) + ((k : ℚ) + 1))
  have he : (∏ k ∈ range n, (t + (n : ℚ) + (((k + 1 : ℕ) : ℚ) + 1))) =
      negativeProduct n (t + 1) := by
    unfold negativeProduct
    apply Finset.prod_congr rfl
    intro k hk
    push_cast
    ring
  rw [he] at h
  have hend : t + (n : ℚ) + ((n : ℚ) + 1) = t + 2 * (n : ℚ) + 1 := by ring
  simpa only [negativeProduct, Nat.cast_zero, zero_add, hend] using h

theorem numerator_shift_identity (n : ℕ) (t : ℚ) :
    CoefficientMap.numerator n (t + 1) * (t - (n : ℚ)) * (t + (n : ℚ) + 1) =
      CoefficientMap.numerator n t * t * (t + 2 * (n : ℚ) + 1) := by
  change (n.factorial : ℚ) ^ 7 * positiveProduct n (t + 1) * negativeProduct n (t + 1) *
      (t - (n : ℚ)) * (t + (n : ℚ) + 1) =
    (n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t * t * (t + 2 * (n : ℚ) + 1)
  calc
    _ = (n.factorial : ℚ) ^ 7 * (positiveProduct n (t + 1) * (t - (n : ℚ))) *
        (negativeProduct n (t + 1) * (t + (n : ℚ) + 1)) := by ring
    _ = _ := by rw [positiveProduct_shift, negativeProduct_shift]; ring

theorem poleProduct_shift_identity (n : ℕ) (t : ℚ) :
    CoefficientMap.poleProduct n (t + 1) * t = CoefficientMap.poleProduct n t * (t + (n : ℚ) + 1) := by
  have h := finite_product_shift_identity (n + 1) (fun k => t + (k : ℚ))
  simpa only [CoefficientMap.poleProduct, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
    add_assoc, add_comm, add_left_comm] using h

theorem actual_R_shift_A_equals_R_B (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0)
    (hregular1 : ∀ k ≤ n, (t + 1) + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR n (t + 1) * aValue n (t + 1) = CoefficientMap.actualR n t * bValue n t := by
  have hden := CoefficientMap.poleProduct_ne_zero n t hregular
  have hden1 := CoefficientMap.poleProduct_ne_zero n (t + 1) hregular1
  have hnum := numerator_shift_identity n t
  have hpole := congrArg (fun x : ℚ => x ^ 9) (poleProduct_shift_identity n t)
  simp only [mul_pow] at hpole
  unfold CoefficientMap.actualR aValue bValue
  field_simp [hden, hden1]
  calc
    _ = (CoefficientMap.numerator n (t + 1) * (t - (n : ℚ)) * (t + (n : ℚ) + 1)) *
        ((t + (n : ℚ) + 1) ^ 9 * CoefficientMap.poleProduct n t ^ 9) := by ring
    _ = (CoefficientMap.numerator n t * t * (t + 2 * (n : ℚ) + 1)) *
        (CoefficientMap.poleProduct n (t + 1) ^ 9 * t ^ 9) := by rw [hnum, hpole]; ring
    _ = _ := by ring

theorem rootPolynomial_numerator_factor (n : ℕ) (t : ℚ) :
    (n.factorial : ℚ) ^ 7 * (rootPolynomial n).eval t =
      CoefficientMap.numerator n t * (t - (n : ℚ) - 1) * (t + (n : ℚ)) := by
  rw [rootPolynomial_eq_explicit_products]
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  rw [Finset.prod_range_succ (fun k : ℕ => t - ((k : ℚ) + 1)) n,
    Finset.prod_range_succ' (fun k : ℕ => t + (n : ℚ) + (k : ℚ)) n]
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  change (n.factorial : ℚ) ^ 7 * ((positiveProduct n t * (t - ((n : ℚ) + 1))) *
      (negativeProduct n t * (t + (n : ℚ)))) = _
  change _ = (n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t *
    (t - (n : ℚ) - 1) * (t + (n : ℚ))
  ring

theorem poleProduct_last_factor (n : ℕ) (hn1 : 1 ≤ n) (t : ℚ) :
    CoefficientMap.poleProduct n t = (polePolynomial (n - 1)).eval t * (t + (n : ℚ)) := by
  rw [CoefficientMapPartialFractions.polePolynomial_eval]
  unfold CoefficientMap.poleProduct
  rw [show n - 1 + 1 = n by omega]
  exact Finset.prod_range_succ _ _

theorem actual_R_A_equals_Pzero (n : ℕ) (hn1 : 1 ≤ n) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR n t * aValue n t =
      (n.factorial : ℚ) ^ 7 * (rootPolynomial n).eval t / (polePolynomial (n - 1)).eval t ^ 9 := by
  have hden := CoefficientMapPartialFractions.polePolynomial_eval_ne_zero (n - 1) t
    (by intro k hk; exact hregular k (by omega))
  have hlast := hregular n (by omega)
  rw [rootPolynomial_numerator_factor]
  unfold CoefficientMap.actualR aValue
  rw [poleProduct_last_factor n hn1, mul_pow]
  field_simp [hden, hlast]

theorem telescoper_quotient_as_R_A (n : ℕ) (hn1 : 1 ≤ n) (W H : ℚ[X])
    (hH : telescoperNumerator n W = rootPolynomial n * H) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    telescoper n W t = CoefficientMap.actualR n t * aValue n t * H.eval t / (n.factorial : ℚ) ^ 7 := by
  have hfactor : (n.factorial : ℚ) ^ 7 ≠ 0 := pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
  rw [telescoper_actual_rational_representation n hn1 W t
    (by intro k hk; exact hregular k (by omega)), hH, Polynomial.eval_mul,
    actual_R_A_equals_Pzero n hn1 t hregular]
  field_simp [hfactor]

theorem actual_R_ne_zero_above_n (n : ℕ) (t : ℚ) (ht : (n : ℚ) < t) : CoefficientMap.actualR n t ≠ 0 := by
  have ht0 : (0 : ℚ) < t := lt_of_le_of_lt (Nat.cast_nonneg n) ht
  apply div_ne_zero
  · unfold CoefficientMap.numerator
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
      · apply Finset.prod_ne_zero_iff.mpr
        intro k hk
        have hk1 : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        exact ne_of_gt (by linarith)
    · apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact ne_of_gt (by positivity)
  · exact pow_ne_zero _ (CoefficientMap.poleProduct_ne_zero n t
      (by intro k hk; exact ne_of_gt (add_pos_of_pos_of_nonneg ht0 (Nat.cast_nonneg k))))

theorem kernel_actual_polynomial_relation (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W H : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (hH : telescoperNumerator n W = rootPolynomial n * H) :
    C ((n.factorial : ℚ) ^ 7) * W.comp (baseU n) =
      ((X - C ((n : ℚ) + 1)) * (X + C (n : ℚ)) ^ 10) * H -
        (X ^ 10 * (X + C (2 * (n : ℚ) + 1))) * H.comp (X + C 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite ((n : ℚ) + 1)).mono
  intro t ht
  have ht1 : (n : ℚ) + 1 < t := ht
  have ht0 : (0 : ℚ) < t := by have hnonneg : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n; linarith
  have hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht0 (Nat.cast_nonneg k))
  have hregular1 : ∀ k ≤ n, (t + 1) + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (by positivity)
  have hR : CoefficientMap.actualR n t ≠ 0 := actual_R_ne_zero_above_n n t (by linarith)
  have hfac : (n.factorial : ℚ) ^ 7 ≠ 0 := pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
  have hdiff := actual_weightedR_is_difference n hn W hstrong hzero t hregular
  rw [telescoper_quotient_as_R_A n hn1 W H hH t hregular,
    telescoper_quotient_as_R_A n hn1 W H hH (t + 1) hregular1] at hdiff
  rw [actual_R_shift_A_equals_R_B n t hregular hregular1] at hdiff
  unfold CoefficientMap.weightedR at hdiff
  have he : (n.factorial : ℚ) ^ 7 * W.eval (t * (t + (n : ℚ))) =
      aValue n t * H.eval t - bValue n t * H.eval (t + 1) := by
    field_simp [hfac] at hdiff
    nlinarith [hdiff]
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    baseU, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    aValue, bValue, sub_sub, add_assoc] using he

theorem original_quartic_aggregate_kernel_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) : W = 0 := by
  have hstrong := quartic_is_strong_proper n (by omega) W hW
  obtain ⟨H, hH, hdegree⟩ := actual_polynomial_quotient_degree_bound n (by omega) hn W hstrong hzero
  have hrelation := kernel_actual_polynomial_relation n (by omega) hn W H hstrong hzero hH
  have hdiff : CoefficientMapShiftDegree.shiftDifference n H =
      C ((n.factorial : ℚ) ^ 7) * W.comp (baseU n) := hrelation.symm
  have hsmall : (CoefficientMapShiftDegree.shiftDifference n H).natDegree ≤ 8 := by
    rw [hdiff]
    have hmul : (C ((n.factorial : ℚ) ^ 7) * W.comp (baseU n)).natDegree ≤
        (C ((n.factorial : ℚ) ^ 7)).natDegree + (W.comp (baseU n)).natDegree := Polynomial.natDegree_mul_le
    have hcomp := Polynomial.natDegree_comp_le (p := W) (q := baseU n)
    rw [Polynomial.natDegree_C, zero_add] at hmul
    rw [baseU_natDegree] at hcomp
    omega
  have hH0 := CoefficientMapShiftDegree.actual_shift_difference_small_degree_implies_zero n (by omega) H hdegree hsmall
  rw [hH0] at hdiff
  simp only [CoefficientMapShiftDegree.shiftDifference, Polynomial.zero_comp, mul_zero, sub_zero] at hdiff
  have hcomp : W.comp (baseU n) = 0 := by
    have hfac : C ((n.factorial : ℚ) ^ 7) ≠ (0 : ℚ[X]) :=
      Polynomial.C_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero))
    exact (mul_eq_zero.mp hdiff.symm).resolve_left hfac
  apply weightedNumerator_zero_implies_multiplier_zero n W
  simp only [weightedNumerator, hcomp, mul_zero]

theorem original_quartic_aggregate_injective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W V : ℚ[X]) (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (heq : aggregate n W = aggregate n V) : W = V := by
  have hdegree : (W - V).natDegree ≤ 4 :=
    le_trans (Polynomial.natDegree_sub_le W V) (max_le hW hV)
  have hzero : aggregate n (W - V) = 0 := by
    change aggregateLinearMap n (W - V) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr heq
  exact sub_eq_zero.mp (original_quartic_aggregate_kernel_zero n hn2 hn (W - V) hdegree hzero)

theorem original_five_dimensional_map_injective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Injective (quarticAggregateLinearMap n) := by
  intro a b heq
  apply coordinatePolynomial_injective
  exact original_quartic_aggregate_injective n hn2 hn (coordinatePolynomial a) (coordinatePolynomial b)
    (coordinatePolynomial_natDegree_le a) (coordinatePolynomial_natDegree_le b) heq

theorem original_five_dimensional_map_bijective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Bijective (quarticAggregateLinearMap n) := by
  have hi := original_five_dimensional_map_injective n hn2 hn
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

def actualAggregateEquiv (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    (Fin 5 → ℚ) ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  LinearEquiv.ofBijective (quarticAggregateLinearMap n) (original_five_dimensional_map_bijective n hn2 hn)

theorem every_exact_formal_output_has_unique_quartic (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) : ∃! W : {W : ℚ[X] // W.natDegree ≤ 4}, aggregate n W.val = b := by
  obtain ⟨a, ha⟩ := (original_five_dimensional_map_bijective n hn2 hn).surjective b
  refine ⟨⟨coordinatePolynomial a, coordinatePolynomial_natDegree_le a⟩, ha, ?_⟩
  intro V hV
  apply Subtype.ext
  exact original_quartic_aggregate_injective n hn2 hn V.val (coordinatePolynomial a) V.property
    (coordinatePolynomial_natDegree_le a) (hV.trans ha.symm)

def inverseMultiplier (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) : ℚ[X] :=
  coordinatePolynomial ((actualAggregateEquiv n hn2 hn).symm b)

def prescribedL (b : Fin 5 → ℚ) : ℝ :=
  (b 0 : ℝ) +
    ((b 1 : ℝ) * CoefficientMapSummation.zetaReal 3 +
     (b 2 : ℝ) * CoefficientMapSummation.zetaReal 5 +
     (b 3 : ℝ) * CoefficientMapSummation.zetaReal 7 +
     (b 4 : ℝ) * CoefficientMapSummation.zetaReal 9)

theorem inverseMultiplier_natDegree_le (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    (inverseMultiplier n hn2 hn b).natDegree ≤ 4 := coordinatePolynomial_natDegree_le _

theorem inverseMultiplier_actual_aggregate (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    aggregate n (inverseMultiplier n hn2 hn b) = b := by
  change (actualAggregateEquiv n hn2 hn) ((actualAggregateEquiv n hn2 hn).symm b) = b
  exact (actualAggregateEquiv n hn2 hn).apply_symm_apply b

theorem inverseMultiplier_unique (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hWb : aggregate n W = b) : W = inverseMultiplier n hn2 hn b :=
  original_quartic_aggregate_injective n hn2 hn W _ hW (inverseMultiplier_natDegree_le n hn2 hn b)
    (hWb.trans (inverseMultiplier_actual_aggregate n hn2 hn b).symm)

theorem inverseMultiplier_nonzero_of_output_nonzero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) (hb : b ≠ 0) : inverseMultiplier n hn2 hn b ≠ 0 := by
  intro hW0
  have h := inverseMultiplier_actual_aggregate n hn2 hn b
  rw [hW0] at h
  have hF0 : aggregate n (0 : ℚ[X]) = 0 := (aggregateLinearMap n).map_zero
  exact hb (h.symm.trans hF0)

theorem inverseMultiplier_exact_L (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    CoefficientMapSummation.exactL n (inverseMultiplier n hn2 hn b) = prescribedL b := by
  have h := inverseMultiplier_actual_aggregate n hn2 hn b
  have hB : CoefficientMapFiniteSum.constantTerm n (inverseMultiplier n hn2 hn b) = b 0 := congrFun h 0
  have h3 : CoefficientMapFiniteSum.rho n 3 (inverseMultiplier n hn2 hn b) = b 1 := congrFun h 1
  have h5 : CoefficientMapFiniteSum.rho n 5 (inverseMultiplier n hn2 hn b) = b 2 := congrFun h 2
  have h7 : CoefficientMapFiniteSum.rho n 7 (inverseMultiplier n hn2 hn b) = b 3 := congrFun h 3
  have h9 : CoefficientMapFiniteSum.rho n 9 (inverseMultiplier n hn2 hn b) = b 4 := congrFun h 4
  simp only [CoefficientMapSummation.exactL, hB, h3, h5, h7, h9, prescribedL]

theorem inverseMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)) (prescribedL b) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖) := by
  have hstrong := quartic_is_strong_proper n (by omega) _ (inverseMultiplier_natDegree_le n hn2 hn b)
  constructor
  · have h := CoefficientMapSummation.actualSeries_hasSum_exactL n hn _ hstrong
    rw [inverseMultiplier_exact_L n hn2 hn b] at h
    exact h
  · exact CoefficientMapSummation.actualSeries_norm_summable n _ hstrong

end OutputsPlatformOracle.CoefficientMapKernelBridge

#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.numerator_shift_identity
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.actual_R_shift_A_equals_R_B
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.actual_R_A_equals_Pzero
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.telescoper_quotient_as_R_A
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.actual_R_ne_zero_above_n
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.kernel_actual_polynomial_relation
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.original_quartic_aggregate_kernel_zero
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.original_quartic_aggregate_injective
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.original_five_dimensional_map_injective
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.original_five_dimensional_map_bijective
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.actualAggregateEquiv
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.every_exact_formal_output_has_unique_quartic
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.inverseMultiplier_actual_aggregate
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.inverseMultiplier_unique
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.inverseMultiplier_nonzero_of_output_nonzero
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.inverseMultiplier_exact_L
#print axioms OutputsPlatformOracle.CoefficientMapKernelBridge.inverseMultiplier_actual_HasSum_and_absolute
