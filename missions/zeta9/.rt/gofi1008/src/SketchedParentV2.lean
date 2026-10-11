import Definitions.Def_ZetaNine_GraphBridge_OneForm
import Theorems.Thm_ZetaNine_GraphBridge_selected_inverse_positive_cone_margin
import Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_coordinates_product
import Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute
import Theorems.Thm_ZetaNine_AnalyticWeightedBound_actual_weighted_uniform_o_one
import Theorems.Thm_ZetaNine_taylor_sign_implies_kernel_sum_pos

/-!
SELF-CONTAINED SOURCE candidate awaiting its first actual compilation.
Each owned theorem below has a complete proof body with no placeholder.
The imported catalogue theorem modules are the actual graph dependencies,
not claimed independent complete-proof verification of those children.
The only mathematical Open input is the actual inverse-image cone margin.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open scoped BigOperators Matrix Topology
open Finset Polynomial Filter

namespace ZetaNine.GraphBridge
open CoefficientMapMatrix CoefficientMapAggregate CoefficientMapKernelBridge
open AnalyticWeightedBound

theorem one_selectedMultiplier_degree_le (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    (selectedIntegerMultiplier n hn2 hn b a).natDegree ≤ 4 := by
  let c : Fin 5 → ℚ := (actualAggregateEquiv n hn2 hn).symm (selectedIntegerOutput b a)
  change (coordinatePolynomial c).natDegree ≤ 4
  unfold coordinatePolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have h : (C (c i) * X ^ i.val : ℚ[X]).natDegree ≤
      (C (c i) : ℚ[X]).natDegree + (X ^ i.val : ℚ[X]).natDegree := natDegree_mul_le
  simp only [natDegree_C, natDegree_X_pow, zero_add] at h
  exact h.trans (by have := i.isLt; omega)

theorem one_selectedMultiplier_height_eq_inverseNorm
    (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    weightedCoefficientHeight n (selectedIntegerMultiplier n hn2 hn b a) =
      selectedInverseWeightedNorm n b a := by
  unfold weightedCoefficientHeight selectedInverseWeightedNorm
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrFun (selectedIntegerMultiplier_coordinates_product n hn2 hn b a) i
  change |((polynomialCoordinates (selectedIntegerMultiplier n hn2 hn b a)) i : ℝ)| *
      (n : ℝ) ^ (2 * i.val) = _
  rw [h]

theorem one_actualR_zero_of_pos_le (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.actualR n (k : ℚ) = 0 := by
  have hpred : ((k - 1 : ℕ) : ℚ) + 1 = (k : ℚ) := by
    exact_mod_cast (Nat.sub_add_cancel hk)
  have hfall : (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) = 0 := by
    apply Finset.prod_eq_zero (mem_range.mpr (by omega : k - 1 < n))
    rw [hpred]
    ring
  simp only [CoefficientMap.actualR, CoefficientMap.numerator, hfall,
    mul_zero, zero_mul, zero_div]

theorem one_actualR_pos_above_n (n k : ℕ) (hk : n < k) :
    0 < CoefficientMap.actualR n (k : ℚ) := by
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnfac : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfall : 0 < ∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1)) := by
    apply Finset.prod_pos
    intro i hi
    have hik : (i : ℚ) + 1 < k := by
      exact_mod_cast (show i + 1 < k by have := mem_range.mp hi; omega)
    linarith
  have hrise : 0 < ∏ i ∈ range n, ((k : ℚ) + n + ((i : ℚ) + 1)) := by
    apply Finset.prod_pos
    intro i hi
    positivity
  have hpole : 0 < CoefficientMap.poleProduct n (k : ℚ) := by
    unfold CoefficientMap.poleProduct
    apply Finset.prod_pos
    intro i hi
    positivity
  unfold CoefficientMap.actualR CoefficientMap.numerator
  positivity

theorem one_real_mapped_eval (W : ℚ[X]) (t : ℚ) :
    ((W.eval t : ℚ) : ℝ) = (W.map (Rat.castHom ℝ)).eval (t : ℝ) := by
  exact (Polynomial.eval_map_apply (p := W) (Rat.castHom ℝ) t).symm

theorem one_actualWeighted_tail_term (n : ℕ) (W : ℚ[X]) (j : ℕ) :
    actualWeightedSequence n W (j + n) =
      (CoefficientMap.actualR n ((j + n + 1 : ℕ) : ℚ) : ℝ) *
        (W.map (Rat.castHom ℝ)).eval
          (((j + n + 1 : ℕ) : ℝ) * (((j + n + 1 : ℕ) : ℝ) + n)) := by
  unfold actualWeightedSequence CoefficientMap.weightedR
  rw [Rat.cast_mul, one_real_mapped_eval]
  congr 2
  push_cast
  rfl

theorem one_actualWeighted_head_zero (n : ℕ) (W : ℚ[X]) :
    (∑ m ∈ range n, actualWeightedSequence n W m) = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have hm' : m + 1 ≤ n := by have := mem_range.mp hm; omega
  simp only [actualWeightedSequence, CoefficientMap.weightedR,
    one_actualR_zero_of_pos_le n (m + 1) (by omega) hm',
    zero_mul, Rat.cast_zero]

theorem one_actualWeighted_tail_center_le (n j : ℕ) :
    ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) ≤
      (((j + n + 1 : ℕ) : ℝ) * (((j + n + 1 : ℕ) : ℝ) + n)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hj : (0 : ℝ) ≤ j := by positivity
  have hjn : 0 ≤ (j : ℝ) * (n : ℝ) := mul_nonneg hj hn
  push_cast
  nlinarith [sq_nonneg (j : ℝ)]

/-- Uses the public Taylor-sign theorem on the strictly positive actual tail,
then removes the initial zero head and identifies the sum with the integer form. -/
theorem one_selected_actual_form_pos (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ)
    (hcoeff : ∀ i : ℕ, 0 ≤
      (Polynomial.taylor (((n : ℝ) + 1) * (2 * (n : ℝ) + 1))
        ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ))).coeff i)
    (hsample : 0 < ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ)).eval
      (((n : ℝ) + 2) * ((n : ℝ) + 2 + (n : ℝ)))) :
    0 < (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re := by
  let W : ℚ[X] := selectedIntegerMultiplier n hn2 hn b a
  let p : ℝ[X] := W.map (Rat.castHom ℝ)
  let R : ℕ → ℝ := fun j => (CoefficientMap.actualR n ((j + n + 1 : ℕ) : ℚ) : ℝ)
  let u : ℕ → ℝ := fun j =>
    ((j + n + 1 : ℕ) : ℝ) * (((j + n + 1 : ℕ) : ℝ) + n)
  let u0 : ℝ := ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)
  have hsum := (selectedIntegerMultiplier_actual_HasSum_and_absolute n hn2 hn b a).1
  have hsum' : Summable (actualWeightedSequence n W) := by
    change Summable (fun t : ℕ => (CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ))
    exact hsum.summable
  have htail : Summable (fun j : ℕ => R j * p.eval (u j)) := by
    have h := (summable_nat_add_iff n).2 hsum'
    apply h.congr
    intro j
    exact one_actualWeighted_tail_term n W j
  have hR : ∀ j : ℕ, 0 < R j := by
    intro j
    change 0 < (CoefficientMap.actualR n ((j + n + 1 : ℕ) : ℚ) : ℝ)
    exact_mod_cast one_actualR_pos_above_n n (j + n + 1) (by omega)
  have hu : ∀ j : ℕ, u0 ≤ u j := one_actualWeighted_tail_center_le n
  have hsample' : ∃ j : ℕ, 0 < p.eval (u j) := by
    refine ⟨1, ?_⟩
    have hu1 : u 1 = ((n : ℝ) + 2) * ((n : ℝ) + 2 + (n : ℝ)) := by
      dsimp [u]
      push_cast
      ring
    simpa only [hu1] using hsample
  have hpos := ZetaNine.taylor_sign_implies_kernel_sum_pos R u p u0 hR hu hcoeff htail hsample'
  have htail_eq : (∑' j : ℕ, R j * p.eval (u j)) =
      ∑' m : ℕ, actualWeightedSequence n W m := by
    have h := hsum'.sum_add_tsum_nat_add n
    rw [one_actualWeighted_head_zero n W, zero_add] at h
    calc
      (∑' j : ℕ, R j * p.eval (u j)) =
          ∑' j : ℕ, actualWeightedSequence n W (j + n) := by
        apply tsum_congr
        intro j
        exact (one_actualWeighted_tail_term n W j).symm
      _ = _ := h
  rw [htail_eq] at hpos
  have hvalue : (∑' m : ℕ, actualWeightedSequence n W m) =
      (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re := by
    simpa only [actualWeightedSequence, W, CoefficientMapSummation.zetaReal, Nat.cast_ofNat] using hsum.tsum_eq
  rwa [hvalue] at hpos

/-- The actual inverse cone/height margin supplies genuinely nonzero small
integer forms; no premise states smallness or nonvanishing of a zeta form. -/
theorem one_small_forms_of_selected_inverse_positive_cone_margin
    (hshort : SelectedInversePositiveConeMargin) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (m : ℝ))) := by
  obtain ⟨ε, hε, hA⟩ := actual_weighted_uniform_o_one
  obtain ⟨δ, hδ, hshort⟩ := hshort
  have hevent : ∀ᶠ n : ℕ in atTop, ε n < δ / 2 :=
    hε.eventually_lt_const (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨δ / 2, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  obtain ⟨n, hn2, hnEven, b, a, hNn, hnorm, hcoeff, hsample⟩ :=
    hshort (max m N)
  have hmn : m ≤ n := (le_max_left m N).trans hNn
  have hNn' : N ≤ n := (le_max_right m N).trans hNn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : ε n < δ / 2 := hN n hNn'
  have hpos := one_selected_actual_form_pos n hn2 hnEven b a hcoeff hsample
  refine ⟨b, a, ne_of_gt hpos, ?_⟩
  have hsum : (∑' j : ℕ,
      actualWeightedSequence n (selectedIntegerMultiplier n hn2 hnEven b a) j) =
        (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re := by
    simpa only [actualWeightedSequence, CoefficientMapSummation.zetaReal, Nat.cast_ofNat] using
      (selectedIntegerMultiplier_actual_HasSum_and_absolute n hn2 hnEven b a).1.tsum_eq
  have hbound := hA n (by omega) (selectedIntegerMultiplier n hn2 hnEven b a)
    (one_selectedMultiplier_degree_le n hn2 hnEven b a)
  calc
    |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| =
        |∑' j : ℕ, actualWeightedSequence n
          (selectedIntegerMultiplier n hn2 hnEven b a) j| := by rw [hsum]
    _ ≤ Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) *
        weightedCoefficientHeight n (selectedIntegerMultiplier n hn2 hnEven b a) := hbound
    _ = Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) *
        selectedInverseWeightedNorm n b a := by
      rw [one_selectedMultiplier_height_eq_inverseNorm]
    _ ≤ Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) *
        Real.exp (((2641 / 250 : ℝ) - δ) * n) :=
      mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _)
    _ = Real.exp ((ε n - δ) * n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ < Real.exp (-((δ / 2) * (n : ℝ))) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    _ ≤ Real.exp (-((δ / 2) * (m : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hmnReal : (m : ℝ) ≤ n := by exact_mod_cast hmn
      nlinarith

end ZetaNine.GraphBridge

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by
  exact ZetaNine.GraphBridge.one_small_forms_of_selected_inverse_positive_cone_margin
    ZetaNine.GraphBridge.selected_inverse_positive_cone_margin

