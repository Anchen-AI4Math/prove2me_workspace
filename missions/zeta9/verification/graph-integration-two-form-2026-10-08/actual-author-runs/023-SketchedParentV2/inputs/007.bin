import Definitions.Def_ZetaNine_GraphBridge_TwoForm
import Theorems.Thm_ZetaNine_GraphBridge_selected_inverse_unbounded_short_independent_pairs
import Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_coordinates_product
import Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute
import Theorems.Thm_ZetaNine_AnalyticWeightedBound_actual_weighted_uniform_o_one

/-!
SOURCE ONLY: no Lean invocation has validated this file.
The imported theorem modules are platform graph dependencies; their catalogue
placeholders are not represented as independent complete proof verification.
The conditional theorem below proves a genuine transfer from inverse coefficient
size to two small values. The only open input is the lattice/height margin.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix Topology
open Finset Polynomial Filter

namespace ZetaNine.GraphBridge
open CoefficientMapMatrix CoefficientMapAggregate CoefficientMapKernelBridge
open AnalyticWeightedBound

theorem selectedMultiplier_degree_le (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
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

theorem selectedMultiplier_weightedHeight_eq_inverseNorm
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

/-- The missing geometric margin is transferred through the actual polynomial,
actual sum identity and coefficient-uniform analytic bound. -/
theorem two_small_forms_of_selected_inverse_margin
    (hshort : SelectedInverseShortPairMargin) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ b₁ a₁ b₂ a₂ : ℤ,
          b₁ * a₂ ≠ b₂ * a₁ ∧
          |(b₁ : ℝ) + (a₁ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) ∧
          |(b₂ : ℝ) + (a₂ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by
  obtain ⟨ε, hε, hA⟩ := actual_weighted_uniform_o_one
  obtain ⟨δ, hδ, hshort⟩ := hshort
  have hevent : ∀ᶠ k : ℕ in atTop, ε k < δ / 2 :=
    hε.eventually_lt_const (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨δ / 2, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  obtain ⟨k, hNk, hk2, hkEven, b₁, a₁, b₂, a₂, hdet, hnorm₁, hnorm₂⟩ :=
    hshort (max n N)
  have hnk : n ≤ k := (le_max_left n N).trans hNk
  have hNk' : N ≤ k := (le_max_right n N).trans hNk
  have hkReal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have he : ε k < δ / 2 := hN k hNk'
  have hone : ∀ b a : ℤ,
      selectedInverseWeightedNorm k b a ≤ Real.exp (((2641 / 250 : ℝ) - δ) * k) →
      |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
        Real.exp (-((δ / 2) * (n : ℝ))) := by
    intro b a hnorm
    have hsum : (∑' m : ℕ,
        actualWeightedSequence k (selectedIntegerMultiplier k hk2 hkEven b a) m) =
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re := by
      simpa only [actualWeightedSequence, CoefficientMapSummation.zetaReal, Nat.cast_ofNat] using
        (selectedIntegerMultiplier_actual_HasSum_and_absolute k hk2 hkEven b a).1.tsum_eq
    have hbound := hA k (by omega) (selectedIntegerMultiplier k hk2 hkEven b a)
      (selectedMultiplier_degree_le k hk2 hkEven b a)
    calc
      |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| =
          |∑' m : ℕ, actualWeightedSequence k
            (selectedIntegerMultiplier k hk2 hkEven b a) m| := by rw [hsum]
      _ ≤ Real.exp ((-(2641 / 250 : ℝ) + ε k) * k) *
          weightedCoefficientHeight k (selectedIntegerMultiplier k hk2 hkEven b a) := hbound
      _ = Real.exp ((-(2641 / 250 : ℝ) + ε k) * k) *
          selectedInverseWeightedNorm k b a := by
        rw [selectedMultiplier_weightedHeight_eq_inverseNorm]
      _ ≤ Real.exp ((-(2641 / 250 : ℝ) + ε k) * k) *
          Real.exp (((2641 / 250 : ℝ) - δ) * k) :=
        mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _)
      _ = Real.exp ((ε k - δ) * k) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ < Real.exp (-((δ / 2) * (k : ℝ))) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      _ ≤ Real.exp (-((δ / 2) * (n : ℝ))) := by
        apply Real.exp_le_exp.mpr
        have hnkReal : (n : ℝ) ≤ k := by exact_mod_cast hnk
        nlinarith
  exact ⟨b₁, a₁, b₂, a₂, hdet, hone b₁ a₁ hnorm₁, hone b₂ a₂ hnorm₂⟩

end ZetaNine.GraphBridge

namespace ZetaNine

/-- Candidate replacement sketch for the existing Open two-form leaf.
The only still Open dependency is the inverse lattice margin. -/
theorem exponentially_small_independent_forms_of_zeta_nine :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b₁ a₁ b₂ a₂ : ℤ,
          b₁ * a₂ ≠ b₂ * a₁ ∧
          |(b₁ : ℝ) + (a₁ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) ∧
          |(b₂ : ℝ) + (a₂ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by
  exact GraphBridge.two_small_forms_of_selected_inverse_margin
    GraphBridge.selected_inverse_unbounded_short_independent_pairs

end ZetaNine
