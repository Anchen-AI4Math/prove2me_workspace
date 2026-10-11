import SketchedParentV2
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open scoped BigOperators Matrix Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.GraphBridge ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapAggregate
open ZetaNine.AnalyticWeightedBound

/- Independent literal complete header applications; no head-only comparisons. -/
example (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    (selectedIntegerMultiplier n hn2 hn b a).natDegree ≤ 4 := by
  exact ZetaNine.GraphBridge.one_selectedMultiplier_degree_le n hn2 hn b a

example
    (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    weightedCoefficientHeight n (selectedIntegerMultiplier n hn2 hn b a) =
      selectedInverseWeightedNorm n b a := by
  exact ZetaNine.GraphBridge.one_selectedMultiplier_height_eq_inverseNorm n hn2 hn b a

example (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.actualR n (k : ℚ) = 0 := by
  exact ZetaNine.GraphBridge.one_actualR_zero_of_pos_le n k hk hkn

example (n k : ℕ) (hk : n < k) :
    0 < CoefficientMap.actualR n (k : ℚ) := by
  exact ZetaNine.GraphBridge.one_actualR_pos_above_n n k hk

example (W : ℚ[X]) (t : ℚ) :
    ((W.eval t : ℚ) : ℝ) = (W.map (Rat.castHom ℝ)).eval (t : ℝ) := by
  exact ZetaNine.GraphBridge.one_real_mapped_eval W t

example (n : ℕ) (W : ℚ[X]) (j : ℕ) :
    actualWeightedSequence n W (j + n) =
      (CoefficientMap.actualR n ((j + n + 1 : ℕ) : ℚ) : ℝ) *
        (W.map (Rat.castHom ℝ)).eval
          (((j + n + 1 : ℕ) : ℝ) * (((j + n + 1 : ℕ) : ℝ) + n)) := by
  exact ZetaNine.GraphBridge.one_actualWeighted_tail_term n W j

example (n : ℕ) (W : ℚ[X]) :
    (∑ m ∈ range n, actualWeightedSequence n W m) = 0 := by
  exact ZetaNine.GraphBridge.one_actualWeighted_head_zero n W

example (n j : ℕ) :
    ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) ≤
      (((j + n + 1 : ℕ) : ℝ) * (((j + n + 1 : ℕ) : ℝ) + n)) := by
  exact ZetaNine.GraphBridge.one_actualWeighted_tail_center_le n j

example (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ)
    (hcoeff : ∀ i : ℕ, 0 ≤
      (Polynomial.taylor (((n : ℝ) + 1) * (2 * (n : ℝ) + 1))
        ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ))).coeff i)
    (hsample : 0 < ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ)).eval
      (((n : ℝ) + 2) * ((n : ℝ) + 2 + (n : ℝ)))) :
    0 < (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re := by
  exact ZetaNine.GraphBridge.one_selected_actual_form_pos n hn2 hn b a hcoeff hsample

example
    (hshort : SelectedInversePositiveConeMargin) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (m : ℝ))) := by
  exact ZetaNine.GraphBridge.one_small_forms_of_selected_inverse_positive_cone_margin hshort

example : ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by
  exact solution

/- Independently expanded actual factorial kernel contract, all scales and valid head index. -/
example (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n.factorial : ℚ) ^ 7 *
      (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) *
      (∏ i ∈ range n, ((k : ℚ) + n + ((i : ℚ) + 1))) /
      (∏ j ∈ range (n + 1), ((k : ℚ) + j)) ^ 9 = 0 := by
  change CoefficientMap.actualR n (k : ℚ) = 0
  exact one_actualR_zero_of_pos_le n k hk hkn

/- Positivity is restricted to the true tail above n; the zero head was not erased. -/
example (n k : ℕ) (hk : n < k) :
    0 < (n.factorial : ℚ) ^ 7 *
      (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) *
      (∏ i ∈ range n, ((k : ℚ) + n + ((i : ℚ) + 1))) /
      (∏ j ∈ range (n + 1), ((k : ℚ) + j)) ^ 9 := by
  change 0 < CoefficientMap.actualR n (k : ℚ)
  exact one_actualR_pos_above_n n k hk

/- The head-zero claim is for the genuine weightedR, with every rational quartic allowed. -/
example (n : ℕ) (W : ℚ[X]) :
    (∑ m ∈ range n,
      (CoefficientMap.actualR n ((m + 1 : ℕ) : ℚ) *
        W.eval (((m + 1 : ℕ) : ℚ) * (((m + 1 : ℕ) : ℚ) + n)) : ℚ) : ℝ)) = 0 := by
  change (∑ m ∈ range n, actualWeightedSequence n W m) = 0
  exact one_actualWeighted_head_zero n W

/- Construction-scale choice needs only cofinality, with both target/error thresholds. -/
example (N m n : ℕ) (h : max m N ≤ n) : m ≤ n ∧ N ≤ n := by omega
