import OneFormBridgeSource

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.GraphBridge ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapAggregate
open ZetaNine.AnalyticWeightedBound

/-! UNCOMPILED exact complete type applications. No Lean execution yet. -/

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

/- Boundary: actual kernel zero head at smallest even scale. -/
example : CoefficientMap.actualR 2 (1 : ℚ) = 0 :=
  one_actualR_zero_of_pos_le 2 1 (by omega) (by omega)
example : CoefficientMap.actualR 2 (2 : ℚ) = 0 :=
  one_actualR_zero_of_pos_le 2 2 (by omega) (by omega)
example : 0 < CoefficientMap.actualR 2 (3 : ℚ) :=
  one_actualR_pos_above_n 2 3 (by omega)
example : CoefficientMap.actualR 0 (1 : ℚ) > 0 :=
  one_actualR_pos_above_n 0 1 (by omega)
example : (∑ m ∈ range 0, actualWeightedSequence 0 (0 : ℚ[X]) m) = 0 :=
  one_actualWeighted_head_zero 0 0
example : (((2 : ℝ)+1)*(2*2+1)) < (((2 : ℝ)+2)*((2 : ℝ)+2+2)) := by norm_num
example : ∀ j : ℕ, (((2 : ℝ)+1)*(2*2+1)) ≤
    (((j+2+1:ℕ):ℝ)*(((j+2+1:ℕ):ℝ)+2)) :=
  one_actualWeighted_tail_center_le 2

#print axioms ZetaNine.GraphBridge.one_selectedMultiplier_degree_le
#print axioms ZetaNine.GraphBridge.one_selectedMultiplier_height_eq_inverseNorm
#print axioms ZetaNine.GraphBridge.one_actualR_zero_of_pos_le
#print axioms ZetaNine.GraphBridge.one_actualR_pos_above_n
#print axioms ZetaNine.GraphBridge.one_real_mapped_eval
#print axioms ZetaNine.GraphBridge.one_actualWeighted_tail_term
#print axioms ZetaNine.GraphBridge.one_actualWeighted_head_zero
#print axioms ZetaNine.GraphBridge.one_actualWeighted_tail_center_le
#print axioms ZetaNine.GraphBridge.one_selected_actual_form_pos
#print axioms ZetaNine.GraphBridge.one_small_forms_of_selected_inverse_positive_cone_margin
