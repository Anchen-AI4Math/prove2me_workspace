import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614


theorem ThreeSum1960614.integer_schedule (J s j : ℕ)
    (hJ : 0 < J) (hs : 0 < s) (heven : Even s) (hj : j < J)
    (hlevel : (j : ℝ) / J ≤ tau) :
    ∃ q : ℕ, 0 < q ∧ q ≤ ((J - j) * s) / 2 ∧ clearedSwitch J s j q ∧
      (∀ k < q, ¬ clearedSwitch J s j k) ∧
      threshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / ((J - j) * s)) ∧
      phi ((q : ℝ) / ((J - j) * s)) <
        threshold ((j : ℝ) / J) + 9 / ((J - j) * s) ∧
      saving ≤ 2 * beta - (j : ℝ) / J +
        (1 - (j : ℝ) / J) * gamma 232 ((q : ℝ) / ((J - j) * s)) ∧
      (1 - (j : ℝ) / J) * entropy ((q : ℝ) / ((J - j) * s)) <
        rho * (1 + v) + 9 * rho / (J * s) := by sorry
