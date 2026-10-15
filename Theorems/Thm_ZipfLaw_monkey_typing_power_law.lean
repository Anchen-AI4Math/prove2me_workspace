import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem monkey_typing_power_law (m : ℕ) (hm : 2 ≤ m) (q : ℝ) (hq : 0 < q) (hmq : (m : ℝ) * q < 1)
    (e : ℕ → List (Fin m)) (he_inj : Function.Injective e)
    (he_range : Set.range e = {w | w ≠ []})
    (he_sorted : Antitone (fun r => monkeyWordProb m q (e r))) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ r : ℕ,
      C₁ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) ≤ monkeyWordProb m q (e r) ∧
        monkeyWordProb m q (e r) ≤ C₂ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) := by sorry

end ZipfLaw
