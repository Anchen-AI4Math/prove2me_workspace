import Definitions.Def_ZetaNine_GraphBridge_OneForm
import Theorems.Thm_ZetaNine_GraphBridge_selected_inverse_positive_cone_margin
import OneFormBridgeSource

/-! SOURCE ONLY, waiting for Root's actual Lean lane grant. -/

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by
  exact ZetaNine.GraphBridge.one_small_forms_of_selected_inverse_positive_cone_margin
    ZetaNine.GraphBridge.selected_inverse_positive_cone_margin
