import Definitions.Def_ZetaNine_AnalyticPhase
set_option autoImplicit false
open Set
open ZetaNine.AnalyticPhase

theorem ZetaNine.AnalyticPhase.phase_global_upper_bound :
    ∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ) := by sorry
