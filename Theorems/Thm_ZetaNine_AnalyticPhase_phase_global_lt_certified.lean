import Definitions.Def_ZetaNine_AnalyticPhase
set_option autoImplicit false
open Set
open ZetaNine.AnalyticPhase

theorem ZetaNine.AnalyticPhase.phase_global_lt_certified (x : ℝ) (hx : 1 < x) :
    phase x < (-10564011 / 1000000 : ℝ) := by sorry
