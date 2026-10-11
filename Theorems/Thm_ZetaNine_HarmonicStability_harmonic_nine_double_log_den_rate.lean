import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false
open Filter
open ZetaNine.HarmonicStability

theorem ZetaNine.HarmonicStability.harmonic_nine_double_log_den_rate :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18):= by sorry
