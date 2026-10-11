import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false
open Filter
open ZetaNine.HarmonicStability

theorem ZetaNine.HarmonicStability.psi_pnt_rate :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1):= by sorry
