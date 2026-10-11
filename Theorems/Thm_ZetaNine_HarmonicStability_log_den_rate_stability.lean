import Definitions.Def_ZetaNine_HarmonicStability
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open scoped BigOperators
open Filter
open ZetaNine.HarmonicStability

set_option autoImplicit false

theorem ZetaNine.HarmonicStability.log_den_rate_stability {ι : Type*} (l : Filter ι)
    (h r : ι → ℚ) (scale : ι → ℝ) (hscale : ∀ i, 0 ≤ scale i) (a : ℝ)
    (hh : Tendsto (fun i => logDen (h i) / scale i) l (nhds a))
    (hr : Tendsto (fun i => logDen (r i) / scale i) l (nhds 0)) :
    Tendsto (fun i => logDen (h i + r i) / scale i) l (nhds a) := by sorry
