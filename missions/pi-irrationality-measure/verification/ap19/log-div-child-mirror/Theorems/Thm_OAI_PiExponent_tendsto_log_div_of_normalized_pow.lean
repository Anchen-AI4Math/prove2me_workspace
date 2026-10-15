import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

namespace OAI.PiExponent

open Filter Topology
open scoped BigOperators

theorem tendsto_log_div_of_normalized_pow {f : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H : ℝ => Real.log (f H) / H) atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℝ => Real.log (f H / H ^ d)) atTop (𝓝 (Real.log L)) :=
    (Real.continuousAt_log hL.ne').tendsto.comp hf
  have hslow : Tendsto (fun H : ℝ => Real.log H / H) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h := (hlog.div_atTop tendsto_id).add (hslow.const_mul (d : ℝ))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hf.eventually (eventually_ne_nhds hL.ne')] with H hH hn
  have hfne : f H ≠ 0 := by
    intro hz
    apply hn
    simp [hz]
  rw [Real.log_div hfne (pow_ne_zero _ hH.ne'), Real.log_pow]
  simp only [id_eq]
  ring

end OAI.PiExponent
