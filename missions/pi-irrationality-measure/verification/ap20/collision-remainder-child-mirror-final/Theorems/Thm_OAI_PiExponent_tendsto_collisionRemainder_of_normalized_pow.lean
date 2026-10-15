import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_tendsto_log_div_of_normalized_pow

namespace OAI

open Filter Topology
open scoped BigOperators

namespace PiExponent

private theorem tendsto_log_add_div_of_normalized_pow {f : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ d) atTop (𝓝 L)) (hL : 0 < L) (C : ℝ) :
    Tendsto (fun H : ℝ => (Real.log (f H) + C) / H) atTop (𝓝 0) := by
  have h := (tendsto_log_div_of_normalized_pow hf hL).add
    (tendsto_id.const_div_atTop C)
  simpa only [add_zero, add_div, id_eq] using h

end PiExponent

end OAI

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent

theorem tendsto_collisionRemainder_of_normalized_pow {M : ℝ → ℕ} {d : ℕ} {L : ℝ}
    (hM : Tendsto (fun H : ℝ => (M H : ℝ) / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H => Collision.collisionRemainder (M H) H) atTop (𝓝 0) := by
  convert tendsto_log_add_div_of_normalized_pow hM hL
    (Real.log 2 / 4 - Real.log (1 - Collision.collisionRatio)) using 1
  funext H
  unfold Collision.collisionRemainder
  congr 1
  ring

end PiExponent

end OAI
