import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open Filter Topology
open OAI.PiExponent

theorem OAI.PiExponent.tendsto_log_translationTermCount_div (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => Real.log (translationTermCount m v H : ℝ) / H)
      atTop (𝓝 0) := by
  sorry
