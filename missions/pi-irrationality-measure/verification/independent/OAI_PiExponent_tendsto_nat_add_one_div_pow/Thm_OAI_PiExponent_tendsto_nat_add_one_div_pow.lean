import Mathlib.Analysis.SpecificLimits.Normed

open Filter Topology


theorem OAI.PiExponent.tendsto_nat_add_one_div_pow {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (𝓝 0) := by sorry
