import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem yuleSimon_tail (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧
      Asymptotics.IsEquivalent Filter.atTop (fun k : ℕ => yuleSimonPMF ρ k)
        (fun k : ℕ => C / (k : ℝ) ^ (ρ + 1)) := by sorry

end ZipfLaw
