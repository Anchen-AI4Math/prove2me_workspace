import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipf_infinite_extension (s : ℝ) (hs : 0 ≤ s) :
    (Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s) ∧
      (1 < s → Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
        (nhds (riemannZeta s))) ∧
      (s ≤ 1 → Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop) := by sorry

end ZipfLaw
