import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipf_genHarmonic_tendsto_atTop (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop := by sorry

end ZipfLaw
