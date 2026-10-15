import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_ratio (N : ℕ) (s : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    zipfPMF N s 1 / zipfPMF N s n = (n : ℝ) ^ s := by sorry

end ZipfLaw
