import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_mode (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    zipfPMF N s k ≤ zipfPMF N s 1 := by sorry

end ZipfLaw
