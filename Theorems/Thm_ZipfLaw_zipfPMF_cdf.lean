import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_cdf (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (n : ℕ) (hn : n ≤ N) :
    ∑ k ∈ Finset.Icc 1 n, zipfPMF N s k = genHarmonic n s / genHarmonic N s := by sorry

end ZipfLaw
