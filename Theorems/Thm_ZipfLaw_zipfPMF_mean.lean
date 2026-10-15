import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_mean (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k = genHarmonic N (s - 1) / genHarmonic N s := by sorry

end ZipfLaw
