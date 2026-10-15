import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_variance (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * zipfPMF N s k) -
        (∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k) ^ 2 =
      genHarmonic N (s - 2) / genHarmonic N s -
        genHarmonic N (s - 1) ^ 2 / genHarmonic N s ^ 2 := by sorry

end ZipfLaw
