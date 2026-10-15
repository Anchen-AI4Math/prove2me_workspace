import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfPMF_entropy (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    -(∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log (zipfPMF N s k)) =
      s / genHarmonic N s * (∑ k ∈ Finset.Icc 1 N, Real.log k / (k : ℝ) ^ s) +
        Real.log (genHarmonic N s) := by sorry

end ZipfLaw
