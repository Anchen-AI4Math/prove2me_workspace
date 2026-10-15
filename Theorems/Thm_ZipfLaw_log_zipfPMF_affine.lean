import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem log_zipfPMF_affine (N : ℕ) (s : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.log (zipfPMF N s k) = -s * Real.log k - Real.log (genHarmonic N s) := by sorry

end ZipfLaw
