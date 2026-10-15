import Theorems.Thm_ZipfLaw_zipfPMF_moment
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k = genHarmonic N (s - 1) / genHarmonic N s := by
  simpa only [Nat.cast_one, pow_one] using zipfPMF_moment N s 1

#print axioms solution
