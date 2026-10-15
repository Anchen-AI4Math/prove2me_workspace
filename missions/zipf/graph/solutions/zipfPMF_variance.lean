import Theorems.Thm_ZipfLaw_zipfPMF_moment
import Theorems.Thm_ZipfLaw_zipfPMF_mean
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * zipfPMF N s k) -
        (∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k) ^ 2 =
      genHarmonic N (s - 2) / genHarmonic N s -
        genHarmonic N (s - 1) ^ 2 / genHarmonic N s ^ 2 := by
  rw [zipfPMF_moment N s 2, zipfPMF_mean N hN s, div_pow]
  norm_num

#print axioms solution
