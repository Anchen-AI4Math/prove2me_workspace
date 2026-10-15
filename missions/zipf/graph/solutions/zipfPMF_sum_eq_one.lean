import Theorems.Thm_ZipfLaw_zipfPMF_cdf
import Theorems.Thm_ZipfLaw_genHarmonic_pos
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, zipfPMF N s k = 1 := by
  rw [zipfPMF_cdf N hN s N le_rfl]
  exact div_self (genHarmonic_pos N hN s).ne'

#print axioms solution
