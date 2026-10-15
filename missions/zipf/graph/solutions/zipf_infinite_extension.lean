import Theorems.Thm_ZipfLaw_zipf_summable_iff
import Theorems.Thm_ZipfLaw_zipf_genHarmonic_tendsto_zeta
import Theorems.Thm_ZipfLaw_zipf_genHarmonic_tendsto_atTop
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (s : ℝ) (hs : 0 ≤ s) :
    (Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s) ∧
      (1 < s → Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
        (nhds (riemannZeta s))) ∧
      (s ≤ 1 → Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop) := by
  exact ⟨zipf_summable_iff s hs,
    fun hs1 => zipf_genHarmonic_tendsto_zeta s hs1,
    fun hs1 => zipf_genHarmonic_tendsto_atTop s hs hs1⟩

#print axioms solution
