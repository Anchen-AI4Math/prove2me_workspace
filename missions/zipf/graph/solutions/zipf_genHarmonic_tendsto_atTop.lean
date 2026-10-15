import Theorems.Thm_ZipfLaw_zipf_summable_iff
import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

private lemma harmonic_range (N : ℕ) (s : ℝ) :
    genHarmonic N s = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ s := by
  induction N with
  | zero => simp [genHarmonic]
  | succ N ih =>
    change (∑ k ∈ Finset.Icc 1 (N + 1), 1 / (k : ℝ) ^ s) = _
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ]
    change genHarmonic N s + 1 / ((N + 1 : ℕ) : ℝ) ^ s = _
    rw [ih]
    simp

theorem solution (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop := by
  have hnot : ¬Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) := by
    rw [zipf_summable_iff s hs]
    exact not_lt_of_ge hs1
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k : ℕ => by positivity : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 1) ^ s)).mp hnot
  simpa only [← harmonic_range] using hdiv

#print axioms solution
