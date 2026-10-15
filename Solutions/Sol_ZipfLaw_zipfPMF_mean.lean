import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

private lemma moment_sum (N : ℕ) (s : ℝ) (p : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ p * zipfPMF N s k) =
      genHarmonic N (s - p) / genHarmonic N s := by
  rw [genHarmonic, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
    exact_mod_cast this
  rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk), Real.rpow_sub hkpos, Real.rpow_natCast]
  simp only [one_div_div]
  ring

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k =
      genHarmonic N (s - 1) / genHarmonic N s := by
  simpa only [Nat.cast_one, pow_one] using moment_sum N s 1

#print axioms solution

