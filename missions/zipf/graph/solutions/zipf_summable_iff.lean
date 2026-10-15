import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw

theorem solution (s : ℝ) (hs : 0 ≤ s) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s := by
  have h := Real.summable_one_div_nat_add_rpow 1 s
  have habs : ∀ k : ℕ, |(k : ℝ) + 1| = (k : ℝ) + 1 := fun k =>
    abs_of_pos (by positivity)
  simpa only [habs] using h

#print axioms solution
