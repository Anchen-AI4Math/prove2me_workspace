import Mathlib

theorem ThreeSumSharpTail.rational_power_representation (a s : ℚ) (ha0 : 0 < a) (ha1 : a < 1)
    (hs0 : 0 < s) (hsHalf : s < 1 / 2) :
    ∃ A B c e : ℕ, 1 ≤ B ∧ 1 ≤ e ∧ A ≤ B ∧ 2 * c ≤ e ∧
      (A : ℝ) / B = (a : ℝ) ∧ (c : ℝ) / e = (s : ℝ) / 2 ∧
      ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
        ((D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) ↔ D ^ B ≤ N ^ A) := by sorry
