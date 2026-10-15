import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_ThreeSumSharpTail_full_d_call_total
import Theorems.Thm_ThreeSumSharpTail_full_d_extra_total
import Mathlib
open ThreeSumApsp Filter

theorem ThreeSumSharpTail.full_d_explicit_time (M : DetTimeModel) (a s : ℝ) (D g : ℕ → ℕ)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hDfloor : ∀ n, D n = ⌊(n : ℝ) ^ a⌋₊)
    (hgceil : ∀ n, 1 ≤ D n → g n = ⌈(D n : ℝ) ^ (s / 2)⌉₊)
    (hprime : Real.logb 2 7 + 3 * a / 2 ≤ 3 - a * s / 2)
    (hbuild : a * (1 + s) ≤ 1)
    (h17 : Claim.Theorem_17 M strassen D g)
    (hlop : ∃ (C : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ M.lopDetect Td ∧
      ∀ n d w : ℕ, 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ a →
        Td n d w ≤ C * ((n : ℝ) ^ 2 * (Real.log d + 1) ^ 2 / (d : ℝ) ^ s +
          (w : ℝ) * (d : ℝ) ^ (1 / 2 - s) * (Real.log d + 1) + (n : ℝ) * d + w + 1)) :
    ∃ n₀, Claim.Theorem_19_explicitAt M (a * s / 2) 2 n₀ := by sorry
