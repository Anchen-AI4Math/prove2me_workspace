import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_ThreeSumSharpTail_pruned_encoding_comparison
set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSumApsp
open ThreeSumSharpTail

theorem ThreeSumSharpTail.pruned_cost_certificate (c : ℕ) (θ : ℝ) (a s : ℚ)
    (hc : 10 < c) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (ha0 : 0 < a)
    (henc : (a : ℝ) * (encodingExponent c + sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - queryExponent θ) :
    ∃ C m₀, 0 ≤ C ∧ ∀ D₀ N m : ℕ,
      2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf (c : ℝ) m) m ≤ N ∧
      cost8p (levelsOf (c : ℝ) m) m (switchOf θ m) N ≤
        C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ (s : ℝ)) ∧
      costQuery (levelsOf (c : ℝ) m) m (switchOf θ m) ≤
        C * ((D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) * Real.log (D₀ : ℝ)) := by sorry
