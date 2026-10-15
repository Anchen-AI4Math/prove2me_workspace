import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Theorems.Thm_ThreeSumSharpTail_full_d_call_balance
import Mathlib
open ThreeSumApsp

theorem ThreeSumSharpTail.full_d_extra_total (n D g : ℕ) (a s κ C : ℝ)
    (hn : 3 ≤ n) (hD : 1 ≤ D) (hDa : (D : ℝ) ≤ (n : ℝ) ^ a)
    (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hgLo : (D : ℝ) ^ (s / 2) ≤ g) (hgHi : (g : ℝ) ≤ 2 * (D : ℝ) ^ (s / 2))
    (hbuild : a * (1 + s) ≤ 1)
    (hprime : Real.logb 2 7 + 3 * a / 2 ≤ 3 - a * s / 2)
    (hκ : 1 ≤ κ) (hC : 0 ≤ C) :
    C * (termScans n g κ + termPrime strassen n D + termBuild n D g) ≤
      4 * C * (κ * ((n : ℝ) ^ 3 * (D : ℝ) ^ (-s / 2) * Real.log n ^ 2)) := by sorry
