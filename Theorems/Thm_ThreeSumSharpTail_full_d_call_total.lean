import Mathlib
import Theorems.Thm_ThreeSumSharpTail_full_d_call_balance
set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.full_d_call_total (n D g s C C' t w : ℝ)
    (hD : 1 ≤ D) (hn : 1 ≤ n) (hs : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hgLo : D ^ (s / 2) ≤ g) (hgHi : g ≤ 2 * D ^ (s / 2))
    (hbuild : D ^ (1 + s) ≤ n) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (_hw0 : 0 ≤ w) (hw : w ≤ n ^ 2 / Real.sqrt D)
    (ht : t ≤ C *
      (n ^ 2 * (Real.log D + 1) ^ 2 / D ^ s +
        w * D ^ (1 / 2 - s) * (Real.log D + 1) + n * D + w + 1)) :
    4 * n * g * (t + C' * n ^ 2 / Real.sqrt D) ≤
      (64 * C + 8 * C') *
        (n ^ 3 * D ^ (-s / 2) * (Real.log D + 1) ^ 2) := by sorry
