import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.full_d_call_balance (D n g s : ℝ)
    (hD : 1 ≤ D) (_hn : 1 ≤ n) (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hgLo : D ^ (s / 2) ≤ g) (hgHi : g ≤ 2 * D ^ (s / 2))
    (hbuild : D ^ (1 + s) ≤ n) :
    g / D ^ s ≤ 2 * D ^ (-s / 2) ∧
    g * D ^ (1 / 2 - s) / Real.sqrt D ≤ 2 * D ^ (-s / 2) ∧
    g / Real.sqrt D ≤ 2 * D ^ (-s / 2) ∧
    g * D ≤ 2 * n * D ^ (-s / 2) ∧
    1 / g ≤ D ^ (-s / 2) := by sorry
