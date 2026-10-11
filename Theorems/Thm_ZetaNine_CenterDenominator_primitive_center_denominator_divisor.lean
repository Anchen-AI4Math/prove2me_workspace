import Definitions.Def_ZetaNine_GramContent
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
open scoped BigOperators
open ZetaNine.GramContent

set_option autoImplicit false

theorem ZetaNine.CenterDenominator.primitive_center_denominator_divisor {ι : Type*} [Fintype ι] (u v : ι → ℤ) (a b Δ : ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1)
    (ha : a ≠ 0) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (normSq u).natAbs /
        Int.gcd (normSq u) (b * Δ * saturatedGram u v Δ) ∣
      (Rat.divInt (b * dot u v) (a * normSq u)).den := by sorry
