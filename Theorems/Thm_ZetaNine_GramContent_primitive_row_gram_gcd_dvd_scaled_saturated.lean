import Definitions.Def_ZetaNine_GramContent
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
open scoped BigOperators
open ZetaNine.GramContent

set_option autoImplicit false

theorem ZetaNine.GramContent.primitive_row_gram_gcd_dvd_scaled_saturated {ι : Type*} [Fintype ι] (u v : ι → ℤ) (Δ : ℤ)
    (hprimitive : ∃ a : ι → ℤ, (∑ i, a i * u i) = 1) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (Int.gcd (normSq u) (dot u v) : ℤ) ∣ Δ * saturatedGram u v Δ := by sorry
