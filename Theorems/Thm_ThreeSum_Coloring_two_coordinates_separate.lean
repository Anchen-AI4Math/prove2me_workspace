import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Coloring.two_coordinates_separate : ∀ {α : Type u_1} {s t u : α → Bool} (hst : @Ne.{u_1 + 1} (α → Bool) s t) (hsu : @Ne.{u_1 + 1} (α → Bool) s u)
  (htu : @Ne.{u_1 + 1} (α → Bool) t u),
  ∃ (i : α) (j : α),
    And
      (@Ne.{1} (Prod.{0, 0} Bool Bool) (@Prod.mk.{0, 0} Bool Bool (s i) (s j)) (@Prod.mk.{0, 0} Bool Bool (t i) (t j)))
      (And
        (@Ne.{1} (Prod.{0, 0} Bool Bool) (@Prod.mk.{0, 0} Bool Bool (s i) (s j))
          (@Prod.mk.{0, 0} Bool Bool (u i) (u j)))
        (@Ne.{1} (Prod.{0, 0} Bool Bool) (@Prod.mk.{0, 0} Bool Bool (t i) (t j))
          (@Prod.mk.{0, 0} Bool Bool (u i) (u j)))) := by
  sorry

