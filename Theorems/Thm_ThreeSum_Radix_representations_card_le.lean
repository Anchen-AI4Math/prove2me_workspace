import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Radix.representations_card_le : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] [inst_1 : DecidableEq.{u_1 + 1} Ω] (p : Int) (left right : Ω → Int) (B : Nat)
  (hcap :
    ∀ (a b : Int),
      @LE.le.{0} Nat instLENat (@Finset.card.{u_1} Ω (@ThreeSum.Radix.localFiber.{u_1} Ω inst p left right a b)) B)
  (j : Nat) (a b : Int),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{u_1} (List.{u_1} Ω) (@ThreeSum.Radix.representations.{u_1} Ω inst inst_1 p left right j a b))
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) B j) := by
  sorry

