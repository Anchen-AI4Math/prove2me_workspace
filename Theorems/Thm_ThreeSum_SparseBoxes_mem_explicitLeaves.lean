import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.SparseBoxes.mem_explicitLeaves : ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] (q leaf : Finset.{u_1} α) (t : Nat),
  Iff
    (@Membership.mem.{u_1, u_1} (Finset.{u_1} α) (Finset.{u_1} (Finset.{u_1} α))
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (Finset.{u_1} α)) (Finset.{u_1} α)
        (@Finset.instSetLike.{u_1} (Finset.{u_1} α)))
      (@ThreeSum.SparseBoxes.explicitLeaves.{u_1} α inst q t) leaf)
    (And
      (@LE.le.{u_1} (Finset.{u_1} α)
        (@Preorder.toLE.{u_1} (Finset.{u_1} α)
          (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α)))
        leaf q)
      (@LT.lt.{0} Nat instLTNat
        (@Finset.card.{u_1} α
          (@SDiff.sdiff.{u_1} (Finset.{u_1} α)
            (@Finset.instSDiff.{u_1} α fun (a b : α) => @LinearOrder.toDecidableEq.{u_1} α inst a b) q leaf))
        t)) := by
  sorry

