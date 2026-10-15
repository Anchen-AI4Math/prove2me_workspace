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

theorem ThreeSum.SparseBoxes.sparse_query_identity : ∀ {α : Type u_1} [inst : LinearOrder.{u_1} α] (q : Finset.{u_1} α) (t : Nat) (weight : Finset.{u_1} α → Int),
  @Eq.{1} Int (∑ leaf ∈ @Finset.powerset.{u_1} α q, weight leaf)
    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
      (∑ leaf ∈ @Finset.powerset.{u_1} α q with
        @LT.lt.{0} Nat instLTNat
          (@Finset.card.{u_1} α
            (@SDiff.sdiff.{u_1} (Finset.{u_1} α)
              (@Finset.instSDiff.{u_1} α fun (a b : α) => @LinearOrder.toDecidableEq.{u_1} α inst a b) q leaf))
          t,
        weight leaf)
      (∑ u ∈ @Finset.powersetCard.{u_1} α t q,
        @ThreeSum.SparseBoxes.boxSum.{u_1} α inst
          (@SDiff.sdiff.{u_1} (Finset.{u_1} α)
            (@Finset.instSDiff.{u_1} α fun (a b : α) => @LinearOrder.toDecidableEq.{u_1} α inst a b) q u)
          (@ThreeSum.SparseBoxes.queryFree.{u_1} α inst q u) weight)) := by
  sorry

