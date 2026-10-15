import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Subset.partialZeta_forced_prefix : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f : Finset.{u_1} α → Int) (processed s₀ t : Finset.{u_1} α)
  (hs : @Disjoint.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α) (@Finset.instOrderBot.{u_1} α) s₀ processed)
  (ht :
    @LE.le.{u_1} (Finset.{u_1} α)
      (@Preorder.toLE.{u_1} (Finset.{u_1} α)
        (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α)))
      t processed),
  @Eq.{1} Int
    (@ThreeSum.Subset.partialZeta.{u_1} α inst processed f
      (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) s₀ t))
    (∑ x ∈ @Finset.powerset.{u_1} α t, f (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) s₀ x)) := by
  sorry

