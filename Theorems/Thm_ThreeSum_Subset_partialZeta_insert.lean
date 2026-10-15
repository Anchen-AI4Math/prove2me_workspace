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

theorem ThreeSum.Subset.partialZeta_insert : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f : Finset.{u_1} α → Int) (u processed : Finset.{u_1} α) (a : α)
  (ha : a ∉ processed),
  @Eq.{1} Int
    (@ThreeSum.Subset.partialZeta.{u_1} α inst
      (@Insert.insert.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instInsert.{u_1} α inst) a processed) f u)
    (@ThreeSum.Subset.zetaStep.{u_1} α inst a (@ThreeSum.Subset.partialZeta.{u_1} α inst processed f) u) := by
  sorry

