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

theorem ThreeSum.Subset.mobius_zeta : ∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] (f : Finset.{u_1} α → Int) (q : Finset.{u_1} α),
  @Eq.{1} Int (@ThreeSum.Subset.mobius.{u_1} α (@ThreeSum.Subset.zeta.{u_1} α f) q) (f q) := by
  sorry

