import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_2

theorem ThreeSum.Reporting.frontier_nodup : ∀ {α : Type u_2} [DecidableEq.{u_2 + 1} α] (children : Nat → List.{u_2} α) (query : Nat → List.{u_2} α → Nat)
  (hc : ∀ (k : Nat), @List.Nodup.{u_2} α (children k)) (k : Nat),
  @List.Nodup.{u_2} (List.{u_2} α) (@ThreeSum.Reporting.frontier.{u_2} α children query k) := by
  sorry

