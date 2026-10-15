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

theorem ThreeSum.Subset.unionConvolution_eq_disjointConvolution : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f g : Finset.{u_1} α → Int) (q : Finset.{u_1} α) (a b : Nat)
  (hf :
    ∀ (s : Finset.{u_1} α),
      @Ne.{1} Int (f s) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
        @Eq.{1} Nat (@Finset.card.{u_1} α s) a)
  (hg :
    ∀ (v : Finset.{u_1} α),
      @Ne.{1} Int (g v) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
        @Eq.{1} Nat (@Finset.card.{u_1} α v) b)
  (hq : @Eq.{1} Nat (@Finset.card.{u_1} α q) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b)),
  @Eq.{1} Int (@ThreeSum.Subset.unionConvolution.{u_1} α inst f g q)
    (@ThreeSum.Subset.disjointConvolution.{u_1} α inst f g q) := by
  sorry

