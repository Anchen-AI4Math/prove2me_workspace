import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_3

theorem ThreeSum.HashFamily.badPartners_card_le : ∀ {α : Type u_1} {E : Type u_3} [inst : Fintype.{u_3} E] [DecidableEq.{u_3 + 1} E] [inst_2 : Fintype.{u_1} α]
  [DecidableEq.{u_1 + 1} α] (left right : E → α → Bool) (e : E) (Delta G : Nat)
  (hL : @LE.le.{0} Nat instLENat (@Finset.card.{u_3} E {f : E | @Eq.{u_1 + 1} (α → Bool) (left e) (left f)}) Delta)
  (hR : @LE.le.{0} Nat instLENat (@Finset.card.{u_3} E {f : E | @Eq.{u_1 + 1} (α → Bool) (right e) (right f)}) Delta)
  (hG :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{u_3} E
        {f : E |
          @Eq.{u_1 + 1} (α → Bool) (@ThreeSum.HashFamily.outputMask.{u_1, u_3} α E left right e)
            (@ThreeSum.HashFamily.outputMask.{u_1, u_3} α E left right f)})
      G),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{u_3} E (@ThreeSum.HashFamily.badPartners.{u_1, u_3} α E inst inst_2 left right e))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Delta)
      G) := by
  sorry

