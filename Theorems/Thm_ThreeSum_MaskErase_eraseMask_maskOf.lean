import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress


theorem ThreeSum.MaskErase.eraseMask_maskOf : ∀ {L : Nat} (s : Finset.{0} Nat)
  (hs :
    @LE.le.{0} (Finset.{0} Nat)
      (@Preorder.toLE.{0} (Finset.{0} Nat)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
      s (Finset.range L))
  (a : Nat),
  @Eq.{1} Nat (ThreeSum.MaskErase.eraseMask L a (ThreeSum.SubsetAddress.maskOf s))
    (ThreeSum.SubsetAddress.maskOf (@Finset.erase.{0} Nat instDecidableEqNat s a)) := by
  sorry

