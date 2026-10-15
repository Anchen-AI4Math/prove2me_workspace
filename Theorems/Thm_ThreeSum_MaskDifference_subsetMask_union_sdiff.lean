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


theorem ThreeSum.MaskDifference.subsetMask_union_sdiff : ∀ {L : Nat} (Q U : Finset.{0} (Fin L))
  (hU :
    @LE.le.{0} (Finset.{0} (Fin L))
      (@Preorder.toLE.{0} (Finset.{0} (Fin L))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin L)) (@Finset.instPartialOrder.{0} (Fin L))))
      U Q),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@ThreeSum.SubsetAddress.subsetMask L U)
      (@ThreeSum.SubsetAddress.subsetMask L
        (@SDiff.sdiff.{0} (Finset.{0} (Fin L)) (@Finset.instSDiff.{0} (Fin L) (instDecidableEqFin L)) Q U)))
    (@ThreeSum.SubsetAddress.subsetMask L Q) := by
  sorry

