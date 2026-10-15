import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Theorems.Thm_ThreeSum_LayerCounts_leftFiber_card


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false


theorem ThreeSum.LayerCounts.rightFiber_card : ∀ {L h : Nat} (V : Finset.{0} (Fin L)) (hV : @Eq.{1} Nat (@Finset.card.{0} (Fin L) V) h),
  @Eq.{1} Nat
    (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)))
      ({p ∈ ThreeSum.LayerCounts.edgeSet L h |
        @Eq.{1} (Finset.{0} (Fin L)) (@Prod.snd.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p) V}))
    ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L h).choose h) := by
  sorry

