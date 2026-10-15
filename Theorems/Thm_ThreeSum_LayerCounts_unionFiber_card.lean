import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false


theorem ThreeSum.LayerCounts.unionFiber_card : ∀ {L h : Nat} (Q : Finset.{0} (Fin L))
  (hQ :
    @Eq.{1} Nat (@Finset.card.{0} (Fin L) Q)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)),
  @Eq.{1} Nat
    (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)))
      ({p ∈ ThreeSum.LayerCounts.edgeSet L h |
        @Eq.{1} (Finset.{0} (Fin L))
          (@Union.union.{0} (Finset.{0} (Fin L)) (@Finset.instUnion.{0} (Fin L) (instDecidableEqFin L))
            (@Prod.fst.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p)
            (@Prod.snd.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p))
          Q}))
    ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h).choose
      h) := by
  sorry

