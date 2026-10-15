import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
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
import Theorems.Thm_ThreeSum_Reporting_frontier_nodup
import Theorems.Thm_ThreeSum_Reporting_mem_frontier_iff


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.Reporting.frontier_length_le_mass : ∀ {ι : Type u_1} {α : Type u_2} [inst : DecidableEq.{u_2 + 1} α] (I : Finset.{u_1} ι) (word : ι → List.{u_2} α)
  (weight : ι → Nat) (children : Nat → List.{u_2} α) (query : Nat → List.{u_2} α → Nat) (J k : Nat)
  (hlen :
    ∀ (i : ι),
      @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i →
        @Eq.{1} Nat (@List.length.{u_2} α (word i)) J)
  (hchildren :
    ∀ (i : ι)
      (hi :
        @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i)
      (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j J),
      @Membership.mem.{u_2, u_2} α (List.{u_2} α) (@List.instMembership.{u_2} α) (children j)
        (@GetElem.getElem.{u_2, 0, u_2} (List.{u_2} α) Nat α
          (fun (as : List.{u_2} α) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{u_2} α as))
          (@List.instGetElemNatLtLength.{u_2} α) (word i) j
          (@Eq.mpr.{0} (@LT.lt.{0} Nat instLTNat j (@List.length.{u_2} α (word i))) (@LT.lt.{0} Nat instLTNat j J)
            (@id.{0}
              (@Eq.{1} Prop (@LT.lt.{0} Nat instLTNat j (@List.length.{u_2} α (word i))) (@LT.lt.{0} Nat instLTNat j J))
              (@congrArg.{1, 1} Nat Prop (@List.length.{u_2} α (word i)) J
                (fun (_a : Nat) => @LT.lt.{0} Nat instLTNat j _a) (hlen i hi)))
            hj)))
  (hquery :
    ∀ (j : Nat),
      @LE.le.{0} Nat instLENat j J →
        ∀ (pre : List.{u_2} α),
          @Eq.{1} Nat (query j pre) (@ThreeSum.Reporting.mass.{u_1, u_2} ι α inst I word weight j pre))
  (hc : ∀ (k : Nat), @List.Nodup.{u_2} α (children k)) (hk : @LE.le.{0} Nat instLENat k J),
  @LE.le.{0} Nat instLENat (@List.length.{u_2} (List.{u_2} α) (@ThreeSum.Reporting.frontier.{u_2} α children query k))
    (∑ i ∈ I, weight i) := by
  sorry

