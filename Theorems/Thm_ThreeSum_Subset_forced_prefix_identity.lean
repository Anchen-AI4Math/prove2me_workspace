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
import Theorems.Thm_ThreeSum_Subset_mobius_zeta
import Theorems.Thm_ThreeSum_Subset_partialZeta_forced_prefix
import Theorems.Thm_ThreeSum_Subset_unionConvolution_eq_disjointConvolution


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Subset.forced_prefix_identity : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f g : Finset.{u_1} α → Int)
  (prefix₁ prefix₂ suffix q : Finset.{u_1} α) (a b : Nat)
  (hf :
    ∀ (s : Finset.{u_1} α),
      @Ne.{1} Int (f s) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
        @Eq.{1} Nat (@Finset.card.{u_1} α s) a)
  (hg :
    ∀ (v : Finset.{u_1} α),
      @Ne.{1} Int (g v) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
        @Eq.{1} Nat (@Finset.card.{u_1} α v) b)
  (hd₁ :
    @Disjoint.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α) (@Finset.instOrderBot.{u_1} α) prefix₁ suffix)
  (hd₂ :
    @Disjoint.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α) (@Finset.instOrderBot.{u_1} α) prefix₂ suffix)
  (hqs :
    @LE.le.{u_1} (Finset.{u_1} α)
      (@Preorder.toLE.{u_1} (Finset.{u_1} α)
        (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α)))
      q suffix)
  (hq :
    @Eq.{1} Nat (@Finset.card.{u_1} α q)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a (@Finset.card.{u_1} α prefix₁))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b (@Finset.card.{u_1} α prefix₂)))),
  @Eq.{1} Int
    (@ThreeSum.Subset.mobius.{u_1} α
      (fun (t : Finset.{u_1} α) =>
        @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@ThreeSum.Subset.partialZeta.{u_1} α inst suffix f
            (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) prefix₁ t))
          (@ThreeSum.Subset.partialZeta.{u_1} α inst suffix g
            (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) prefix₂ t)))
      q)
    (∑ x ∈ @Finset.powerset.{u_1} α q,
      @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (f (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) prefix₁ x))
        (g
          (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) prefix₂
            (@SDiff.sdiff.{u_1} (Finset.{u_1} α) (@Finset.instSDiff.{u_1} α inst) q x)))) := by
  sorry

