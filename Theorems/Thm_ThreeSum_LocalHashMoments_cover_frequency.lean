import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Cover_trimmed_support_lower
import Theorems.Thm_ThreeSum_HashFamily_badPartners_card_le
import Theorems.Thm_ThreeSum_HashFamily_raw_second_moment_five
import Theorems.Thm_ThreeSum_HashFamily_trimmedPairEvent_bound
import Theorems.Thm_ThreeSum_LayerCounts_edgeSet_card
import Theorems.Thm_ThreeSum_LayerCounts_leftFiber_card
import Theorems.Thm_ThreeSum_LayerCounts_rightFiber_card
import Theorems.Thm_ThreeSum_LayerCounts_unionFiber_card
import Theorems.Thm_ThreeSum_LocalCoverBounds_mean_lower


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph

universe u_1

theorem ThreeSum.LocalHashMoments.cover_frequency : ∀ {K : Type u_1} [inst : Field.{u_1} K] [inst_1 : Fintype.{u_1} K] [inst_2 : DecidableEq.{u_1 + 1} K] {L h : Nat}
  (hsep :
    @LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
      L)
  (hDelta : @LE.le.{0} Nat instLENat (ThreeSum.LocalCoverBounds.degree L h) (@Fintype.card.{u_1} K inst_1))
  (hG : @LE.le.{0} Nat instLENat (ThreeSum.LocalCoverBounds.groupSize h) (@Fintype.card.{u_1} K inst_1))
  (hE :
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LocalCoverBounds.outputCount L h)
        (ThreeSum.LocalCoverBounds.groupSize h))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@Fintype.card.{u_1} K inst_1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (hupper :
    @LE.le.{0} Nat instLENat
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@Fintype.card.{u_1} K inst_1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LocalCoverBounds.outputCount L h)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)))))
  (target : Prod.{u_1, u_1} K K),
  @LE.le.{0} Nat instLENat
    (@Fintype.card.{u_1} (ThreeSum.LocalHashMoments.Weight.{u_1} L K)
      (@Pi.instFintype.{0, u_1} (Prod.{0, 0} (Fin L) Bool) (fun (a : Prod.{0, 0} (Fin L) Bool) => K)
        (fun (a b : Prod.{0, 0} (Fin L) Bool) =>
          @instDecidableEqProd.{0, 0} (Fin L) Bool (instDecidableEqFin L) instDecidableEqBool a b)
        (@instFintypeProd.{0, 0} (Fin L) Bool (Fin.fintype L) Bool.fintype) fun (a : Prod.{0, 0} (Fin L) Bool) =>
        inst_1))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Finset.card.{u_1} (ThreeSum.LocalHashMoments.Weight.{u_1} L K)
        {w : ThreeSum.LocalHashMoments.Weight.{u_1} L K |
          @ThreeSum.LocalHashMoments.Covers.{u_1} K inst inst_1 inst_2 L h
            (ThreeSum.LocalHashMoments.bucketBound L h (@Fintype.card.{u_1} K inst_1)) w target})) := by
  sorry

