import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_IndexedGreedy_argmax_range


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum

universe u_1 u_2

theorem ThreeSum.LightLocalCoverTransport.choices_map : ∀ {Ω : Type u_1} {U : Type u_2} [inst : Inhabited.{u_1 + 1} Ω] [inst_1 : DecidableEq.{u_2 + 1} U]
  (matrix : Nat → Nat → Nat) (candidate : Nat → Ω) (target : Nat → U) (covers : Ω → U → Prop)
  [inst_2 : @DecidableRel.{u_1 + 1, u_2 + 1} Ω U covers] {rows cols : Nat}
  (hrows : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) rows)
  (hinj :
    @Set.InjOn.{0, u_2} Nat U target
      (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) (Finset.range cols)))
  (hcover :
    ∀ (i j : Nat),
      @LT.lt.{0} Nat instLTNat j cols →
        Iff (ThreeSum.BooleanGreedy.covers matrix i j) (covers (candidate i) (target j)))
  (rounds : Nat),
  @Eq.{u_1 + 1} (List.{u_1} Ω)
    (@List.map.{0, u_1} Nat Ω candidate (ThreeSum.BooleanGreedy.choices matrix rows cols rounds))
    (@ThreeSum.Cover.greedyChoices.{u_1, u_2} Ω U inst (@List.map.{0, u_1} Nat Ω candidate (List.range rows)) covers
      inst_2 (@Finset.image.{0, u_2} Nat U inst_1 target (Finset.range cols)) rounds) := by
  sorry

