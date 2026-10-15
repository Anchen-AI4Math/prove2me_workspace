import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Mathlib.Data.List.Range
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

universe u_1 u_2

theorem ThreeSum.WeightEnumeration.pi_eq_range : ∀ {ι : Type u_1} {K : Type u_2} [inst : DecidableEq.{u_1 + 1} ι] [inst_1 : NatCast.{u_2} K] (p : Nat)
  (l : List.{u_1} ι),
  @Eq.{max (u_1 + 1) (u_2 + 1)}
    (List.{max u_1 u_2} ((i : ι) → @Membership.mem.{u_1, u_1} ι (List.{u_1} ι) (@List.instMembership.{u_1} ι) l i → K))
    (@List.pi.{u_1, u_2} ι inst (fun (x : ι) => K) l fun (x : ι) =>
      @List.map.{0, u_2} Nat K (fun (n : Nat) => @Nat.cast.{u_2} K inst_1 n) (List.range p))
    (@List.map.{0, max u_1 u_2} Nat
      ((i : ι) → @Membership.mem.{u_1, u_1} ι (List.{u_1} ι) (@List.instMembership.{u_1} ι) l i → K)
      (@ThreeSum.WeightEnumeration.decode.{u_1, u_2} ι K inst inst_1 p l)
      (List.range
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
          (@List.length.{u_1} ι l)))) := by
  sorry

