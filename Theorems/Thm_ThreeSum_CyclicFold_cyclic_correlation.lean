import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba


theorem ThreeSum.CyclicFold.cyclic_correlation : ∀ {p : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) p] (F H : ZMod p → Nat)
  (r : Nat) (hr : @LT.lt.{0} Nat instLTNat r p),
  @Eq.{1} Int
    (ThreeSum.CyclicFold.cyclic p (ThreeSum.CyclicFold.vector p F)
      (ThreeSum.CyclicFold.vector p fun (z : ZMod p) =>
        H
          (@Neg.neg.{0} (ZMod p)
            (@NegZeroClass.toNeg.{0} (ZMod p)
              (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod p)
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod p)
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} (ZMod p)
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} (ZMod p)
                      (@Ring.toAddCommGroup.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))))))))
            z))
      r)
    (@Nat.cast.{0} Int instNatCastInt
      (@ThreeSum.Balancing.correlation.{0} (ZMod p)
        (@Ring.toAddCommGroup.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))) (@ZMod.fintype p inst) F H
        (@Nat.cast.{0} (ZMod p)
          (@AddMonoidWithOne.toNatCast.{0} (ZMod p)
            (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
              (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))
          r))) := by
  sorry

