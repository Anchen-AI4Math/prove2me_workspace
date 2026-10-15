import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba


theorem ThreeSum.LightKaratsuba.joined_product : ∀ {μ : Nat → Int} {work n half : Nat} {as bs : List.{0} Int}
  (hhalf :
    @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) half)
      n)
  (ha : @Eq.{1} Nat (@List.length.{0} Int as) n) (hb : @Eq.{1} Nat (@List.length.{0} Int bs) n)
  (h0 : ThreeSum.LightKaratsuba.ProductAt μ work half (@List.take.{0} Int half as) (@List.take.{0} Int half bs))
  (h2 :
    ThreeSum.LightKaratsuba.ProductAt μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work n) half
      (@List.drop.{0} Int half as) (@List.drop.{0} Int half bs))
  (hm :
    ThreeSum.LightKaratsuba.ProductAt μ
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      half (ThreeSum.Karatsuba.plus (@List.take.{0} Int half as) (@List.drop.{0} Int half as))
      (ThreeSum.Karatsuba.plus (@List.take.{0} Int half bs) (@List.drop.{0} Int half bs)))
  (j : Nat),
  @Eq.{1} Int (ThreeSum.LightKaratsuba.joined μ work n half j)
    (@Polynomial.coeff.{0} Int Int.instSemiring
      (@HMul.hMul.{0, 0, 0} (@Polynomial.{0} Int Int.instSemiring) (@Polynomial.{0} Int Int.instSemiring)
        (@Polynomial.{0} Int Int.instSemiring)
        (@instHMul.{0} (@Polynomial.{0} Int Int.instSemiring) (@Polynomial.instMul.{0} Int Int.instSemiring))
        (ThreeSum.Karatsuba.asPolynomial as) (ThreeSum.Karatsuba.asPolynomial bs))
      j) := by
  sorry

