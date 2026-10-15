import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Light
end Light
namespace Polynomial
end Polynomial
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

namespace ThreeSum1960614.Machine

/-!
# Dense integer Karatsuba multiplication

This file implements a dense, low-coefficient-first list algorithm. Its
correctness theorem is an equality of integer polynomials. The instrumented
work model counts list traversal and scalar arithmetic primitives; it is a
separate obligation to compile this implementation to `Light` and prove the
benchmark's word-RAM step and word-size bounds.
-/

namespace ThreeSum.Karatsuba
open _root_.ThreeSum.Karatsuba


open _root_.Polynomial









@[simp] theorem length_plus (as bs : List ℤ) :
    (_root_.ThreeSum.Karatsuba.plus as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [_root_.ThreeSum.Karatsuba.plus]
  | cons a as ih =>
    cases bs with
    | nil => simp [_root_.ThreeSum.Karatsuba.plus]
    | cons b bs => simpa [_root_.ThreeSum.Karatsuba.plus, Nat.succ_max_succ] using congrArg Nat.succ (ih bs)







@[simp] theorem asPolynomial_plus (as bs : List ℤ) :
    _root_.ThreeSum.Karatsuba.asPolynomial (_root_.ThreeSum.Karatsuba.plus as bs) = _root_.ThreeSum.Karatsuba.asPolynomial as + _root_.ThreeSum.Karatsuba.asPolynomial bs := by
  induction as generalizing bs with
  | nil => simp [_root_.ThreeSum.Karatsuba.plus, _root_.ThreeSum.Karatsuba.asPolynomial]
  | cons a as ih =>
    cases bs with
    | nil => simp [_root_.ThreeSum.Karatsuba.plus, _root_.ThreeSum.Karatsuba.asPolynomial]
    | cons b bs =>
      simp only [_root_.ThreeSum.Karatsuba.plus, _root_.ThreeSum.Karatsuba.asPolynomial, ih, map_add]
      ring







/-- Splitting at a coefficient boundary is exact, also for padded short lists. -/
theorem asPolynomial_split (n : ℕ) (as : List ℤ) :
    _root_.ThreeSum.Karatsuba.asPolynomial as = _root_.ThreeSum.Karatsuba.asPolynomial (as.take n) + X ^ n * _root_.ThreeSum.Karatsuba.asPolynomial (as.drop n) := by
  induction n generalizing as with
  | zero => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
  | succ n ih =>
    cases as with
    | nil => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
    | cons a as =>
      simp only [List.take_succ_cons, List.drop_succ_cons, _root_.ThreeSum.Karatsuba.asPolynomial, pow_succ]
      rw [ih as]
      ring











/-! ## Explicit traversal/arithmetic work model

The following charges reflect the operations in the executable list code:
two units per matched coefficient of `plus`; two per mapped coefficient of
`negate`; two per generated/concatenated zero of `shift`; and the two scans
used by `take` and `drop`. The fixed per-call charges include list tests.
They are a conventional unit-cost list/arithmetic model, **not** a theorem
about the benchmark machine or Lean's runtime system.

The recursive charge below uses the actual intermediate list sizes. The
uniform three-subcall recurrence is proved from those sizes; it is not an
assumption that the desired multiplication bound already holds.
-/





















end ThreeSum.Karatsuba

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Coefficient and intermediate-value bounds for the array realization -/

namespace ThreeSum.Karatsuba
open _root_.ThreeSum.Karatsuba


open _root_.Polynomial
open scoped _root_.BigOperators

@[simp] theorem asPolynomial_coeff (as : List ℤ) (j : ℕ) :
    (_root_.ThreeSum.Karatsuba.asPolynomial as).coeff j = as.getD j 0 := by
  induction as generalizing j with
  | nil => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
  | cons a as ih =>
    cases j with
    | zero => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
    | succ j =>
      rw [_root_.ThreeSum.Karatsuba.asPolynomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul, ih]
      simp





















theorem product_coeff_zero {as bs : List ℤ} {n j : ℕ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n) (hj : 2 * n ≤ j) :
    (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff j = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  by_cases hpa : n ≤ p.1
  · rw [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff, List.getD_eq_default _ _ (ha.trans hpa), zero_mul]
  · have hpb : n ≤ p.2 := by omega
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff bs, List.getD_eq_default _ _ (hb.trans hpb), mul_zero]





end ThreeSum.Karatsuba

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba
open _root_.ThreeSum.LightKaratsuba


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.Polynomial











































section Join

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d pLinear pFill : ℕ}



end Join

section BaseCase

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end BaseCase

@[simp] theorem window_sub (f g : ℕ → ℤ) (offset n j : ℕ) :
    _root_.ThreeSum.LightKaratsuba.window (fun i => f i - g i) offset n j =
      _root_.ThreeSum.LightKaratsuba.window f offset n j - _root_.ThreeSum.LightKaratsuba.window g offset n j := by
  unfold _root_.ThreeSum.LightKaratsuba.window
  split_ifs <;> simp

theorem ProductAt.window {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (offset j : ℕ) :
    _root_.ThreeSum.LightKaratsuba.window (fun i => μ (out + i)) offset (2 * n) j =
      (X ^ offset * (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs)).coeff j := by
  rw [Polynomial.coeff_X_pow_mul']
  unfold _root_.ThreeSum.LightKaratsuba.window
  by_cases ho : offset ≤ j
  · rw [if_pos ho]
    by_cases hj : j < offset + 2 * n
    · rw [if_pos ⟨ho, hj⟩]
      exact hp _ (by omega)
    · rw [if_neg (by omega : ¬ (offset ≤ j ∧ j < offset + 2 * n))]
      exact (_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_zero ha hb (by omega : 2 * n ≤ j - offset)).symm
  · rw [if_neg ho, if_neg (by omega : ¬ (offset ≤ j ∧ j < offset + 2 * n))]

















section RecursiveExecution

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}



end RecursiveExecution

section CompleteProcedure

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}









end CompleteProcedure

end ThreeSum.LightKaratsuba

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.Polynomial
section

/-- The coefficient identity matched by the six actual joining passes. -/
theorem ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.joined_product__implementation_691e66f66b {μ : ℕ → ℤ} {work n half : ℕ} {as bs : List ℤ}
    (hhalf : 2 * half = n) (ha : as.length = n) (hb : bs.length = n)
    (h0 : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ work half (as.take half) (bs.take half))
    (h2 : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ (work + n) half (as.drop half) (bs.drop half))
    (hm : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ (work + 2 * n) half
      (_root_.ThreeSum.Karatsuba.plus (as.take half) (as.drop half)) (_root_.ThreeSum.Karatsuba.plus (bs.take half) (bs.drop half)))
    (j : ℕ) : _root_.ThreeSum.LightKaratsuba.joined μ work n half j = (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff j := by
  have ha0 : (as.take half).length ≤ half := by simp
  have hb0 : (bs.take half).length ≤ half := by simp
  have ha1 : (as.drop half).length ≤ half := by simp only [List.length_drop, ha]; omega
  have hb1 : (bs.drop half).length ≤ half := by simp only [List.length_drop, hb]; omega
  have has : (_root_.ThreeSum.Karatsuba.plus (as.take half) (as.drop half)).length ≤ half := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.length_plus] using max_le ha0 ha1
  have hbs : (_root_.ThreeSum.Karatsuba.plus (bs.take half) (bs.drop half)).length ≤ half := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.length_plus] using max_le hb0 hb1
  have hw0 := h0.window ha0 hb0 0 j
  have hw0m := h0.window ha0 hb0 half j
  have hw2m := h2.window ha1 hb1 half j
  have hw2 := h2.window ha1 hb1 n j
  have hwm := hm.window has hbs half j
  rw [hhalf] at hw0 hw0m hw2m hw2 hwm
  unfold _root_.ThreeSum.LightKaratsuba.joined
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.window_sub, _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.window_sub, hw0, hwm, hw0m, hw2m, hw2]
  simp only [pow_zero, one_mul]
  have hp :
      _root_.ThreeSum.Karatsuba.asPolynomial (as.take half) * _root_.ThreeSum.Karatsuba.asPolynomial (bs.take half) +
        (X ^ half * (_root_.ThreeSum.Karatsuba.asPolynomial (_root_.ThreeSum.Karatsuba.plus (as.take half) (as.drop half)) *
          _root_.ThreeSum.Karatsuba.asPolynomial (_root_.ThreeSum.Karatsuba.plus (bs.take half) (bs.drop half))) -
         X ^ half * (_root_.ThreeSum.Karatsuba.asPolynomial (as.take half) * _root_.ThreeSum.Karatsuba.asPolynomial (bs.take half)) -
         X ^ half * (_root_.ThreeSum.Karatsuba.asPolynomial (as.drop half) * _root_.ThreeSum.Karatsuba.asPolynomial (bs.drop half))) +
        X ^ n * (_root_.ThreeSum.Karatsuba.asPolynomial (as.drop half) * _root_.ThreeSum.Karatsuba.asPolynomial (bs.drop half)) =
      _root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_plus, _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_plus]
    conv_rhs => rw [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_split half as, _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_split half bs]
    rw [← hhalf, two_mul, pow_add]
    ring
  simpa only [Polynomial.coeff_add, Polynomial.coeff_sub] using
    congrArg (fun p : Polynomial ℤ => p.coeff j) hp
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.joined_product__implementation_691e66f66b) := (@ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.joined_product__implementation_691e66f66b)

#print axioms solution
