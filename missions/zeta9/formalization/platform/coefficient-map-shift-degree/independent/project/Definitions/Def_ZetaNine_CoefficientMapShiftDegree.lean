import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Reverse

set_option autoImplicit false
noncomputable section
namespace ZetaNine.CoefficientMapShiftDegree

open Polynomial

def shiftA (n : ℕ) : ℚ[X] := (X - C ((n : ℚ) + 1)) * (X + C (n : ℚ)) ^ 10

def shiftB (n : ℕ) : ℚ[X] := X ^ 10 * (X + C (2 * (n : ℚ) + 1))

def shiftDifference (n : ℕ) (H : ℚ[X]) : ℚ[X] :=
  shiftA n * H - shiftB n * H.comp (X + C 1)

end ZetaNine.CoefficientMapShiftDegree
