import Definitions.Def_ZetaNine_CoefficientMapShiftDegree

set_option autoImplicit false
open Polynomial
open ZetaNine ZetaNine.CoefficientMapShiftDegree

theorem ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient (n : ℕ) (H : ℚ[X]) (hH : H ≠ 0) :
    (shiftDifference n H).coeff (H.natDegree + 10) =
      (7 * (n : ℚ) - 2 - (H.natDegree : ℚ)) * H.leadingCoeff:= by sorry
