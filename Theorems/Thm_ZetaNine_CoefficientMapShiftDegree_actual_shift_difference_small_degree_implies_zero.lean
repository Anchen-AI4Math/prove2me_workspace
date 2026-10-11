import Definitions.Def_ZetaNine_CoefficientMapShiftDegree

set_option autoImplicit false
open Polynomial
open ZetaNine ZetaNine.CoefficientMapShiftDegree

theorem ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_small_degree_implies_zero (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hdeg : H.natDegree ≤ 7 * n - 3)
    (hsmall : (shiftDifference n H).natDegree ≤ 8) : H = 0:= by sorry
