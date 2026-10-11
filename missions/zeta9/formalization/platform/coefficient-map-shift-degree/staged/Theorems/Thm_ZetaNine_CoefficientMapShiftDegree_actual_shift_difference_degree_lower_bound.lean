import Definitions.Def_ZetaNine_CoefficientMapShiftDegree

set_option autoImplicit false
open Polynomial
open ZetaNine ZetaNine.CoefficientMapShiftDegree

theorem ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_degree_lower_bound (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hH : H ≠ 0) (hdeg : H.natDegree ≤ 7 * n - 3) :
    H.natDegree + 10 ≤ (shiftDifference n H).natDegree:= by sorry
