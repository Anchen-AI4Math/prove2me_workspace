import Definitions.Def_ZetaNine_CoefficientMap

set_option autoImplicit false
open Finset Polynomial
open ZetaNine.CoefficientMap

theorem ZetaNine.CoefficientMap.leadingPoleCoefficient_eq (n j : ℕ) (hj : j ≤ n) :
    leadingPoleCoefficient n j =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ):= by sorry
