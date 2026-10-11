import Definitions.Def_ZetaNine_CoefficientMap

set_option autoImplicit false
open Finset Polynomial
open ZetaNine.CoefficientMap

theorem ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even (n j : ℕ) (hn : Even n)
    (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)):= by sorry
