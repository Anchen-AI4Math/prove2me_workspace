import Definitions.Def_ZetaNine_CoefficientMapJet

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapJet

theorem ZetaNine.CoefficientMapJet.coefficient_convolution_explicit (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℚ[X]) :
    weightedLocalCoefficient n j s W =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        (W.comp (C (-(j : ℚ) * (n - j : ℕ)) +
          C ((n : ℚ) - 2 * j) * X + X ^ 2)).coeff (l - s):= by sorry
