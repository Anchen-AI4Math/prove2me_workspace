import Definitions.Def_ZetaNine_CoefficientMapPartialFractions

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapPartialFractions.candidate_local_coefficients (n j s : ℕ) (W : ℚ[X]) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    PowerSeries.coeff (9 - s) (candidateClearedSeries n j W) =
      CoefficientMapJet.weightedLocalCoefficient n j s W:= by sorry
