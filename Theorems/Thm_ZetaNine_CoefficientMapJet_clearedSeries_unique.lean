import Definitions.Def_ZetaNine_CoefficientMapJet

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapJet

theorem ZetaNine.CoefficientMapJet.clearedSeries_unique (n j : ℕ) (S : PowerSeries ℚ)
    (hS : S * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j : PowerSeries ℚ)) : S = clearedSeries n j:= by sorry
