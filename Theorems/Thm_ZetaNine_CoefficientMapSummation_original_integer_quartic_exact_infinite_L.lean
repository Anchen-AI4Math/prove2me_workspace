import Definitions.Def_ZetaNine_CoefficientMapSummation

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapSummation.original_integer_quartic_exact_infinite_L (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries n (W.map (Int.castRingHom ℚ))) (exactL n (W.map (Int.castRingHom ℚ))):= by sorry
