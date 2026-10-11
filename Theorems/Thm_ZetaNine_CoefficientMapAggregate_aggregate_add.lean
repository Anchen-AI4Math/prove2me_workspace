import Definitions.Def_ZetaNine_CoefficientMapAggregate

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapAggregate.aggregate_add (n : ℕ) (W V : ℚ[X]) :
    aggregate n (W + V) = aggregate n W + aggregate n V:= by sorry
