import Definitions.Def_ZetaNine_CoefficientMapInjectivity

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapInjectivity.all_local_coefficients_zero_implies_zero (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (hzero : AllLocalCoefficientsZero n W) : W = 0:= by sorry
