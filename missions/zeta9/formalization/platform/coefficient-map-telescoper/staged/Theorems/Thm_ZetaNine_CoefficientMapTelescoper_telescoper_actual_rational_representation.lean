import Definitions.Def_ZetaNine_CoefficientMapTelescoper

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapTelescoper ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate

theorem ZetaNine.CoefficientMapTelescoper.telescoper_actual_rational_representation (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) (t : ℚ)
    (hregular : ∀ k < n, t + (k : ℚ) ≠ 0) :
    telescoper n W t = (telescoperNumerator n W).eval t / (polePolynomial (n - 1)).eval t ^ 9:= by sorry
