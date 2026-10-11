import Definitions.Def_ZetaNine_CoefficientMapTelescoper

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapTelescoper ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate

theorem ZetaNine.CoefficientMapTelescoper.actual_polynomial_quotient_degree_bound (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    ∃ H : ℚ[X], telescoperNumerator n W = rootPolynomial n * H ∧ H.natDegree ≤ 7 * n - 3:= by sorry
