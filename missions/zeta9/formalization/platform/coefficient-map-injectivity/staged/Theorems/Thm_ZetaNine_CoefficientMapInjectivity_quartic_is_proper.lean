import Definitions.Def_ZetaNine_CoefficientMapInjectivity

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapInjectivity.quartic_is_proper (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4) : ProperMultiplier n W:= by sorry
