import Definitions.Def_ZetaNine_CoefficientMapInjectivity

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap_injective (n : ℕ) :
    Function.Injective (fun W : {W : ℚ[X] // ProperMultiplier n W} => fullLocalCoefficientMap n W.val):= by sorry
