import Definitions.Def_ZetaNine_CoefficientMapConnection

set_option autoImplicit false
noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection

theorem ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (connectionLinearMap n):= by sorry
