import Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs
set_option autoImplicit false
open scoped BigOperators Matrix
open Finset Polynomial
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapFormalTransportData

theorem ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r) := by sorry
