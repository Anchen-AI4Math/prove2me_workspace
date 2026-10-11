import Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs
set_option autoImplicit false
open scoped BigOperators Matrix
open Finset Polynomial
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapFormalTransportData

theorem ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport (n : ℕ) (hn : 1 ≤ n) :
    actualFMatrix (n + 2) = connectionGamma n * actualFMatrix n := by sorry
