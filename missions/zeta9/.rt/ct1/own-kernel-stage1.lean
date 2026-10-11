import Solutions.Sol_ZetaNine_CoefficientMapConnection_connectionLinearMap_bijective
import Lean
set_option autoImplicit false
noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection
namespace IndependentConnectionExpected
theorem expected_connectionLinearMap_bijective (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (connectionLinearMap n) := ZetaNine.CoefficientMapConnection.checked_connectionLinearMap_bijective n hn

end IndependentConnectionExpected
open Lean Meta
run_meta do
  do
    let a ← getConstInfo `solution
    let e ← getConstInfo `IndependentConnectionExpected.expected_connectionLinearMap_bijective
    let equal ← isDefEq a.type e.type
    unless equal do throwError "Complete original source type differs"
    let ax ← collectAxioms `IndependentConnectionExpected.expected_connectionLinearMap_bijective
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_endpoint_kernel_type"),
      ("source",Json.str "solution"),("expected",Json.str "IndependentConnectionExpected.expected_connectionLinearMap_bijective"),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr e.type)),
      ("axioms",toJson (ax.toList.map Name.toString))]).compress
