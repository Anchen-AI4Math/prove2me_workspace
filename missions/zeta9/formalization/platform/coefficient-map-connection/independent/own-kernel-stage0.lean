import Solutions.Sol_ZetaNine_CoefficientMapConnection_connection_homogeneous_kernel_zero
import Lean
set_option autoImplicit false
noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection
namespace IndependentConnectionExpected
theorem expected_connection_homogeneous_kernel_zero (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X])
    (hqdeg : q.natDegree ≤ 9)
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q = 0) :
    P = 0 ∧ q = 0 := ZetaNine.CoefficientMapConnection.checked_connection_homogeneous_kernel_zero n hn P q hqdeg heq

end IndependentConnectionExpected
open Lean Meta
run_meta do
  do
    let a ← getConstInfo `solution
    let e ← getConstInfo `IndependentConnectionExpected.expected_connection_homogeneous_kernel_zero
    let equal ← isDefEq a.type e.type
    unless equal do throwError "Complete original source type differs"
    let ax ← collectAxioms `IndependentConnectionExpected.expected_connection_homogeneous_kernel_zero
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_endpoint_kernel_type"),
      ("source",Json.str "solution"),("expected",Json.str "IndependentConnectionExpected.expected_connection_homogeneous_kernel_zero"),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr e.type)),
      ("axioms",toJson (ax.toList.map Name.toString))]).compress
