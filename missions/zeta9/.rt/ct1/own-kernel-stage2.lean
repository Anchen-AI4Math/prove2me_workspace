import Solutions.Sol_ZetaNine_CoefficientMapConnection_connection_five_systems_unique
import Lean
set_option autoImplicit false
noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection
namespace IndependentConnectionExpected
theorem expected_connection_five_systems_unique (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        (connectionTarget n r.val).comp (connectionU n) := ZetaNine.CoefficientMapConnection.checked_connection_five_systems_unique n hn r

end IndependentConnectionExpected
open Lean Meta
run_meta do
  do
    let a ← getConstInfo `solution
    let e ← getConstInfo `IndependentConnectionExpected.expected_connection_five_systems_unique
    let equal ← isDefEq a.type e.type
    unless equal do throwError "Complete original source type differs"
    let ax ← collectAxioms `IndependentConnectionExpected.expected_connection_five_systems_unique
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_endpoint_kernel_type"),
      ("source",Json.str "solution"),("expected",Json.str "IndependentConnectionExpected.expected_connection_five_systems_unique"),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr e.type)),
      ("axioms",toJson (ax.toList.map Name.toString))]).compress
