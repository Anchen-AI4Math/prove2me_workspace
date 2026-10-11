import missions.zeta9.formalization.CoefficientMapConnection
import Lean
set_option autoImplicit false
noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection
namespace IndependentConnectionExpected
theorem expected_connection_homogeneous_kernel_zero (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X])
    (hqdeg : q.natDegree ≤ 9)
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q = 0) :
    P = 0 ∧ q = 0 := ZetaNine.CoefficientMapConnection.connection_homogeneous_kernel_zero n hn P q hqdeg heq

theorem expected_connectionLinearMap_bijective (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (connectionLinearMap n) := ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective n hn

theorem expected_connection_five_systems_unique (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        (connectionTarget n r.val).comp (connectionU n) := ZetaNine.CoefficientMapConnection.connection_five_systems_unique n hn r

end IndependentConnectionExpected
open Lean Meta
run_meta do
  do
    let a ← getConstInfo `ZetaNine.CoefficientMapConnection.connection_homogeneous_kernel_zero
    let e ← getConstInfo `IndependentConnectionExpected.expected_connection_homogeneous_kernel_zero
    let equal ← isDefEq a.type e.type
    unless equal do throwError "Complete original source type differs"
    let ax ← collectAxioms `IndependentConnectionExpected.expected_connection_homogeneous_kernel_zero
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_endpoint_kernel_type"),
      ("source",Json.str "ZetaNine.CoefficientMapConnection.connection_homogeneous_kernel_zero"),("expected",Json.str "IndependentConnectionExpected.expected_connection_homogeneous_kernel_zero"),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr e.type)),
      ("axioms",toJson (ax.toList.map Name.toString))]).compress
  do
    let a ← getConstInfo `ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective
    let e ← getConstInfo `IndependentConnectionExpected.expected_connectionLinearMap_bijective
    let equal ← isDefEq a.type e.type
    unless equal do throwError "Complete original source type differs"
    let ax ← collectAxioms `IndependentConnectionExpected.expected_connectionLinearMap_bijective
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_endpoint_kernel_type"),
      ("source",Json.str "ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective"),("expected",Json.str "IndependentConnectionExpected.expected_connectionLinearMap_bijective"),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr e.type)),
      ("axioms",toJson (ax.toList.map Name.toString))]).compress
  do
    let a ← getConstInfo `ZetaNine.CoefficientMapConnection.connection_five_systems_unique
    let e ← getConstInfo `IndependentConnectionExpected.expected_connection_five_systems_unique
    let equal ← isDefEq a.type e.type
    unless equal do throwError "Complete original source type differs"
    let ax ← collectAxioms `IndependentConnectionExpected.expected_connection_five_systems_unique
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_endpoint_kernel_type"),
      ("source",Json.str "ZetaNine.CoefficientMapConnection.connection_five_systems_unique"),("expected",Json.str "IndependentConnectionExpected.expected_connection_five_systems_unique"),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr e.type)),
      ("axioms",toJson (ax.toList.map Name.toString))]).compress
