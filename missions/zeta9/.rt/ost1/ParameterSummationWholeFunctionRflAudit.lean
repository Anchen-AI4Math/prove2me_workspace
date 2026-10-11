import missions.zeta9.formalization.CoefficientMapParameterSummationTransport
import IndependentExprDagV3
import Lean

noncomputable section
open scoped BigOperators Matrix
open Polynomial
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapParameterSummationTransport

namespace ParameterSummationAuthorWholeFunction

theorem transferMultiplier_whole_rfl :
    transferMultiplier = (fun (n : ℕ) (W : ℚ[X]) =>
      coordinatePolynomial (polynomialCoordinates W ᵥ* connectionGamma n)) := by
  rfl

end ParameterSummationAuthorWholeFunction

open Lean Meta
set_option maxHeartbeats 0
set_option maxRecDepth 20000
run_meta do
  let name := `ParameterSummationAuthorWholeFunction.transferMultiplier_whole_rfl
  let .thmInfo info ← getConstInfo name | throwError "Expected whole-function rfl theorem"
  let aa ← collectAxioms name
  let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
  unless aa.toList.all allowed.contains do throwError "Nonstandard whole-function axioms"
  let dag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip info.type info.value)
  IO.println (Json.mkObj [("kind",Json.str "actual_whole_function_rfl"),
    ("declaration",Json.str name.toString),
    ("full_type_and_proof_expression_dag",dag),
    ("axioms",toJson (aa.toList.map Name.toString))]).compress
