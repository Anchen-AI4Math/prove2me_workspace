import missions.zeta9.formalization.CoefficientMapParameterSummationTransport
import IndependentExprDagV3
import Lean
noncomputable section
open scoped BigOperators Matrix
open Polynomial
open ZetaNine
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportBounds ZetaNine.CoefficientMapFormalTransportOutputs
open ZetaNine.CoefficientMapParameterSummationTransport

namespace ParameterSummationAuthorDefinitionExpected
def transferMultiplier (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  coordinatePolynomial (polynomialCoordinates W ᵥ* connectionGamma n)
end ParameterSummationAuthorDefinitionExpected
open Lean Meta
set_option maxHeartbeats 0
set_option maxRecDepth 20000
run_meta do
  let actual := `ZetaNine.CoefficientMapParameterSummationTransport.transferMultiplier
  let expected := `ParameterSummationAuthorDefinitionExpected.transferMultiplier
  let .defnInfo a ← getConstInfo actual | throwError "Not a source definition"
  let .defnInfo b ← getConstInfo expected | throwError "Not an expected definition"
  let te ← isDefEq a.type b.type
  let ve ← isDefEq a.value b.value
  unless te && ve do throwError "Complete definition type/value mismatch"
  let aa ← collectAxioms actual
  let ba ← collectAxioms expected
  let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
  unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
    throwError "Nonstandard definition axioms"
  let ad ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
  let bd ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
  IO.println (Json.mkObj [("kind",Json.str "actual_complete_definition_kernel_value"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson te),("value_kernel_equal",toJson ve),
    ("full_source_type_and_value_expression_dag",ad),
    ("full_expected_type_and_value_expression_dag",bd),
    ("source_axioms",toJson (aa.toList.map Name.toString)),
    ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
