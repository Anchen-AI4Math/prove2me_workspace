import missions.zeta9.formalization.CoefficientMapFormalTransportOutputs
import IndependentExprDagV3
import Lean
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine
open ZetaNine.HarmonicStability ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapAggregate
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapConnection
open ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapFormalTransportData
namespace OutputsAuthorDefinitionExpected
def expected_connectionPair (n : ℕ) (r : Fin 5) : ℚ[X] × ℚ[X] :=
  if hn : 1 ≤ n then
    Classical.choose (connection_five_systems_unique n hn r).exists
  else (0, 0)


def expected_connectionP (n : ℕ) (r : Fin 5) : ℚ[X] := (connectionPair n r).1


def expected_connectionQ (n : ℕ) (r : Fin 5) : ℚ[X] := (connectionPair n r).2


def expected_connectionGamma (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun r l => (connectionP n r).coeff l.val

/-- True cancellation numerator for Q(t), with denominator
    ((t-1) polePolynomial_n(t))^9.  The positive roots are 2,...,n+1. -/

def expected_remainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) *
    (∏ i ∈ range n, (X - C ((i : ℚ) + 2))) *
    (∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1))) *
    q.comp (connectionV n)


def expected_shiftedRemainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  (remainderNumerator n q).comp (X + 1)

/-- Genuine formal jet for an arbitrary numerator, not an abstract array. -/

def expected_numeratorClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  ((A.comp (shiftedVariable j) : ℚ[X]) : PowerSeries ℚ) *
    ((shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹


def expected_numeratorLocalCoefficient (m j s : ℕ) (A : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (numeratorClearedSeries m j A)


def expected_remainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  numeratorLocalCoefficient (n + 1) j s (shiftedRemainderNumerator n q)


def expected_extendedOldCoefficient (n j s : ℕ) (P : ℚ[X]) : ℚ :=
  if 1 ≤ j ∧ j ≤ n + 1 then weightedLocalCoefficient n (j - 1) s P else 0


def expected_extendedRemainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  if j ≤ n + 1 then remainderCoefficient n j s q else 0


def expected_previousRemainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  if j = 0 then 0 else extendedRemainderCoefficient n (j - 1) s q

/- Planned universal theorem, NOT YET PROVED OR COMPILED:

weightedLocalCoefficient (n+2) j s (X^r.val) =
  extendedOldCoefficient n j s (connectionP n r) +
  extendedRemainderCoefficient n j s (connectionQ n r) -
  previousRemainderCoefficient n j s (connectionQ n r)

for n>=1, j<=n+2 and 1<=s<=9.  From this derive all nine rho
relations and the rational constant correction, then the actual row matrix
identity F_(n+2) = connectionGamma n * F_n for Even n>=2.
-/


def expected_rho (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n j s W


def expected_constantTerm (n : ℕ) (W : ℚ[X]) : ℚ :=
  -(∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    CoefficientMapJet.weightedLocalCoefficient n j s W * harmonicPower s j)


def expected_aggregate (n : ℕ) (W : ℚ[X]) (i : Fin 5) : ℚ :=
  match i.val with
  | 0 => CoefficientMapFiniteSum.constantTerm n W
  | 1 => CoefficientMapFiniteSum.rho n 3 W
  | 2 => CoefficientMapFiniteSum.rho n 5 W
  | 3 => CoefficientMapFiniteSum.rho n 7 W
  | _ => CoefficientMapFiniteSum.rho n 9 W


def expected_aggregateLinearMap (n : ℕ) : ℚ[X] →ₗ[ℚ] (Fin 5 → ℚ) where
  toFun := aggregate n
  map_add' := aggregate_add n
  map_smul' := aggregate_smul n


def expected_quarticAggregateLinearMap (n : ℕ) : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) :=
  (aggregateLinearMap n).comp coordinateLinearMap


def expected_actualFMatrix (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => aggregate n (X ^ i.val) j


end OutputsAuthorDefinitionExpected
open Lean Meta
set_option maxHeartbeats 0
set_option maxRecDepth 20000
run_meta do
  for (actual,expected) in [(`ZetaNine.CoefficientMapFormalTransportData.connectionPair, `OutputsAuthorDefinitionExpected.expected_connectionPair), (`ZetaNine.CoefficientMapFormalTransportData.connectionP, `OutputsAuthorDefinitionExpected.expected_connectionP), (`ZetaNine.CoefficientMapFormalTransportData.connectionQ, `OutputsAuthorDefinitionExpected.expected_connectionQ), (`ZetaNine.CoefficientMapFormalTransportData.connectionGamma, `OutputsAuthorDefinitionExpected.expected_connectionGamma), (`ZetaNine.CoefficientMapFormalTransportData.remainderNumerator, `OutputsAuthorDefinitionExpected.expected_remainderNumerator), (`ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator, `OutputsAuthorDefinitionExpected.expected_shiftedRemainderNumerator), (`ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries, `OutputsAuthorDefinitionExpected.expected_numeratorClearedSeries), (`ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient, `OutputsAuthorDefinitionExpected.expected_numeratorLocalCoefficient), (`ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient, `OutputsAuthorDefinitionExpected.expected_remainderCoefficient), (`ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient, `OutputsAuthorDefinitionExpected.expected_extendedOldCoefficient), (`ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient, `OutputsAuthorDefinitionExpected.expected_extendedRemainderCoefficient), (`ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient, `OutputsAuthorDefinitionExpected.expected_previousRemainderCoefficient), (`ZetaNine.CoefficientMapFiniteSum.rho, `OutputsAuthorDefinitionExpected.expected_rho), (`ZetaNine.CoefficientMapFiniteSum.constantTerm, `OutputsAuthorDefinitionExpected.expected_constantTerm), (`ZetaNine.CoefficientMapAggregate.aggregate, `OutputsAuthorDefinitionExpected.expected_aggregate), (`ZetaNine.CoefficientMapAggregate.aggregateLinearMap, `OutputsAuthorDefinitionExpected.expected_aggregateLinearMap), (`ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap, `OutputsAuthorDefinitionExpected.expected_quarticAggregateLinearMap), (`ZetaNine.CoefficientMapMatrix.actualFMatrix, `OutputsAuthorDefinitionExpected.expected_actualFMatrix)] do
    let .defnInfo a ← getConstInfo actual | throwError "Actual is not a complete definition"
    let .defnInfo b ← getConstInfo expected | throwError "Expected is not a complete definition"
    let typeSame ← isDefEq a.type b.type
    let valueSame ← isDefEq a.value b.value
    unless typeSame && valueSame do throwError "Whole definition kernel mismatch: {actual}"
    let aa ← collectAxioms actual
    let ba ← collectAxioms expected
    let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
    unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
      throwError "Nonstandard definition axioms"
    let sourceDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    let expectedDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_definition_kernel_value"),
      ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
      ("type_kernel_equal",toJson typeSame),("value_kernel_equal",toJson valueSame),
      ("full_source_type_and_value_expression_dag",sourceDag),
      ("full_expected_type_and_value_expression_dag",expectedDag),
      ("all_fields_Expr_equal_roundtrip",toJson true),
      ("source_axioms",toJson (aa.toList.map Name.toString)),
      ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
