import GAIExprDag
import Definitions.Def_ZetaNine_CoefficientMap
import Definitions.Def_ZetaNine_AnalyticPhase
import Definitions.Def_ZetaNine_AnalyticUniformWeighted
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open Lean Meta Elab Command
open ZetaNine.AnalyticMomentBounds
open ZetaNine.AnalyticPhase
open ZetaNine.AnalyticUniformMomentBound
open ZetaNine.AnalyticWeightedBound
open ZetaNine.CoefficientMap

private def afEmit (j : Json) : MetaM Unit := do
  let action : IO Unit := do
    let stdout ← IO.getStdout
    stdout.putStrLn ("GAI_RECORD|" ++ j.compress)
    stdout.flush
  liftM action

private def afAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def afRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let some value := ci.value? true | throwError "Missing complete proof/definition value: {n}"
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type value)
  let (rt,rv) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  let exactType := Expr.equal ci.type rt
  let exactValue := Expr.equal value rv
  unless exactType && exactValue do throwError "Full-field Expr DAG changed an expression: {n}"
  let typeKernel ← isDefEq ci.type rt
  let valueKernel ← isDefEq value rv
  let typed ← isDefEq (← inferType rv) ci.type
  unless typeKernel && valueKernel && typed do
    throwError "Complete reconstructed proof/value does not have its exact complete type: {n}"
  afEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",toJson payload.compress),
    ("value_raw_format",toJson "lossless lean-expr-dag-v1; full type_root and value_root"),
    ("all_fields_type_Expr_equal",toJson exactType),("all_fields_value_Expr_equal",toJson exactValue),
    ("full_type_kernel_equal",toJson typeKernel),("full_value_kernel_equal",toJson valueKernel),
    ("value_type_isDefEq",toJson typed),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← afAxioms n)]

namespace GAIOriginalDefs
def numerator (n : ℕ) (t : ℚ) : ℚ  := 
  (n.factorial : ℚ) ^ 7 *
    (∏ i ∈ range n, (t - ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (t + n + ((i : ℚ) + 1)))

def poleProduct (n : ℕ) (t : ℚ) : ℚ  := 
  ∏ k ∈ range (n + 1), (t + k)

def actualR (n : ℕ) (t : ℚ) : ℚ  :=  ZetaNine.CoefficientMap.numerator n t / ZetaNine.CoefficientMap.poleProduct n t ^ 9

def clearedPoleProduct (n j : ℕ) (t : ℚ) : ℚ  := 
  ∏ k ∈ (range (n + 1)).erase j, (t + k)

def clearedR (n j : ℕ) (t : ℚ) : ℚ  := 
  ZetaNine.CoefficientMap.numerator n t / ZetaNine.CoefficientMap.clearedPoleProduct n j t ^ 9

def leadingPoleCoefficient (n j : ℕ) : ℚ  :=  ZetaNine.CoefficientMap.clearedR n j (-(j : ℚ))

def weightedR (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ  := 
  ZetaNine.CoefficientMap.actualR n t * W.eval (t * (t + n))

def clearedWeightedR (n j : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ  := 
  ZetaNine.CoefficientMap.clearedR n j t * W.eval (t * (t + n))

def weightedLeadingPoleCoefficient (n j : ℕ) (W : ℚ[X]) : ℚ  := 
  ZetaNine.CoefficientMap.clearedWeightedR n j W (-(j : ℚ))

def phase (x : ℝ) : ℝ  := 
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    (x - 1) * Real.log (x - 1) - 10 * (x + 1) * Real.log (x + 1)

def phaseRatio (x : ℝ) : ℝ  :=  (x + 2) * x ^ 10 / ((x - 1) * (x + 1) ^ 10)

def phaseSlope (x : ℝ) : ℝ  := 
  10 * Real.log x + Real.log (x + 2) - Real.log (x - 1) - 10 * Real.log (x + 1)

def upperSlopeConstant : ℝ  :=  (301 / 100 : ℝ) * (101 / 201 : ℝ) ^ 10

def smoothPhaseGap (x : ℝ) : ℝ  := 
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    10 * (x + 1) * Real.log (x + 1) - ZetaNine.AnalyticPhase.phase 1 -
      (x - 1) * (1 + Real.log ZetaNine.AnalyticPhase.upperSlopeConstant)

def smoothPhaseSlope (x : ℝ) : ℝ  := 
  10 * Real.log x + Real.log (x + 2) - 10 * Real.log (x + 1) -
    Real.log ZetaNine.AnalyticPhase.upperSlopeConstant

def smoothPhaseRatio (x : ℝ) : ℝ  := 
  (x + 2) * (x / (x + 1)) ^ 10

def actualMomentTerm (n r k : ℕ) : ℝ  := 
  (CoefficientMap.actualR n (k : ℚ) : ℝ) *
    ((k : ℝ) * ((k : ℝ) + (n : ℝ))) ^ r

def actualMomentSequence (n r m : ℕ) : ℝ  :=  ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 1)

def actualMoment (n r : ℕ) : ℝ  :=  ∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m

def tailPower (n r : ℕ) : ℕ  :=  7 * n + 9 - 2 * r

def tailCoefficient (n r : ℕ) : ℝ  := 
  (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n * (3 / 2 : ℝ) ^ r

def tailWeightConstant (r : ℕ) : ℝ  := 
  (9 / 7 : ℝ) * (3 / 2 : ℝ) ^ r / (2 : ℝ) ^ (9 - 2 * r)

def tailMajorant (n r : ℕ) : ℝ  := 
  ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (2 * (n : ℝ)) ^ ZetaNine.AnalyticMomentBounds.tailPower n r * (9 / 7 : ℝ) /
    (n : ℝ) ^ (2 * r)

def tailExponent : ℝ  :=  7 + 6 * Real.log 2

def momentBoundConstant : ℝ  :=  5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7

def actualWeightedSequence (n : ℕ) (W : ℚ[X]) (m : ℕ) : ℝ  := 
  (CoefficientMap.weightedR n W ((m + 1 : ℕ) : ℚ) : ℝ)

def weightedCoefficientHeight (n : ℕ) (W : ℚ[X]) : ℝ  := 
  ∑ r ∈ range 5, |(W.coeff r : ℝ)| * (n : ℝ) ^ (2 * r)

def analyticPrefactor (n : ℕ) : ℝ  := 
  ZetaNine.AnalyticUniformMomentBound.momentBoundConstant * ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n)

def uniformError (n : ℕ) : ℝ  := 
  (Real.log ZetaNine.AnalyticUniformMomentBound.momentBoundConstant + 10 * Real.log ((n : ℝ) + 1)) / (n : ℝ)
end GAIOriginalDefs

theorem original_value_numerator : GAIOriginalDefs.numerator = ZetaNine.CoefficientMap.numerator := rfl
theorem original_value_poleProduct : GAIOriginalDefs.poleProduct = ZetaNine.CoefficientMap.poleProduct := rfl
theorem original_value_actualR : GAIOriginalDefs.actualR = ZetaNine.CoefficientMap.actualR := rfl
theorem original_value_clearedPoleProduct : GAIOriginalDefs.clearedPoleProduct = ZetaNine.CoefficientMap.clearedPoleProduct := rfl
theorem original_value_clearedR : GAIOriginalDefs.clearedR = ZetaNine.CoefficientMap.clearedR := rfl
theorem original_value_leadingPoleCoefficient : GAIOriginalDefs.leadingPoleCoefficient = ZetaNine.CoefficientMap.leadingPoleCoefficient := rfl
theorem original_value_weightedR : GAIOriginalDefs.weightedR = ZetaNine.CoefficientMap.weightedR := rfl
theorem original_value_clearedWeightedR : GAIOriginalDefs.clearedWeightedR = ZetaNine.CoefficientMap.clearedWeightedR := rfl
theorem original_value_weightedLeadingPoleCoefficient : GAIOriginalDefs.weightedLeadingPoleCoefficient = ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient := rfl
theorem original_value_phase : GAIOriginalDefs.phase = ZetaNine.AnalyticPhase.phase := rfl
theorem original_value_phaseRatio : GAIOriginalDefs.phaseRatio = ZetaNine.AnalyticPhase.phaseRatio := rfl
theorem original_value_phaseSlope : GAIOriginalDefs.phaseSlope = ZetaNine.AnalyticPhase.phaseSlope := rfl
theorem original_value_upperSlopeConstant : GAIOriginalDefs.upperSlopeConstant = ZetaNine.AnalyticPhase.upperSlopeConstant := rfl
theorem original_value_smoothPhaseGap : GAIOriginalDefs.smoothPhaseGap = ZetaNine.AnalyticPhase.smoothPhaseGap := rfl
theorem original_value_smoothPhaseSlope : GAIOriginalDefs.smoothPhaseSlope = ZetaNine.AnalyticPhase.smoothPhaseSlope := rfl
theorem original_value_smoothPhaseRatio : GAIOriginalDefs.smoothPhaseRatio = ZetaNine.AnalyticPhase.smoothPhaseRatio := rfl
theorem original_value_actualMomentTerm : GAIOriginalDefs.actualMomentTerm = ZetaNine.AnalyticMomentBounds.actualMomentTerm := rfl
theorem original_value_actualMomentSequence : GAIOriginalDefs.actualMomentSequence = ZetaNine.AnalyticMomentBounds.actualMomentSequence := rfl
theorem original_value_actualMoment : GAIOriginalDefs.actualMoment = ZetaNine.AnalyticMomentBounds.actualMoment := rfl
theorem original_value_tailPower : GAIOriginalDefs.tailPower = ZetaNine.AnalyticMomentBounds.tailPower := rfl
theorem original_value_tailCoefficient : GAIOriginalDefs.tailCoefficient = ZetaNine.AnalyticMomentBounds.tailCoefficient := rfl
theorem original_value_tailWeightConstant : GAIOriginalDefs.tailWeightConstant = ZetaNine.AnalyticUniformMomentBound.tailWeightConstant := rfl
theorem original_value_tailMajorant : GAIOriginalDefs.tailMajorant = ZetaNine.AnalyticUniformMomentBound.tailMajorant := rfl
theorem original_value_tailExponent : GAIOriginalDefs.tailExponent = ZetaNine.AnalyticUniformMomentBound.tailExponent := rfl
theorem original_value_momentBoundConstant : GAIOriginalDefs.momentBoundConstant = ZetaNine.AnalyticUniformMomentBound.momentBoundConstant := rfl
theorem original_value_actualWeightedSequence : GAIOriginalDefs.actualWeightedSequence = ZetaNine.AnalyticWeightedBound.actualWeightedSequence := rfl
theorem original_value_weightedCoefficientHeight : GAIOriginalDefs.weightedCoefficientHeight = ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight := rfl
theorem original_value_analyticPrefactor : GAIOriginalDefs.analyticPrefactor = ZetaNine.AnalyticWeightedBound.analyticPrefactor := rfl
theorem original_value_uniformError : GAIOriginalDefs.uniformError = ZetaNine.AnalyticWeightedBound.uniformError := rfl



private def afProofHelpers (actual expected : Name) (av bv : Expr) : MetaM (Expr × Expr) := do
  let mut aa := av
  let mut bb := bv
  for _ in [:16] do
    let mut amap : Array (Name × Expr) := #[]
    let mut bmap : Array (Name × Expr) := #[]
    for n in aa.getUsedConstants do
      if #[`ZetaNine.CoefficientMap.numerator, `ZetaNine.CoefficientMap.poleProduct, `ZetaNine.CoefficientMap.actualR, `ZetaNine.CoefficientMap.clearedPoleProduct, `ZetaNine.CoefficientMap.clearedR, `ZetaNine.CoefficientMap.leadingPoleCoefficient, `ZetaNine.CoefficientMap.weightedR, `ZetaNine.CoefficientMap.clearedWeightedR, `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient, `ZetaNine.AnalyticPhase.phase, `ZetaNine.AnalyticPhase.phaseRatio, `ZetaNine.AnalyticPhase.phaseSlope, `ZetaNine.AnalyticPhase.upperSlopeConstant, `ZetaNine.AnalyticPhase.smoothPhaseGap, `ZetaNine.AnalyticPhase.smoothPhaseSlope, `ZetaNine.AnalyticPhase.smoothPhaseRatio, `ZetaNine.AnalyticMomentBounds.actualMomentTerm, `ZetaNine.AnalyticMomentBounds.actualMomentSequence, `ZetaNine.AnalyticMomentBounds.actualMoment, `ZetaNine.AnalyticMomentBounds.tailPower, `ZetaNine.AnalyticMomentBounds.tailCoefficient, `ZetaNine.AnalyticUniformMomentBound.tailWeightConstant, `ZetaNine.AnalyticUniformMomentBound.tailMajorant, `ZetaNine.AnalyticUniformMomentBound.tailExponent, `ZetaNine.AnalyticUniformMomentBound.momentBoundConstant, `ZetaNine.AnalyticWeightedBound.actualWeightedSequence, `ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight, `ZetaNine.AnalyticWeightedBound.analyticPrefactor, `ZetaNine.AnalyticWeightedBound.uniformError].contains n.getPrefix && n.getString!.startsWith "_proof_" then
        let a ← getConstInfo n
        let some va0 := a.value? true | throwError "Missing actual helper proof {n}"
        let mut matched : Option Name := none
        for m in bb.getUsedConstants do
          if #[`GAIOriginalDefs.numerator, `GAIOriginalDefs.poleProduct, `GAIOriginalDefs.actualR, `GAIOriginalDefs.clearedPoleProduct, `GAIOriginalDefs.clearedR, `GAIOriginalDefs.leadingPoleCoefficient, `GAIOriginalDefs.weightedR, `GAIOriginalDefs.clearedWeightedR, `GAIOriginalDefs.weightedLeadingPoleCoefficient, `GAIOriginalDefs.phase, `GAIOriginalDefs.phaseRatio, `GAIOriginalDefs.phaseSlope, `GAIOriginalDefs.upperSlopeConstant, `GAIOriginalDefs.smoothPhaseGap, `GAIOriginalDefs.smoothPhaseSlope, `GAIOriginalDefs.smoothPhaseRatio, `GAIOriginalDefs.actualMomentTerm, `GAIOriginalDefs.actualMomentSequence, `GAIOriginalDefs.actualMoment, `GAIOriginalDefs.tailPower, `GAIOriginalDefs.tailCoefficient, `GAIOriginalDefs.tailWeightConstant, `GAIOriginalDefs.tailMajorant, `GAIOriginalDefs.tailExponent, `GAIOriginalDefs.momentBoundConstant, `GAIOriginalDefs.actualWeightedSequence, `GAIOriginalDefs.weightedCoefficientHeight, `GAIOriginalDefs.analyticPrefactor, `GAIOriginalDefs.uniformError].contains m.getPrefix && m.getString!.startsWith "_proof_" then
            let c ← getConstInfo m
            if let some vc := c.value? true then
              if Expr.equal a.type c.type && Expr.equal va0 vc then matched := some m
        let some paired := matched | throwError "No full-expression identical expected helper for {n}"
        let b ← getConstInfo paired
        unless (← isProp a.type) && (← isProp b.type) do
          throwError "Only proposition-valued compiler proof helpers can be expanded {n}"
        unless a.levelParams.isEmpty && b.levelParams.isEmpty do
          throwError "Unexpected helper universes {n}"
        let some va := a.value? true | throwError "Missing full helper proof value {n}"
        let some vb := b.value? true | throwError "Missing full helper proof value {paired}"
        let typeDefEq ← isDefEq a.type b.type
        let valueDefEq ← isDefEq va vb
        let actualValueTyped ← isDefEq (← inferType va) a.type
        let expectedValueTyped ← isDefEq (← inferType vb) b.type
        unless typeDefEq && valueDefEq && actualValueTyped && expectedValueTyped do
          throwError "Helper kernel mismatch {n} {paired}"
        afEmit <| Json.mkObj [("kind",toJson "definition_helper_compare"),
          ("actual",toJson n.toString),("expected",toJson paired.toString),
          ("type_actual_raw",toJson (reprStr a.type)),("type_expected_raw",toJson (reprStr b.type)),
          ("value_actual_raw",← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type va)),("value_expected_raw",← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type vb)),
          ("type_exprEqual",toJson (Expr.equal a.type b.type)),("value_exprEqual",toJson (Expr.equal va vb)),
          ("type_isDefEq",toJson typeDefEq),("value_isDefEq",toJson valueDefEq),
          ("actual_value_typed",toJson actualValueTyped),("expected_value_typed",toJson expectedValueTyped),
          ("actual_axioms",← afAxioms n),("expected_axioms",← afAxioms paired)]
        amap := amap.push (n,va)
        bmap := bmap.push (paired,vb)
    if amap.isEmpty then return (aa,bb)
    aa := aa.replace fun e => match e with
      | .const n [] => (amap.find? fun x => x.1 == n).map Prod.snd
      | _ => none
    bb := bb.replace fun e => match e with
      | .const n [] => (bmap.find? fun x => x.1 == n).map Prod.snd
      | _ => none
  throwError "Helper expansion did not terminate within the fixed bound"

private def afCompare (kind : String) (actual expected : Name) (requireValue : Bool) : MetaM Unit := do
  let a ← getConstInfo actual
  let b ← getConstInfo expected
  let typeEqual := Expr.equal a.type b.type
  let typeDefEq ← isDefEq a.type b.type
  unless typeDefEq do throwError "Type mismatch {actual} {expected}"
  let mut valueEqual := false
  let mut valueDefEq := false
  let mut normalizedEqual := false
  let mut normalizedDefEq := false
  let mut va := Json.null
  let mut vb := Json.null
  let mut normalizedA := Json.null
  let mut normalizedB := Json.null
  if requireValue then
    let some av := a.value? | throwError "No actual definition value {actual}"
    let some bv := b.value? | throwError "No original definition value {expected}"
    valueEqual := Expr.equal av bv
    valueDefEq ← isDefEq av bv
    va := toJson (reprStr av)
    vb := toJson (reprStr bv)
    let (na,nb) ← afProofHelpers actual expected av bv
    normalizedEqual := Expr.equal na nb
    normalizedDefEq ← isDefEq na nb
    normalizedA := toJson (reprStr na)
    normalizedB := toJson (reprStr nb)
  afEmit <| Json.mkObj [("kind",toJson kind),("actual",toJson actual.toString),
    ("expected",toJson expected.toString),("type_actual_raw",toJson (reprStr a.type)),
    ("type_expected_raw",toJson (reprStr b.type)),("type_exprEqual",toJson typeEqual),
    ("type_isDefEq",toJson typeDefEq),("value_actual_raw",va),("value_expected_raw",vb),
    ("value_exprEqual",toJson valueEqual),("value_isDefEq",toJson valueDefEq),
    ("normalized_value_actual_raw",normalizedA),("normalized_value_expected_raw",normalizedB),
    ("normalized_value_exprEqual",toJson normalizedEqual),("normalized_value_isDefEq",toJson normalizedDefEq),
    ("normalization",toJson "Only unfold all paired proposition-valued own compiler _proof_ helpers; no binder or metadata erasure"),
    ("actual_axioms",← afAxioms actual),("expected_axioms",← afAxioms expected)]
  if requireValue then
    unless valueDefEq && normalizedDefEq && normalizedEqual do throwError "Full definition kernel/structural mismatch {actual}"

run_cmd liftTermElabM do
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.numerator ``GAIOriginalDefs.numerator true
  afRecord "definition_rfl" ``original_value_numerator
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.poleProduct ``GAIOriginalDefs.poleProduct true
  afRecord "definition_rfl" ``original_value_poleProduct
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.actualR ``GAIOriginalDefs.actualR true
  afRecord "definition_rfl" ``original_value_actualR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedPoleProduct ``GAIOriginalDefs.clearedPoleProduct true
  afRecord "definition_rfl" ``original_value_clearedPoleProduct
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedR ``GAIOriginalDefs.clearedR true
  afRecord "definition_rfl" ``original_value_clearedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient ``GAIOriginalDefs.leadingPoleCoefficient true
  afRecord "definition_rfl" ``original_value_leadingPoleCoefficient
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.weightedR ``GAIOriginalDefs.weightedR true
  afRecord "definition_rfl" ``original_value_weightedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedWeightedR ``GAIOriginalDefs.clearedWeightedR true
  afRecord "definition_rfl" ``original_value_clearedWeightedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient ``GAIOriginalDefs.weightedLeadingPoleCoefficient true
  afRecord "definition_rfl" ``original_value_weightedLeadingPoleCoefficient
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phase ``GAIOriginalDefs.phase true
  afRecord "definition_rfl" ``original_value_phase
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseRatio ``GAIOriginalDefs.phaseRatio true
  afRecord "definition_rfl" ``original_value_phaseRatio
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseSlope ``GAIOriginalDefs.phaseSlope true
  afRecord "definition_rfl" ``original_value_phaseSlope
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant ``GAIOriginalDefs.upperSlopeConstant true
  afRecord "definition_rfl" ``original_value_upperSlopeConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap ``GAIOriginalDefs.smoothPhaseGap true
  afRecord "definition_rfl" ``original_value_smoothPhaseGap
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope ``GAIOriginalDefs.smoothPhaseSlope true
  afRecord "definition_rfl" ``original_value_smoothPhaseSlope
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio ``GAIOriginalDefs.smoothPhaseRatio true
  afRecord "definition_rfl" ``original_value_smoothPhaseRatio
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm ``GAIOriginalDefs.actualMomentTerm true
  afRecord "definition_rfl" ``original_value_actualMomentTerm
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence ``GAIOriginalDefs.actualMomentSequence true
  afRecord "definition_rfl" ``original_value_actualMomentSequence
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment ``GAIOriginalDefs.actualMoment true
  afRecord "definition_rfl" ``original_value_actualMoment
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.tailPower ``GAIOriginalDefs.tailPower true
  afRecord "definition_rfl" ``original_value_tailPower
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.tailCoefficient ``GAIOriginalDefs.tailCoefficient true
  afRecord "definition_rfl" ``original_value_tailCoefficient
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant ``GAIOriginalDefs.tailWeightConstant true
  afRecord "definition_rfl" ``original_value_tailWeightConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant ``GAIOriginalDefs.tailMajorant true
  afRecord "definition_rfl" ``original_value_tailMajorant
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailExponent ``GAIOriginalDefs.tailExponent true
  afRecord "definition_rfl" ``original_value_tailExponent
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant ``GAIOriginalDefs.momentBoundConstant true
  afRecord "definition_rfl" ``original_value_momentBoundConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence ``GAIOriginalDefs.actualWeightedSequence true
  afRecord "definition_rfl" ``original_value_actualWeightedSequence
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight ``GAIOriginalDefs.weightedCoefficientHeight true
  afRecord "definition_rfl" ``original_value_weightedCoefficientHeight
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor ``GAIOriginalDefs.analyticPrefactor true
  afRecord "definition_rfl" ``original_value_analyticPrefactor
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.uniformError ``GAIOriginalDefs.uniformError true
  afRecord "definition_rfl" ``original_value_uniformError
