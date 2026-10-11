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

run_cmd liftTermElabM do
  afRecord "definition" ``ZetaNine.CoefficientMap.numerator
  afRecord "definition" ``ZetaNine.CoefficientMap.poleProduct
  afRecord "definition" ``ZetaNine.CoefficientMap.actualR
  afRecord "definition" ``ZetaNine.CoefficientMap.clearedPoleProduct
  afRecord "definition" ``ZetaNine.CoefficientMap.clearedR
  afRecord "definition" ``ZetaNine.CoefficientMap.leadingPoleCoefficient
  afRecord "definition" ``ZetaNine.CoefficientMap.weightedR
  afRecord "definition" ``ZetaNine.CoefficientMap.clearedWeightedR
  afRecord "definition" ``ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient
  afRecord "definition" ``ZetaNine.AnalyticPhase.phase
  afRecord "definition" ``ZetaNine.AnalyticPhase.phaseRatio
  afRecord "definition" ``ZetaNine.AnalyticPhase.phaseSlope
  afRecord "definition" ``ZetaNine.AnalyticPhase.upperSlopeConstant
  afRecord "definition" ``ZetaNine.AnalyticPhase.smoothPhaseGap
  afRecord "definition" ``ZetaNine.AnalyticPhase.smoothPhaseSlope
  afRecord "definition" ``ZetaNine.AnalyticPhase.smoothPhaseRatio
  afRecord "definition" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm
  afRecord "definition" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence
  afRecord "definition" ``ZetaNine.AnalyticMomentBounds.actualMoment
  afRecord "definition" ``ZetaNine.AnalyticMomentBounds.tailPower
  afRecord "definition" ``ZetaNine.AnalyticMomentBounds.tailCoefficient
  afRecord "definition" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant
  afRecord "definition" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant
  afRecord "definition" ``ZetaNine.AnalyticUniformMomentBound.tailExponent
  afRecord "definition" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant
  afRecord "definition" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence
  afRecord "definition" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight
  afRecord "definition" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor
  afRecord "definition" ``ZetaNine.AnalyticWeightedBound.uniformError
  let env ← getEnv
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if #[`Definitions.Def_ZetaNine_CoefficientMap, `Definitions.Def_ZetaNine_AnalyticPhase, `Definitions.Def_ZetaNine_AnalyticUniformWeighted].contains m then
      let data := env.header.moduleData[i]!
      afEmit <| Json.mkObj [("kind",toJson "module_inventory"),("module",toJson m.toString),
        ("constant_names",toJson (data.constNames.map Name.toString)),
        ("extra_names",toJson (data.extraConstNames.map Name.toString))]
      for n in data.constNames do afRecord "module_declaration" n
      for n in data.extraConstNames do
        afEmit <| Json.mkObj [("kind",toJson "compiler_extra_environment_visibility"),("module",toJson m.toString),
          ("name",toJson n.toString),("actual_env_find_some",toJson (env.find? n).isSome)]
        if (env.find? n).isSome then afRecord "module_extra" n
