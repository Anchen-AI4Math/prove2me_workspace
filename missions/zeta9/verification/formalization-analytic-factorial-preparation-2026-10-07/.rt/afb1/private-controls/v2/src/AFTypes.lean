import AnalyticWeightedBound
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
open ZetaNine.AnalyticFactorialBounds
open ZetaNine.AnalyticMomentBounds
open ZetaNine.AnalyticPSeriesTail
open ZetaNine.AnalyticPhase
open ZetaNine.AnalyticRationalFactorial
open ZetaNine.AnalyticRationalLogBound
open ZetaNine.AnalyticRationalTail
open ZetaNine.AnalyticUniformMomentBound
open ZetaNine.AnalyticWeightedBound
open ZetaNine.CoefficientMap

private def afEmit (j : Json) : MetaM Unit := do
  liftM <| IO.println ("AF_RECORD|" ++ j.compress)

private def afAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def afRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let mut value := Json.null
  let mut valueTyped := false
  if let some e := ci.value? true then
    value := toJson (reprStr e)
    valueTyped ← isDefEq (← inferType e) ci.type
    unless valueTyped do throwError "Actual value/type kernel mismatch {n}"
  afEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",value),
    ("value_type_isDefEq",toJson valueTyped),
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
  afRecord "theorem" ``ZetaNine.AnalyticFactorialBounds.real_factorial_pos
  afRecord "theorem" ``ZetaNine.AnalyticFactorialBounds.log_factorial_succ
  afRecord "theorem" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper
  afRecord "theorem" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower
  afRecord "theorem" ``ZetaNine.AnalyticFactorialBounds.log_factorial_lower
  afRecord "theorem" ``ZetaNine.AnalyticFactorialBounds.log_factorial_upper
  afRecord "theorem" ``ZetaNine.AnalyticFactorialBounds.log_factorial_pred
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.rational_factorial_ne_zero
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.ascending_product_factorial
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial_real
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.actualR_pos
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.actualR_real_pos
  afRecord "theorem" ``ZetaNine.AnalyticRationalFactorial.actualR_log_factorial
  afRecord "theorem" ``ZetaNine.AnalyticRationalLogBound.scaled_phase_identity
  afRecord "theorem" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase
  afRecord "theorem" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified
  afRecord "theorem" ``ZetaNine.AnalyticRationalLogBound.actualR_le_certified
  afRecord "theorem" ``ZetaNine.AnalyticRationalLogBound.actualR_compact_bound
  afRecord "theorem" ``ZetaNine.AnalyticRationalTail.actual_falling_product_le
  afRecord "theorem" ``ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le
  afRecord "theorem" ``ZetaNine.AnalyticRationalTail.actual_poleProduct_ge
  afRecord "theorem" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational
  afRecord "theorem" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound
  afRecord "theorem" ``ZetaNine.AnalyticRationalTail.actual_tail_weight_le
  afRecord "theorem" ``ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow
  afRecord "theorem" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable
  afRecord "theorem" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound
  afRecord "theorem" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_zero_of_pos_le
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_nonneg
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_nonneg
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actual_compact_weight_le
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actual_compact_momentTerm_bound
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.tailPower_ge
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.tailCoefficient_nonneg
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actual_tail_momentTerm_bound
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail
  afRecord "theorem" ``ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_pos
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_le
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_pos
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.log_tailWeightConstant
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_identity
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant_pos
  afRecord "theorem" ``ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.actualWeighted_summable
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.actualWeighted_tsum_eq_actual_moment_sum
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.actualMoment_nonneg
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight_nonneg
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor_eq_uniform_exponent
  afRecord "theorem" ``ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one
  let env ← getEnv
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if #[`CoefficientMap, `AnalyticFactorialBounds, `AnalyticRationalFactorial, `missions.zeta9.formalization.AnalyticPhase, `AnalyticPhaseUpperBound, `AnalyticRationalLogBound, `AnalyticRationalTail, `AnalyticPSeriesTail, `AnalyticMomentBounds, `AnalyticUniformMomentBound, `AnalyticWeightedBound].contains m then
      let data := env.header.moduleData[i]!
      afEmit <| Json.mkObj [("kind",toJson "module_inventory"),("module",toJson m.toString),
        ("constant_names",toJson (data.constNames.map Name.toString)),
        ("extra_names",toJson (data.extraConstNames.map Name.toString))]
      for n in data.constNames do afRecord "module_declaration" n
      for n in data.extraConstNames do
        if (env.find? n).isSome then afRecord "module_extra" n
