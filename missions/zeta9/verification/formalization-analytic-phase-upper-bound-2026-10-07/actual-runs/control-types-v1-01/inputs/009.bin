import missions.zeta9.formalization.AnalyticPhaseUpperBound
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
open Set
open ZetaNine.AnalyticPhase
open Lean Meta Elab Command

private def apEmit (j : Json) : MetaM Unit := do
  liftIO <| IO.println ("AP_RECORD|" ++ j.compress)

private def apAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def apRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let value := match ci.value? with
    | some e => Json.str (reprStr e)
    | none => Json.null
  apEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",value),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← apAxioms n)]

run_cmd liftTermElabM do
  for n in #[``ZetaNine.AnalyticPhase.phase, ``ZetaNine.AnalyticPhase.phaseRatio, ``ZetaNine.AnalyticPhase.phaseSlope, ``ZetaNine.AnalyticPhase.upperSlopeConstant, ``ZetaNine.AnalyticPhase.smoothPhaseGap, ``ZetaNine.AnalyticPhase.smoothPhaseSlope, ``ZetaNine.AnalyticPhase.smoothPhaseRatio] do apRecord "definition" n
  for n in #[``ZetaNine.AnalyticPhase.phaseGap_identity, ``ZetaNine.AnalyticPhase.phaseGap_pos, ``ZetaNine.AnalyticPhase.phaseRatio_pos, ``ZetaNine.AnalyticPhase.phaseRatio_lt_one, ``ZetaNine.AnalyticPhase.phaseSlope_eq_log_ratio, ``ZetaNine.AnalyticPhase.phaseSlope_neg_right, ``ZetaNine.AnalyticPhase.hasDerivAt_mul_log_shift, ``ZetaNine.AnalyticPhase.phase_hasDerivAt, ``ZetaNine.AnalyticPhase.deriv_phase, ``ZetaNine.AnalyticPhase.phase_strictAntiOn_right, ``ZetaNine.AnalyticPhase.phase_le_right_endpoint, ``ZetaNine.AnalyticPhase.upperSlopeConstant_pos, ``ZetaNine.AnalyticPhase.upperSlopeConstant_eq, ``ZetaNine.AnalyticPhase.phaseRatio_small_interval_le, ``ZetaNine.AnalyticPhase.phaseSlope_small_interval_le, ``ZetaNine.AnalyticPhase.phase_one_eq, ``ZetaNine.AnalyticPhase.smoothPhaseGap_one, ``ZetaNine.AnalyticPhase.smoothPhaseGap_hasDerivAt, ``ZetaNine.AnalyticPhase.smoothPhaseRatio_pos, ``ZetaNine.AnalyticPhase.smoothPhaseRatio_le_upperSlopeConstant, ``ZetaNine.AnalyticPhase.smoothPhaseSlope_eq_log_ratio, ``ZetaNine.AnalyticPhase.smoothPhaseSlope_nonpos, ``ZetaNine.AnalyticPhase.smoothPhaseGap_antitoneOn, ``ZetaNine.AnalyticPhase.smoothPhaseGap_le_zero, ``ZetaNine.AnalyticPhase.mul_one_add_log_div_le, ``ZetaNine.AnalyticPhase.phase_small_interval_identity, ``ZetaNine.AnalyticPhase.phase_small_interval_le_one_add_constant, ``ZetaNine.AnalyticPhase.phase_global_le_one_add_constant, ``ZetaNine.AnalyticPhase.log_two_lower_rational, ``ZetaNine.AnalyticPhase.log_three_upper_rational, ``ZetaNine.AnalyticPhase.upperSlopeConstant_lt_rational, ``ZetaNine.AnalyticPhase.phase_one_add_constant_lt_certified, ``ZetaNine.AnalyticPhase.phase_global_lt_certified, ``ZetaNine.AnalyticPhase.phase_global_upper_bound] do apRecord "theorem" n
  let env ← getEnv
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if #[`missions.zeta9.formalization.AnalyticPhase,
          `missions.zeta9.formalization.AnalyticPhaseUpperBound].contains m then
      let data := env.header.moduleData[i]!
      apEmit <| Json.mkObj [("kind",toJson "module_inventory"),("module",toJson m.toString),
        ("constant_names",toJson (data.constNames.map Name.toString)),
        ("extra_names",toJson (data.extraConstNames.map Name.toString))]
      for n in data.constNames do apRecord "module_declaration" n
      for n in data.extraConstNames do
        if (env.find? n).isSome then apRecord "module_extra" n
