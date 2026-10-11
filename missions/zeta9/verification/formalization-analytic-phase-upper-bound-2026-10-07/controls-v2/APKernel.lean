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
  liftM <| IO.println ("AP_RECORD|" ++ j.compress)

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

namespace APOriginalDefs
def phase (x : ℝ) : ℝ :=
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    (x - 1) * Real.log (x - 1) - 10 * (x + 1) * Real.log (x + 1)

def phaseRatio (x : ℝ) : ℝ := (x + 2) * x ^ 10 / ((x - 1) * (x + 1) ^ 10)

def phaseSlope (x : ℝ) : ℝ :=
  10 * Real.log x + Real.log (x + 2) - Real.log (x - 1) - 10 * Real.log (x + 1)

def upperSlopeConstant : ℝ := (301 / 100 : ℝ) * (101 / 201 : ℝ) ^ 10

def smoothPhaseGap (x : ℝ) : ℝ :=
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    10 * (x + 1) * Real.log (x + 1) - ZetaNine.AnalyticPhase.phase 1 -
      (x - 1) * (1 + Real.log ZetaNine.AnalyticPhase.upperSlopeConstant)

def smoothPhaseSlope (x : ℝ) : ℝ :=
  10 * Real.log x + Real.log (x + 2) - 10 * Real.log (x + 1) -
    Real.log ZetaNine.AnalyticPhase.upperSlopeConstant

def smoothPhaseRatio (x : ℝ) : ℝ :=
  (x + 2) * (x / (x + 1)) ^ 10

end APOriginalDefs

theorem original_value_phase : APOriginalDefs.phase = ZetaNine.AnalyticPhase.phase := rfl
theorem original_value_phaseRatio : APOriginalDefs.phaseRatio = ZetaNine.AnalyticPhase.phaseRatio := rfl
theorem original_value_phaseSlope : APOriginalDefs.phaseSlope = ZetaNine.AnalyticPhase.phaseSlope := rfl
theorem original_value_upperSlopeConstant : APOriginalDefs.upperSlopeConstant = ZetaNine.AnalyticPhase.upperSlopeConstant := rfl
theorem original_value_smoothPhaseGap : APOriginalDefs.smoothPhaseGap = ZetaNine.AnalyticPhase.smoothPhaseGap := rfl
theorem original_value_smoothPhaseSlope : APOriginalDefs.smoothPhaseSlope = ZetaNine.AnalyticPhase.smoothPhaseSlope := rfl
theorem original_value_smoothPhaseRatio : APOriginalDefs.smoothPhaseRatio = ZetaNine.AnalyticPhase.smoothPhaseRatio := rfl

namespace APExpected
theorem phaseGap_identity (x : ℝ) :
    (x - 1) * (x + 1) ^ 10 - (x + 2) * x ^ 10 =
    (743876235460997060507 / 100000000000000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 0 +
    (109589356802878649457 / 100000000000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 1 +
    (10634683646357555663 / 2000000000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 2 +
    (29280046551142071 / 2500000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 3 +
    (1524457114482447 / 100000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 4 +
    (32277046531191 / 2500000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 5 +
    (73792828347 / 10000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 6 +
    (71169471 / 25000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 7 +
    (1428963 / 2000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 8 +
    (1057 / 10 : ℝ) * (x - (101 / 100 : ℝ)) ^ 9 +
    (7 / 1 : ℝ) * (x - (101 / 100 : ℝ)) ^ 10 := by
  exact @ZetaNine.AnalyticPhase.phaseGap_identity x

theorem phaseGap_pos (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    0 < (x - 1) * (x + 1) ^ 10 - (x + 2) * x ^ 10 := by
  exact @ZetaNine.AnalyticPhase.phaseGap_pos x hx

theorem phaseRatio_pos (x : ℝ) (hx : 1 < x) : 0 < phaseRatio x := by
  exact @ZetaNine.AnalyticPhase.phaseRatio_pos x hx

theorem phaseRatio_lt_one (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    phaseRatio x < 1 := by
  exact @ZetaNine.AnalyticPhase.phaseRatio_lt_one x hx

theorem phaseSlope_eq_log_ratio (x : ℝ) (hx : 1 < x) :
    phaseSlope x = Real.log (phaseRatio x) := by
  exact @ZetaNine.AnalyticPhase.phaseSlope_eq_log_ratio x hx

theorem phaseSlope_neg_right (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    phaseSlope x < 0 := by
  exact @ZetaNine.AnalyticPhase.phaseSlope_neg_right x hx

theorem hasDerivAt_mul_log_shift (x a : ℝ) (ha : x + a ≠ 0) :
    HasDerivAt (fun y : ℝ => (y + a) * Real.log (y + a))
      (Real.log (x + a) + 1) x := by
  exact @ZetaNine.AnalyticPhase.hasDerivAt_mul_log_shift x a ha

theorem phase_hasDerivAt (x : ℝ) (hx : 1 < x) :
    HasDerivAt phase (phaseSlope x) x := by
  exact @ZetaNine.AnalyticPhase.phase_hasDerivAt x hx

theorem deriv_phase (x : ℝ) (hx : 1 < x) : deriv phase x = phaseSlope x := by
  exact @ZetaNine.AnalyticPhase.deriv_phase x hx

theorem phase_strictAntiOn_right : StrictAntiOn phase (Ici (101 / 100 : ℝ)) := by
  exact @ZetaNine.AnalyticPhase.phase_strictAntiOn_right 

theorem phase_le_right_endpoint (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    phase x ≤ phase (101 / 100) := by
  exact @ZetaNine.AnalyticPhase.phase_le_right_endpoint x hx

theorem upperSlopeConstant_pos : 0 < upperSlopeConstant := by
  exact @ZetaNine.AnalyticPhase.upperSlopeConstant_pos 

theorem upperSlopeConstant_eq : upperSlopeConstant =
    (33249125974877255751301 / 10763674952097696180200100 : ℝ) := by
  exact @ZetaNine.AnalyticPhase.upperSlopeConstant_eq 

theorem phaseRatio_small_interval_le (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : phaseRatio (1 + u) ≤ upperSlopeConstant / u := by
  exact @ZetaNine.AnalyticPhase.phaseRatio_small_interval_le u hu hu1

theorem phaseSlope_small_interval_le (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : phaseSlope (1 + u) ≤ Real.log (upperSlopeConstant / u) := by
  exact @ZetaNine.AnalyticPhase.phaseSlope_small_interval_le u hu hu1

theorem phase_one_eq : phase 1 = 3 * Real.log 3 - 20 * Real.log 2 := by
  exact @ZetaNine.AnalyticPhase.phase_one_eq 

theorem smoothPhaseGap_one : smoothPhaseGap 1 = 0 := by
  exact @ZetaNine.AnalyticPhase.smoothPhaseGap_one 

theorem smoothPhaseGap_hasDerivAt (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt smoothPhaseGap (smoothPhaseSlope x) x := by
  exact @ZetaNine.AnalyticPhase.smoothPhaseGap_hasDerivAt x hx

theorem smoothPhaseRatio_pos (x : ℝ) (hx : 1 ≤ x) :
    0 < smoothPhaseRatio x := by
  exact @ZetaNine.AnalyticPhase.smoothPhaseRatio_pos x hx

theorem smoothPhaseRatio_le_upperSlopeConstant (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    smoothPhaseRatio x ≤ upperSlopeConstant := by
  exact @ZetaNine.AnalyticPhase.smoothPhaseRatio_le_upperSlopeConstant x hx

theorem smoothPhaseSlope_eq_log_ratio (x : ℝ) (hx : 1 ≤ x) :
    smoothPhaseSlope x =
      Real.log (smoothPhaseRatio x) - Real.log upperSlopeConstant := by
  exact @ZetaNine.AnalyticPhase.smoothPhaseSlope_eq_log_ratio x hx

theorem smoothPhaseSlope_nonpos (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    smoothPhaseSlope x ≤ 0 := by
  exact @ZetaNine.AnalyticPhase.smoothPhaseSlope_nonpos x hx

theorem smoothPhaseGap_antitoneOn :
    AntitoneOn smoothPhaseGap (Icc (1 : ℝ) (101 / 100 : ℝ)) := by
  exact @ZetaNine.AnalyticPhase.smoothPhaseGap_antitoneOn 

theorem smoothPhaseGap_le_zero (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    smoothPhaseGap x ≤ 0 := by
  exact @ZetaNine.AnalyticPhase.smoothPhaseGap_le_zero x hx

theorem mul_one_add_log_div_le (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    u * (1 + Real.log (a / u)) ≤ a := by
  exact @ZetaNine.AnalyticPhase.mul_one_add_log_div_le a u ha hu

theorem phase_small_interval_identity (u : ℝ) (hu : 0 < u) :
    phase (1 + u) = phase 1 +
      u * (1 + Real.log (upperSlopeConstant / u)) + smoothPhaseGap (1 + u) := by
  exact @ZetaNine.AnalyticPhase.phase_small_interval_identity u hu

theorem phase_small_interval_le_one_add_constant (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) :
    phase (1 + u) ≤ phase 1 + upperSlopeConstant := by
  exact @ZetaNine.AnalyticPhase.phase_small_interval_le_one_add_constant u hu hu1

theorem phase_global_le_one_add_constant (x : ℝ) (hx : 1 < x) :
    phase x ≤ phase 1 + upperSlopeConstant := by
  exact @ZetaNine.AnalyticPhase.phase_global_le_one_add_constant x hx

theorem log_two_lower_rational : (693147 / 1000000 : ℝ) < Real.log 2 := by
  exact @ZetaNine.AnalyticPhase.log_two_lower_rational 

theorem log_three_upper_rational : Real.log 3 < (1098613 / 1000000 : ℝ) := by
  exact @ZetaNine.AnalyticPhase.log_three_upper_rational 

theorem upperSlopeConstant_lt_rational :
    upperSlopeConstant < (309 / 100000 : ℝ) := by
  exact @ZetaNine.AnalyticPhase.upperSlopeConstant_lt_rational 

theorem phase_one_add_constant_lt_certified :
    phase 1 + upperSlopeConstant < (-10564011 / 1000000 : ℝ) := by
  exact @ZetaNine.AnalyticPhase.phase_one_add_constant_lt_certified 

theorem phase_global_lt_certified (x : ℝ) (hx : 1 < x) :
    phase x < (-10564011 / 1000000 : ℝ) := by
  exact @ZetaNine.AnalyticPhase.phase_global_lt_certified x hx

theorem phase_global_upper_bound :
    ∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ) := by
  exact @ZetaNine.AnalyticPhase.phase_global_upper_bound 

theorem exact_open_domain : ∀ x : ℝ, 1 < x →
    ZetaNine.AnalyticPhase.phase x ≤ (-2641 / 250 : ℝ) :=
  ZetaNine.AnalyticPhase.phase_global_upper_bound
end APExpected

private def apCompare (kind : String) (actual expected : Name) (requireValue : Bool) : MetaM Unit := do
  let a ← getConstInfo actual
  let b ← getConstInfo expected
  let typeEqual := Expr.equal a.type b.type
  let typeDefEq ← isDefEq a.type b.type
  unless typeDefEq do throwError "Type mismatch {actual} {expected}"
  let mut valueEqual := false
  let mut valueDefEq := false
  let mut va := Json.null
  let mut vb := Json.null
  if requireValue then
    let some av := a.value? | throwError "No actual definition value {actual}"
    let some bv := b.value? | throwError "No original definition value {expected}"
    valueEqual := Expr.equal av bv
    valueDefEq ← isDefEq av bv
    unless typeEqual && valueEqual && valueDefEq do
      throwError "Full definition mismatch {actual}"
    va := toJson (reprStr av)
    vb := toJson (reprStr bv)
  apEmit <| Json.mkObj [("kind",toJson kind),("actual",toJson actual.toString),
    ("expected",toJson expected.toString),("type_actual_raw",toJson (reprStr a.type)),
    ("type_expected_raw",toJson (reprStr b.type)),("type_exprEqual",toJson typeEqual),
    ("type_isDefEq",toJson typeDefEq),("value_actual_raw",va),("value_expected_raw",vb),
    ("value_exprEqual",toJson valueEqual),("value_isDefEq",toJson valueDefEq),
    ("actual_axioms",← apAxioms actual),("expected_axioms",← apAxioms expected)]

run_cmd liftTermElabM do
  apCompare "definition_compare" ``ZetaNine.AnalyticPhase.phase ``APOriginalDefs.phase true
  apRecord "definition_rfl" ``original_value_phase
  apCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseRatio ``APOriginalDefs.phaseRatio true
  apRecord "definition_rfl" ``original_value_phaseRatio
  apCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseSlope ``APOriginalDefs.phaseSlope true
  apRecord "definition_rfl" ``original_value_phaseSlope
  apCompare "definition_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant ``APOriginalDefs.upperSlopeConstant true
  apRecord "definition_rfl" ``original_value_upperSlopeConstant
  apCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap ``APOriginalDefs.smoothPhaseGap true
  apRecord "definition_rfl" ``original_value_smoothPhaseGap
  apCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope ``APOriginalDefs.smoothPhaseSlope true
  apRecord "definition_rfl" ``original_value_smoothPhaseSlope
  apCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio ``APOriginalDefs.smoothPhaseRatio true
  apRecord "definition_rfl" ``original_value_smoothPhaseRatio
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseGap_identity ``APExpected.phaseGap_identity false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseGap_pos ``APExpected.phaseGap_pos false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseRatio_pos ``APExpected.phaseRatio_pos false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseRatio_lt_one ``APExpected.phaseRatio_lt_one false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseSlope_eq_log_ratio ``APExpected.phaseSlope_eq_log_ratio false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseSlope_neg_right ``APExpected.phaseSlope_neg_right false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.hasDerivAt_mul_log_shift ``APExpected.hasDerivAt_mul_log_shift false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_hasDerivAt ``APExpected.phase_hasDerivAt false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.deriv_phase ``APExpected.deriv_phase false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_strictAntiOn_right ``APExpected.phase_strictAntiOn_right false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_le_right_endpoint ``APExpected.phase_le_right_endpoint false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant_pos ``APExpected.upperSlopeConstant_pos false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant_eq ``APExpected.upperSlopeConstant_eq false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseRatio_small_interval_le ``APExpected.phaseRatio_small_interval_le false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseSlope_small_interval_le ``APExpected.phaseSlope_small_interval_le false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_one_eq ``APExpected.phase_one_eq false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_one ``APExpected.smoothPhaseGap_one false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_hasDerivAt ``APExpected.smoothPhaseGap_hasDerivAt false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio_pos ``APExpected.smoothPhaseRatio_pos false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio_le_upperSlopeConstant ``APExpected.smoothPhaseRatio_le_upperSlopeConstant false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope_eq_log_ratio ``APExpected.smoothPhaseSlope_eq_log_ratio false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope_nonpos ``APExpected.smoothPhaseSlope_nonpos false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_antitoneOn ``APExpected.smoothPhaseGap_antitoneOn false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_le_zero ``APExpected.smoothPhaseGap_le_zero false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.mul_one_add_log_div_le ``APExpected.mul_one_add_log_div_le false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_small_interval_identity ``APExpected.phase_small_interval_identity false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_small_interval_le_one_add_constant ``APExpected.phase_small_interval_le_one_add_constant false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_global_le_one_add_constant ``APExpected.phase_global_le_one_add_constant false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.log_two_lower_rational ``APExpected.log_two_lower_rational false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.log_three_upper_rational ``APExpected.log_three_upper_rational false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant_lt_rational ``APExpected.upperSlopeConstant_lt_rational false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_one_add_constant_lt_certified ``APExpected.phase_one_add_constant_lt_certified false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_global_lt_certified ``APExpected.phase_global_lt_certified false
  apCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_global_upper_bound ``APExpected.phase_global_upper_bound false
  apCompare "exact_domain_compare" ``ZetaNine.AnalyticPhase.phase_global_upper_bound ``APExpected.exact_open_domain false
