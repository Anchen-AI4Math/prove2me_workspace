import missions.zeta9.formalization.AnalyticPhaseUpperBound
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
open Set
open ZetaNine.AnalyticPhase
open Lean Meta Elab Command

private def apEmit (j : Json) : MetaM Unit := do
  liftM <| IO.println ("PHI_RECORD|" ++ j.compress)

private def apAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def apRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let mut value := Json.null
  let mut typed := false
  if let some e := ci.value? true then
    value := toJson (reprStr e)
    typed ← isDefEq (← inferType e) ci.type
    unless typed do throwError "Declaration value does not have its full type: {n}"
  apEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",value),
    ("full_value_typed",toJson typed),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← apAxioms n)]
namespace APIndBoundary
theorem phase_endpoint_one : phase 1 = 3 * Real.log 3 - 20 * Real.log 2 := phase_one_eq
theorem gap_endpoint_one : smoothPhaseGap 1 = 0 := smoothPhaseGap_one
theorem ratio_endpoint_one : smoothPhaseRatio 1 = (3 / 1024 : ℝ) := by norm_num [smoothPhaseRatio]
theorem slope_constant_exact : upperSlopeConstant =
    (33249125974877255751301 / 10763674952097696180200100 : ℝ) := upperSlopeConstant_eq
theorem slope_constant_small : 0 < upperSlopeConstant ∧ upperSlopeConstant < (1 / 100 : ℝ) := by
  constructor
  · exact upperSlopeConstant_pos
  · exact upperSlopeConstant_lt_rational.trans (by norm_num)
theorem universal_cap_attained : upperSlopeConstant *
    (1 + Real.log (upperSlopeConstant / upperSlopeConstant)) = upperSlopeConstant := by
  rw [div_self (ne_of_gt upperSlopeConstant_pos), Real.log_one]
  ring
theorem gap_endpoint_right : smoothPhaseGap (101 / 100) ≤ 0 := by
  exact smoothPhaseGap_le_zero (101 / 100) (by constructor <;> norm_num)
theorem phase_endpoint_right : phase (101 / 100) ≤ (-2641 / 250 : ℝ) :=
  phase_global_upper_bound (101 / 100) (by norm_num)
theorem phase_inside_left : phase (1003 / 1000) ≤ (-2641 / 250 : ℝ) :=
  phase_global_upper_bound (1003 / 1000) (by norm_num)
theorem phase_in_right : phase 2 ≤ (-2641 / 250 : ℝ) := phase_global_upper_bound 2 (by norm_num)
theorem phase_zero_exact : phase 0 = 2 * Real.log 2 := by norm_num [phase]
theorem phase_zero_exceeds_cap : (-2641 / 250 : ℝ) < phase 0 := by
  rw [phase_zero_exact]
  have h := log_two_lower_rational
  linarith
theorem excluded_endpoint_one : ¬ (1 : ℝ) < 1 := by norm_num
theorem excluded_zero : ¬ (1 : ℝ) < 0 := by norm_num
theorem global_stronger_margin : ∀ x : ℝ, 1 < x → phase x < (-10564011 / 1000000 : ℝ) :=
  phase_global_lt_certified
end APIndBoundary

run_cmd liftTermElabM do
  apRecord "typed_boundary" ``APIndBoundary.phase_endpoint_one
  apRecord "typed_boundary" ``APIndBoundary.gap_endpoint_one
  apRecord "typed_boundary" ``APIndBoundary.ratio_endpoint_one
  apRecord "typed_boundary" ``APIndBoundary.slope_constant_exact
  apRecord "typed_boundary" ``APIndBoundary.slope_constant_small
  apRecord "typed_boundary" ``APIndBoundary.universal_cap_attained
  apRecord "typed_boundary" ``APIndBoundary.gap_endpoint_right
  apRecord "typed_boundary" ``APIndBoundary.phase_endpoint_right
  apRecord "typed_boundary" ``APIndBoundary.phase_inside_left
  apRecord "typed_boundary" ``APIndBoundary.phase_in_right
  apRecord "typed_boundary" ``APIndBoundary.phase_zero_exact
  apRecord "typed_boundary" ``APIndBoundary.phase_zero_exceeds_cap
  apRecord "typed_boundary" ``APIndBoundary.excluded_endpoint_one
  apRecord "typed_boundary" ``APIndBoundary.excluded_zero
  apRecord "typed_boundary" ``APIndBoundary.global_stronger_margin
