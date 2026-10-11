import Definitions.Def_ZetaNine_AnalyticPhase
import Native.AnalyticPhaseUpperBound
import Solutions.Sol_ZetaNine_AnalyticPhase_phase_global_upper_bound
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
noncomputable section
open Set
open ZetaNine.AnalyticPhase
namespace PhasePlatformWhole
theorem whole_phase : ZetaNine.AnalyticPhase.phase = PhasePlatformNativeOracle.phase := by rfl
theorem whole_phaseRatio : ZetaNine.AnalyticPhase.phaseRatio = PhasePlatformNativeOracle.phaseRatio := by rfl
theorem whole_phaseSlope : ZetaNine.AnalyticPhase.phaseSlope = PhasePlatformNativeOracle.phaseSlope := by rfl
theorem whole_upperSlopeConstant : ZetaNine.AnalyticPhase.upperSlopeConstant = PhasePlatformNativeOracle.upperSlopeConstant := by rfl
theorem whole_smoothPhaseGap : ZetaNine.AnalyticPhase.smoothPhaseGap = PhasePlatformNativeOracle.smoothPhaseGap := by rfl
theorem whole_smoothPhaseSlope : ZetaNine.AnalyticPhase.smoothPhaseSlope = PhasePlatformNativeOracle.smoothPhaseSlope := by rfl
theorem whole_smoothPhaseRatio : ZetaNine.AnalyticPhase.smoothPhaseRatio = PhasePlatformNativeOracle.smoothPhaseRatio := by rfl
end PhasePlatformWhole
namespace PhasePlatformBoundary
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
end PhasePlatformBoundary
