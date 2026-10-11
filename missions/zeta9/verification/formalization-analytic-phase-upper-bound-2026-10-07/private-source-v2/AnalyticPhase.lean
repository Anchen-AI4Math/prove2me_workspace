import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
UNCOMPILED preparation for the actual phase in round7/research/analytic.md.
The phase, ratio and derivative are actual functions, not assumed bounds.
This does not yet establish the moment asymptotic, uniform o(1), or Z9.A.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set

namespace ZetaNine.AnalyticPhase

def phase (x : ℝ) : ℝ :=
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    (x - 1) * Real.log (x - 1) - 10 * (x + 1) * Real.log (x + 1)

def phaseRatio (x : ℝ) : ℝ := (x + 2) * x ^ 10 / ((x - 1) * (x + 1) ^ 10)

def phaseSlope (x : ℝ) : ℝ :=
  10 * Real.log x + Real.log (x + 2) - Real.log (x - 1) - 10 * Real.log (x + 1)

def upperSlopeConstant : ℝ := (301 / 100 : ℝ) * (101 / 201 : ℝ) ^ 10

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
  ring

theorem phaseGap_pos (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    0 < (x - 1) * (x + 1) ^ 10 - (x + 2) * x ^ 10 := by
  rw [phaseGap_identity]
  have hy : 0 ≤ x - (101 / 100 : ℝ) := sub_nonneg.mpr hx
  positivity

theorem phaseRatio_pos (x : ℝ) (hx : 1 < x) : 0 < phaseRatio x := by
  unfold phaseRatio
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hxp : 0 < x + 1 := by linarith
  have hx2 : 0 < x + 2 := by linarith
  positivity

theorem phaseRatio_lt_one (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    phaseRatio x < 1 := by
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hxp : 0 < x + 1 := by linarith
  have hd : 0 < (x - 1) * (x + 1) ^ 10 := by positivity
  unfold phaseRatio
  apply (div_lt_one hd).mpr
  exact sub_pos.mp (phaseGap_pos x hx)

theorem phaseSlope_eq_log_ratio (x : ℝ) (hx : 1 < x) :
    phaseSlope x = Real.log (phaseRatio x) := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
  have hxm : x - 1 ≠ 0 := ne_of_gt (by linarith : 0 < x - 1)
  have hxp : x + 1 ≠ 0 := ne_of_gt (by linarith : 0 < x + 1)
  have hx2 : x + 2 ≠ 0 := ne_of_gt (by linarith : 0 < x + 2)
  unfold phaseSlope phaseRatio
  rw [Real.log_div (mul_ne_zero hx2 (pow_ne_zero 10 hx0))
    (mul_ne_zero hxm (pow_ne_zero 10 hxp)),
    Real.log_mul hx2 (pow_ne_zero 10 hx0),
    Real.log_mul hxm (pow_ne_zero 10 hxp), Real.log_pow, Real.log_pow]
  ring

theorem phaseSlope_neg_right (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    phaseSlope x < 0 := by
  have hx1 : 1 < x := by linarith
  rw [phaseSlope_eq_log_ratio x hx1]
  exact Real.log_neg (phaseRatio_pos x hx1) (phaseRatio_lt_one x hx)

theorem hasDerivAt_mul_log_shift (x a : ℝ) (ha : x + a ≠ 0) :
    HasDerivAt (fun y : ℝ => (y + a) * Real.log (y + a))
      (Real.log (x + a) + 1) x := by
  have h := ((hasDerivAt_id x).add_const a).mul
    (((hasDerivAt_id x).add_const a).log ha)
  have hd : (x + a) * (1 / (x + a)) = 1 := by
    field_simp [ha]
  simpa [id_eq, hd] using h

theorem phase_hasDerivAt (x : ℝ) (hx : 1 < x) :
    HasDerivAt phase (phaseSlope x) x := by
  have h0 : x + 0 ≠ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by linarith
  have hm : x + (-1) ≠ 0 := by linarith
  have hp : x + 1 ≠ 0 := by linarith
  have h := (((hasDerivAt_mul_log_shift x 0 h0).const_mul 10).add
    (hasDerivAt_mul_log_shift x 2 h2)).sub
    (hasDerivAt_mul_log_shift x (-1) hm)
  have h' := h.sub ((hasDerivAt_mul_log_shift x 1 hp).const_mul 10)
  convert h' using 1 <;> (try simp only [phase, phaseSlope, add_zero, sub_eq_add_neg]) <;> ring

theorem deriv_phase (x : ℝ) (hx : 1 < x) : deriv phase x = phaseSlope x :=
  (phase_hasDerivAt x hx).deriv

theorem phase_strictAntiOn_right : StrictAntiOn phase (Ici (101 / 100 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (101 / 100 : ℝ))
  · intro x hx
    have hx1 : 1 < x := by have h : (101 / 100 : ℝ) ≤ x := hx; linarith
    exact (phase_hasDerivAt x hx1).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : (101 / 100 : ℝ) ≤ x := interior_subset hx
    rw [deriv_phase x (by linarith : 1 < x)]
    exact phaseSlope_neg_right x hx'

theorem phase_le_right_endpoint (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    phase x ≤ phase (101 / 100) :=
  phase_strictAntiOn_right.antitoneOn (by exact le_rfl) hx hx

theorem upperSlopeConstant_pos : 0 < upperSlopeConstant := by
  norm_num [upperSlopeConstant]

theorem upperSlopeConstant_eq : upperSlopeConstant =
    (33249125974877255751301 / 10763674952097696180200100 : ℝ) := by
  norm_num [upperSlopeConstant]

theorem phaseRatio_small_interval_le (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : phaseRatio (1 + u) ≤ upperSlopeConstant / u := by
  have h2 : 0 < 2 + u := by linarith
  have hb : (1 + u) / (2 + u) ≤ (101 / 201 : ℝ) := by
    apply (div_le_iff₀ h2).mpr
    nlinarith
  have hb0 : 0 ≤ (1 + u) / (2 + u) := by positivity
  have hp : ((1 + u) / (2 + u)) ^ 10 ≤ (101 / 201 : ℝ) ^ 10 :=
    pow_le_pow_left₀ hb0 hb 10
  have hc : 3 + u ≤ (301 / 100 : ℝ) := by linarith
  have hm : (3 + u) * ((1 + u) / (2 + u)) ^ 10 ≤ upperSlopeConstant := by
    unfold upperSlopeConstant
    exact mul_le_mul hc hp (by positivity) (by norm_num)
  have he : phaseRatio (1 + u) = ((3 + u) * ((1 + u) / (2 + u)) ^ 10) / u := by
    unfold phaseRatio
    field_simp [ne_of_gt hu, ne_of_gt h2]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right hm (le_of_lt hu)

theorem phaseSlope_small_interval_le (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : phaseSlope (1 + u) ≤ Real.log (upperSlopeConstant / u) := by
  have hx : 1 < 1 + u := by linarith
  rw [phaseSlope_eq_log_ratio (1 + u) hx]
  exact Real.log_le_log (phaseRatio_pos (1 + u) hx) (phaseRatio_small_interval_le u hu hu1)

end ZetaNine.AnalyticPhase
