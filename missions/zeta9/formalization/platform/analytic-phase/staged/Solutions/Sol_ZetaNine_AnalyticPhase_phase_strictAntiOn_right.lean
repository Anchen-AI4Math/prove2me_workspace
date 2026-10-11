import Definitions.Def_ZetaNine_AnalyticPhase
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Set
open scoped BigOperators
namespace ZetaNine.AnalyticPhase

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
  convert h using 1
  all_goals first | rfl | simp [id_eq, one_div, mul_inv_cancel₀ ha]

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
  convert h' using 1
  all_goals first | rfl | (funext y; simp [phase, Pi.neg_apply, sub_eq_add_neg]; ring) | (simp [phaseSlope, id_eq, sub_eq_add_neg]; ring)

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
    phase x ≤ phase (101 / 100) := by
  have h0 : (101 / 100 : ℝ) ∈ Ici (101 / 100 : ℝ) := by
    change (101 / 100 : ℝ) ≤ (101 / 100 : ℝ)
    exact le_rfl
  exact phase_strictAntiOn_right.antitoneOn h0 hx hx

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

theorem phase_one_eq : phase 1 = 3 * Real.log 3 - 20 * Real.log 2 := by
  norm_num [phase] <;> ring

theorem smoothPhaseGap_one : smoothPhaseGap 1 = 0 := by
  norm_num [smoothPhaseGap, phase] <;> ring

theorem smoothPhaseGap_hasDerivAt (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt smoothPhaseGap (smoothPhaseSlope x) x := by
  have h0 : x + 0 ≠ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by linarith
  have hp : x + 1 ≠ 0 := by linarith
  have hmain :=
    ((((hasDerivAt_mul_log_shift x 0 h0).const_mul 10).add
      (hasDerivAt_mul_log_shift x 2 h2)).sub
        ((hasDerivAt_mul_log_shift x 1 hp).const_mul 10)).sub_const (phase 1)
  have hlinear := ((hasDerivAt_id x).sub_const 1).mul_const
    (1 + Real.log upperSlopeConstant)
  have h := hmain.sub hlinear
  convert h using 1
  all_goals first | rfl | (funext y; simp [smoothPhaseGap, id_eq, Pi.neg_apply, sub_eq_add_neg]; ring) | (simp [smoothPhaseSlope, id_eq, sub_eq_add_neg]; ring)

theorem smoothPhaseRatio_pos (x : ℝ) (hx : 1 ≤ x) :
    0 < smoothPhaseRatio x := by
  unfold smoothPhaseRatio
  have hx0 : 0 < x := by linarith
  have hp : 0 < x + 1 := by linarith
  have h2 : 0 < x + 2 := by linarith
  positivity

theorem smoothPhaseRatio_le_upperSlopeConstant (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    smoothPhaseRatio x ≤ upperSlopeConstant := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hp : 0 < x + 1 := by linarith [hx.1]
  have hb : x / (x + 1) ≤ (101 / 201 : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [hx.2]
  have hb0 : 0 ≤ x / (x + 1) := le_of_lt (div_pos hx0 hp)
  have hpow : (x / (x + 1)) ^ 10 ≤ (101 / 201 : ℝ) ^ 10 :=
    pow_le_pow_left₀ hb0 hb 10
  have hc : x + 2 ≤ (301 / 100 : ℝ) := by linarith [hx.2]
  unfold smoothPhaseRatio upperSlopeConstant
  exact mul_le_mul hc hpow (by positivity) (by norm_num)

theorem smoothPhaseSlope_eq_log_ratio (x : ℝ) (hx : 1 ≤ x) :
    smoothPhaseSlope x =
      Real.log (smoothPhaseRatio x) - Real.log upperSlopeConstant := by
  have hx0 : 0 < x := by linarith
  have hp : 0 < x + 1 := by linarith
  have h2 : 0 < x + 2 := by linarith
  have hr : 0 < x / (x + 1) := div_pos hx0 hp
  unfold smoothPhaseSlope smoothPhaseRatio
  rw [Real.log_mul (ne_of_gt h2) (pow_ne_zero 10 (ne_of_gt hr)),
    Real.log_pow, Real.log_div (ne_of_gt hx0) (ne_of_gt hp)]
  norm_num <;> ring

theorem smoothPhaseSlope_nonpos (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    smoothPhaseSlope x ≤ 0 := by
  rw [smoothPhaseSlope_eq_log_ratio x hx.1]
  exact sub_nonpos.mpr (Real.log_le_log (smoothPhaseRatio_pos x hx.1)
    (smoothPhaseRatio_le_upperSlopeConstant x hx))

theorem smoothPhaseGap_antitoneOn :
    AntitoneOn smoothPhaseGap (Icc (1 : ℝ) (101 / 100 : ℝ)) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := smoothPhaseSlope) (convex_Icc (1 : ℝ) (101 / 100 : ℝ)) ?_ ?_ ?_
  · intro x hx
    exact (smoothPhaseGap_hasDerivAt x hx.1).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ) := interior_subset hx
    exact (smoothPhaseGap_hasDerivAt x hx'.1).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ) := interior_subset hx
    exact smoothPhaseSlope_nonpos x hx'

theorem smoothPhaseGap_le_zero (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    smoothPhaseGap x ≤ 0 := by
  have h1 : (1 : ℝ) ∈ Icc (1 : ℝ) (101 / 100 : ℝ) := by
    constructor <;> norm_num
  have h := smoothPhaseGap_antitoneOn h1 hx hx.1
  simpa only [smoothPhaseGap_one] using h

/-- The universal elementary cap; its hypotheses assert only positivity. -/

theorem mul_one_add_log_div_le (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    u * (1 + Real.log (a / u)) ≤ a := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos ha hu)
  have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hu)
  have he : u * (a / u - 1) = a - u := by
    field_simp [ne_of_gt hu]
  calc
    u * (1 + Real.log (a / u)) = u + u * Real.log (a / u) := by ring
    _ ≤ u + u * (a / u - 1) := add_le_add (le_refl u) hmul
    _ = a := by rw [he]; ring

theorem phase_small_interval_identity (u : ℝ) (hu : 0 < u) :
    phase (1 + u) = phase 1 +
      u * (1 + Real.log (upperSlopeConstant / u)) + smoothPhaseGap (1 + u) := by
  rw [Real.log_div (ne_of_gt upperSlopeConstant_pos) (ne_of_gt hu)]
  unfold smoothPhaseGap phase
  have he : (1 + u : ℝ) - 1 = u := by ring
  simp only [he]
  ring

theorem phase_small_interval_le_one_add_constant (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) :
    phase (1 + u) ≤ phase 1 + upperSlopeConstant := by
  have hx : (1 + u : ℝ) ∈ Icc (1 : ℝ) (101 / 100 : ℝ) := by
    constructor <;> linarith
  have hgap := smoothPhaseGap_le_zero (1 + u) hx
  have hcap := mul_one_add_log_div_le upperSlopeConstant u upperSlopeConstant_pos hu
  rw [phase_small_interval_identity u hu]
  linarith

theorem phase_global_le_one_add_constant (x : ℝ) (hx : 1 < x) :
    phase x ≤ phase 1 + upperSlopeConstant := by
  by_cases hsmall : x ≤ (101 / 100 : ℝ)
  · have hu : 0 < x - 1 := by linarith
    have hu1 : x - 1 ≤ (1 / 100 : ℝ) := by linarith
    have h := phase_small_interval_le_one_add_constant (x - 1) hu hu1
    have he : (1 + (x - 1) : ℝ) = x := by ring
    simpa only [he] using h
  · have hright : (101 / 100 : ℝ) ≤ x := by linarith
    have hendpoint := phase_small_interval_le_one_add_constant (1 / 100)
      (by norm_num) (by norm_num)
    have he : (1 + (1 / 100) : ℝ) = 101 / 100 := by norm_num
    rw [he] at hendpoint
    exact (phase_le_right_endpoint x hright).trans hendpoint

/-- Six terms at `1/3`; the lower rational margin is strictly positive. -/

theorem log_two_lower_rational : (693147 / 1000000 : ℝ) < Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 6
  have harg : (1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) = 2 := by norm_num
  rw [harg] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Eleven terms at `1/2`, using the actual proved Mathlib geometric remainder. -/

theorem log_three_upper_rational : Real.log 3 < (1098613 / 1000000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) 11
  have harg : (1 + (1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) = 3 := by norm_num
  rw [harg] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem upperSlopeConstant_lt_rational :
    upperSlopeConstant < (309 / 100000 : ℝ) := by
  norm_num [upperSlopeConstant]

theorem phase_one_add_constant_lt_certified :
    phase 1 + upperSlopeConstant < (-10564011 / 1000000 : ℝ) := by
  rw [phase_one_eq]
  have h2 := log_two_lower_rational
  have h3 := log_three_upper_rational
  have hA := upperSlopeConstant_lt_rational
  linarith

/-- Stronger rational margin, without any finite sampling of the phase. -/

theorem phase_global_lt_certified (x : ℝ) (hx : 1 < x) :
    phase x < (-10564011 / 1000000 : ℝ) :=
  (phase_global_le_one_add_constant x hx).trans_lt phase_one_add_constant_lt_certified

/-- The actual requested whole-domain phase component, with its exact open domain. -/

theorem phase_global_upper_bound :
    ∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ) := by
  intro x hx
  have h := phase_global_lt_certified x hx
  linarith

end ZetaNine.AnalyticPhase

open ZetaNine.AnalyticPhase
theorem solution : StrictAntiOn phase (Ici (101 / 100 : ℝ)) := by
  exact ZetaNine.AnalyticPhase.phase_strictAntiOn_right

#print axioms solution
