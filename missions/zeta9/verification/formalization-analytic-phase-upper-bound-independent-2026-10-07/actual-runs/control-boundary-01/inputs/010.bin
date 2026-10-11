import missions.zeta9.formalization.AnalyticPhase

/-!
UNCOMPILED full-source candidate for the global actual phase bound.

The imported AnalyticPhase source is itself an unchanged UNCOMPILED preparation.
No Lean execution, kernel verification, moment asymptotic, uniform error estimate
or complete Z9.A result is claimed by this source-only preparation.

The numerical steps use Real.sum_range_le_log_div and
Real.log_div_le_sum_range_add, whose finite sums and remainders are already
proved in the pinned Mathlib source. All displayed constants are rational.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Set
open scoped BigOperators

namespace ZetaNine.AnalyticPhase

/-- The actual smooth remainder, with the singular `(x-1) log(x-1)` removed. -/
def smoothPhaseGap (x : ℝ) : ℝ :=
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    10 * (x + 1) * Real.log (x + 1) - phase 1 -
      (x - 1) * (1 + Real.log upperSlopeConstant)

def smoothPhaseSlope (x : ℝ) : ℝ :=
  10 * Real.log x + Real.log (x + 2) - 10 * Real.log (x + 1) -
    Real.log upperSlopeConstant

def smoothPhaseRatio (x : ℝ) : ℝ :=
  (x + 2) * (x / (x + 1)) ^ 10

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
