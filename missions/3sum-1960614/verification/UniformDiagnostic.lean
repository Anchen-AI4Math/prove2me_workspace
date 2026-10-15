-- Concavity argument adapted from the pinned upstream Parameters.lean;
-- all tangent and polynomial constants are those of the new quartic certificate.
import Theorems.Thm_ThreeSum1960614_quartic_geometry
import Theorems.Thm_ThreeSum1960614_tangent_log_bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
open ThreeSum1960614 Set

private theorem entropy_tangent {u t : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    entropy t ≤ (-Real.log (1 - u) + (Real.log (1 - u) - Real.log u) * t) / Real.log 2 := by
  run_tac do
    dbg_trace "generic tangent starts"
  have hu : u ∈ Icc (0 : ℝ) 1 := ⟨hu0.le, hu1.le⟩
  have hd := Real.hasDerivAt_binEntropy (p := u) hu0.ne' (ne_of_lt hu1)
  have hconc := Real.strictConcave_binEntropy.concaveOn
  have htan : Real.binEntropy t ≤ Real.binEntropy u +
      (t - u) * (Real.log (1 - u) - Real.log u) := by
    rcases lt_trichotomy t u with h | h | h
    · have hs := hconc.le_slope_of_hasDerivAt ht hu h hd
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
      nlinarith only [hs]
    · subst t
      simp
    · have hs := hconc.slope_le_of_hasDerivAt hu ht h hd
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
      nlinarith only [hs]
  run_tac do
    dbg_trace "generic tangent slope complete"
  have heq : Real.binEntropy u + (t - u) * (Real.log (1 - u) - Real.log u) =
      -Real.log (1 - u) + (Real.log (1 - u) - Real.log u) * t := by
    simp only [Real.binEntropy, Real.log_inv]
    ring
  run_tac do
    dbg_trace "generic tangent formula complete"
  rw [heq] at htan
  exact div_le_div_of_nonneg_right htan (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem solution (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    entropy t < rho * (1 + phi t) := by
  run_tac do
    dbg_trace "uniform proof starts"
  let A : ℝ := -Real.log (1 - tangentPoint) / Real.log 2
  let B : ℝ := (Real.log (1 - tangentPoint) - Real.log tangentPoint) / Real.log 2
  obtain ⟨hl, hr⟩ := ThreeSum1960614.tangent_log_bounds
  have hA : A < (272298515211 / 1000000000000 : ℝ) := hl
  have hAB : A + B / 2 < (140590616299 / 100000000000 : ℝ) := by
    convert hr using 1 <;> dsimp [A, B] <;> ring
  run_tac do
    dbg_trace "tangent-log conversion complete"
  have hleft : (272298515211 / 1000000000000 : ℝ) <
      rho * (1 + phi tangentPoint - tangentPoint * phiDeriv tangentPoint) := by
    norm_num [rho, phi, phiDeriv, tangentPoint]
  run_tac do
    dbg_trace "left rational endpoint complete"
  have hright : (140590616299 / 100000000000 : ℝ) <
      rho * (1 + phi tangentPoint + (1 / 2 - tangentPoint) * phiDeriv tangentPoint) := by
    norm_num [rho, phi, phiDeriv, tangentPoint]
  run_tac do
    dbg_trace "right rational endpoint complete"
  have hl' := hA.trans hleft
  have hr' := hAB.trans hright
  have hline : A + B * t <
      rho * (1 + phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint) := by
    by_cases hhalf : t < 1 / 2
    · have hp := mul_lt_mul_of_pos_left hl' (by linarith : 0 < 1 - 2 * t)
      have hq := mul_le_mul_of_nonneg_left hr'.le (by linarith [ht.1] : 0 ≤ 2 * t)
      have hsum := add_lt_add_of_lt_of_le hp hq
      convert hsum using 1 <;> ring
    · have heq : t = 1 / 2 := by linarith [ht.2]
      rw [heq]
      simpa [div_eq_mul_inv] using hr'
  run_tac do
    dbg_trace "affine interpolation complete"
  have htan := (ThreeSum1960614.quartic_geometry t ht).2.2
  have hpoly := mul_le_mul_of_nonneg_left (add_le_add_left htan 1)
    (by norm_num [rho] : 0 ≤ rho)
  have hpoly' : rho * (1 + phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint) ≤
      rho * (1 + phi t) := by
    convert hpoly using 1 <;> ring
  run_tac do
    dbg_trace "polynomial bound complete"
  have hent : entropy t ≤ A + B * t := by
    have he := entropy_tangent (u := tangentPoint) (by norm_num [tangentPoint])
      (by norm_num [tangentPoint]) ⟨ht.1, by linarith [ht.2]⟩
    convert he using 1 <;> dsimp [A, B] <;> ring
  run_tac do
    dbg_trace "entropy tangent complete"
  exact lt_of_le_of_lt hent (lt_of_lt_of_le hline hpoly')
