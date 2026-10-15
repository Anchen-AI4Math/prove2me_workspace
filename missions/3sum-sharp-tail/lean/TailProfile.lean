import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace ThreeSumSharpTail

lemma entropy_eq_binEntropy (x : ℝ) : entropy x = Real.binEntropy x := by
  unfold entropy Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

noncomputable def tailProfile (c u : ℝ) : ℝ :=
  c * Real.binEntropy ((1 - u) / c) + u * Real.log 9

lemma tailProfile_continuous (c : ℝ) : Continuous (tailProfile c) := by
  unfold tailProfile
  fun_prop

lemma tailProfile_hasDerivAt {c u : ℝ} (hc : 10 < c) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (tailProfile c)
      (c * ((Real.log (1 - (1 - u) / c) - Real.log ((1 - u) / c)) * (-1 / c)) + Real.log 9) u := by
  have hcpos : 0 < c := by linarith
  have hp : 0 < (1 - u) / c := div_pos (by linarith) hcpos
  have hp1 : (1 - u) / c < 1 := by
    rw [div_lt_one hcpos]
    linarith
  have hlin : HasDerivAt (fun v : ℝ => (1 - v) / c) (-1 / c) u := by
    simpa using ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).div_const c
  have hbin := (Real.hasDerivAt_binEntropy hp.ne' hp1.ne).comp u hlin
  unfold tailProfile
  convert (hbin.const_mul c).add ((hasDerivAt_id u).mul_const (Real.log 9)) using 1 <;>
    (first | ext v <;> dsimp <;> field_simp <;> ring | field_simp <;> ring)

/-- The entropy plus `log 9` profile is antitone on the full parameter interval. -/
theorem tail_profile_antitone (c : ℝ) (hc : 10 < c) :
    AntitoneOn (fun u => c * entropy ((1 - u) / c) + u * Real.log 9) (Icc 0 1) := by
  have hEq : (fun u => c * entropy ((1 - u) / c) + u * Real.log 9) = tailProfile c := by
    funext u
    simp [tailProfile, entropy_eq_binEntropy]
  rw [hEq]
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · exact (tailProfile_continuous c).continuousOn
  · intro u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hu
    obtain ⟨hu0, hu1⟩ := hu'
    exact (tailProfile_hasDerivAt hc hu0 hu1).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hu
    obtain ⟨hu0, hu1⟩ := hu'
    have hF := tailProfile_hasDerivAt hc hu0 hu1
    rw [hF.deriv]
    let p : ℝ := (1 - u) / c
    have hp : 0 < p := by dsimp [p]; positivity
    have hq : 0 < 1 - p := by
      dsimp [p]
      have hcpos : 0 < c := by linarith
      have hlt : (1 - u) / c < 1 := by rw [div_lt_one hcpos]; linarith
      linarith
    have hsmall : 9 * p < 1 - p := by
      dsimp [p]
      have hcpos : 0 < c := by linarith
      have hnum : 9 * (1 - u) < c - 1 + u := by nlinarith [hc, hu0]
      have hscaled : 9 * (1 - u) / c < (c - 1 + u) / c :=
        (div_lt_div_iff₀ hcpos hcpos).2 (by nlinarith)
      have hqeq : 1 - (1 - u) / c = (c - 1 + u) / c := by field_simp; ring
      rw [hqeq]
      convert hscaled using 1 <;> ring
    have hlog : Real.log (9 * p) < Real.log (1 - p) := Real.log_lt_log (by positivity) hsmall
    have hderiv : c * ((Real.log (1 - p) - Real.log p) * (-1 / c)) + Real.log 9 =
        Real.log (9 * p) - Real.log (1 - p) := by
      have hcne : c ≠ 0 := ne_of_gt (by linarith : 0 < c)
      rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) hp.ne']
      dsimp [p]
      field_simp
      ring
    rw [hderiv]
    linarith

end ThreeSumSharpTail
