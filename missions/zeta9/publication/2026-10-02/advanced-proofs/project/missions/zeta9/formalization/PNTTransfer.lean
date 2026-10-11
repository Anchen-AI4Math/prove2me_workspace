import missions.zeta9.formalization.HarmonicAsymptotic
import PrimeNumberTheoremAnd.MediumPNT
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Transfer the actual Chebyshev psi rate to the two harmonic PNT inputs

The existing `ThetaPNT` and `LcmPNT` objects are imported, not redefined.
The transfer theorems identify the actual limit of `Chebyshev.psi x / x`
with the two needed inputs. The unconditional endpoints then derive that
limit from the imported, fully proved original `MediumPNT` theorem and
the decay of its explicit relative exponential error. No PNT axiom or
harmonic denominator-rate premise is introduced.
-/

set_option autoImplicit false
open Filter Asymptotics

namespace ZetaNine.HarmonicStability

/-- The actual Chebyshev difference is negligible after division by x.
This uses Mathlib's proved O(sqrt x) error, and has no PNT premise. -/
theorem psi_theta_normalized_error_tendsto_zero :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt x / x) atTop (nhds 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hsqrt_small : IsLittleO atTop Real.sqrt (fun x : ℝ => x) :=
    (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr hsqrt
  simpa only [Pi.sub_apply] using
    (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt_small).tendsto_div_nhds_zero

/-- The actual psi PNT rate implies the existing theta PNT input. -/
theorem theta_pnt_of_psi_rate
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)) :
    ThetaPNT := by
  unfold ThetaPNT
  have h := hψ.sub psi_theta_normalized_error_tendsto_zero
  simp only [sub_zero] at h
  convert h using 1
  funext x
  ring

/-- Restricting the actual psi rate to natural endpoints yields the lcm
input by the exact Mathlib identity psi(N)=log(lcmUpto N). -/
theorem lcm_pnt_of_psi_rate
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)) :
    LcmPNT := by
  unfold LcmPNT
  simpa only [Function.comp_def, Chebyshev.psi_eq_log_lcmUpto] using
    hψ.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The two original inputs are both consequences of one genuine psi rate,
without assuming the lcm input or the harmonic denominator rate. -/
theorem harmonic_pnt_inputs_of_psi_rate
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)) :
    ThetaPNT ∧ LcmPNT :=
  ⟨theta_pnt_of_psi_rate hψ, lcm_pnt_of_psi_rate hψ⟩

/-- The actual harmonic denominator baseline requires only the actual psi
prime-distribution theorem; its denominator growth is derived. -/
theorem harmonic_log_den_rate_of_psi_rate (s : ℕ) (hs : 0 < s)
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N) / (N : ℝ))
      atTop (nhds (s : ℝ)) :=
  harmonic_log_den_rate_of_pnt s hs (theta_pnt_of_psi_rate hψ) (lcm_pnt_of_psi_rate hψ)

/-- The original double-endpoint order-nine rate, derived from psi alone. -/
theorem harmonic_nine_double_log_den_rate_of_psi_rate
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)) :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18) :=
  harmonic_nine_double_log_den_rate_of_pnt (theta_pnt_of_psi_rate hψ) (lcm_pnt_of_psi_rate hψ)

/-- The explicit relative exponential error in the original MediumPNT
theorem tends to zero. Every analytic limit here is proved. -/
theorem medium_pnt_relative_error_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 10)).comp Real.tendsto_log_atTop
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.const_mul_atTop hc)

/-- Convert the actual MediumPNT error estimate to the literal psi PNT
rate. This auxiliary implication introduces no substitute psi function. -/
theorem psi_rate_of_medium_error (c : ℝ) (hc : 0 < c)
    (herror : IsBigO atTop (Chebyshev.psi - id)
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := by
  have hweight : Tendsto (fun x : ℝ =>
      (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) / x) atTop (nhds 0) := by
    apply (medium_pnt_relative_error_tendsto_zero c hc).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp
  have hsmall : IsLittleO atTop
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      (fun x : ℝ => x) :=
    (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr hweight
  have hnormalized : Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x)
      atTop (nhds 0) := by
    simpa only [Pi.sub_apply, id_eq] using
      (herror.trans_isLittleO hsmall).tendsto_div_nhds_zero
  have hrate := hnormalized.add_const (1 : ℝ)
  simp only [zero_add] at hrate
  apply hrate.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

/-- The actual psi prime-number-theorem rate, derived from the genuine
imported MediumPNT proof and its proved error decay, with no hypotheses. -/
theorem psi_pnt_rate :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := by
  obtain ⟨c, hc, herror⟩ := MediumPNT
  exact psi_rate_of_medium_error c hc herror

theorem theta_pnt : ThetaPNT := theta_pnt_of_psi_rate psi_pnt_rate

theorem lcm_pnt : LcmPNT := lcm_pnt_of_psi_rate psi_pnt_rate

/-- The original full-sequence harmonic denominator baseline is now
unconditional for every fixed positive order. -/
theorem harmonic_log_den_rate (s : ℕ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N) / (N : ℝ))
      atTop (nhds (s : ℝ)) :=
  harmonic_log_den_rate_of_psi_rate s hs psi_pnt_rate

/-- The original rational perturbation corollary, with only its genuine
sublinear perturbation-denominator hypothesis. -/
theorem harmonic_perturbed_log_den_rate (s : ℕ) (hs : 0 < s) (r : ℕ → ℚ)
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N + r N) / (N : ℝ))
      atTop (nhds (s : ℝ)) :=
  harmonic_perturbed_log_den_rate_of_pnt s hs theta_pnt lcm_pnt r hr

/-- The exact order-nine rate eighteen at double natural endpoints. -/
theorem harmonic_nine_double_log_den_rate :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18) :=
  harmonic_nine_double_log_den_rate_of_psi_rate psi_pnt_rate

#print axioms psi_theta_normalized_error_tendsto_zero
#print axioms theta_pnt_of_psi_rate
#print axioms lcm_pnt_of_psi_rate
#print axioms harmonic_pnt_inputs_of_psi_rate
#print axioms harmonic_log_den_rate_of_psi_rate
#print axioms harmonic_nine_double_log_den_rate_of_psi_rate
#print axioms MediumPNT
#print axioms psi_pnt_rate
#print axioms theta_pnt
#print axioms lcm_pnt
#print axioms harmonic_log_den_rate
#print axioms harmonic_perturbed_log_den_rate
#print axioms harmonic_nine_double_log_den_rate

end ZetaNine.HarmonicStability
