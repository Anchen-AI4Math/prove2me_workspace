import missions.zeta9.formalization.PNTTransfer

set_option autoImplicit false
open Filter ZetaNine.HarmonicStability

namespace ZetaNine.AdvancedAudit
theorem checked_psi_rate :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := psi_pnt_rate

theorem checked_harmonic_rate (s : ℕ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N) / (N : ℝ))
      atTop (nhds (s : ℝ)) := harmonic_log_den_rate s hs

theorem checked_perturbed_harmonic_rate (s : ℕ) (hs : 0 < s) (r : ℕ → ℚ)
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N + r N) / (N : ℝ))
      atTop (nhds (s : ℝ)) := harmonic_perturbed_log_den_rate s hs r hr

theorem checked_nine_double_harmonic_rate :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18) := harmonic_nine_double_log_den_rate

#print axioms MediumPNT
#print axioms psi_pnt_rate
#print axioms theta_pnt
#print axioms lcm_pnt
#print axioms harmonic_log_den_rate
#print axioms harmonic_perturbed_log_den_rate
#print axioms harmonic_nine_double_log_den_rate
#print axioms checked_psi_rate
#print axioms checked_harmonic_rate
#print axioms checked_perturbed_harmonic_rate
#print axioms checked_nine_double_harmonic_rate
end ZetaNine.AdvancedAudit
