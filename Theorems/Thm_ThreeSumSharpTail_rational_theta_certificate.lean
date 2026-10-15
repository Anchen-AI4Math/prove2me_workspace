import Definitions.Def_ThreeSumSharpTail_Analysis
set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSumSharpTail

theorem ThreeSumSharpTail.rational_theta_certificate (c : ℕ) (θ : ℝ) (a s : ℚ)
    (hc : 10 < c) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (henc : (a : ℝ) * (encodingExponent c + sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - queryExponent θ) :
    ∃ η : ℚ, 0 < (η : ℝ) ∧ (η : ℝ) < 9 / 10 ∧
      (a : ℝ) * (encodingExponent c + sharpSaving c (η : ℝ)) < 1 ∧
      (s : ℝ) < sharpSaving c (η : ℝ) ∧
      (s : ℝ) < 1 / 2 - queryExponent (η : ℝ) := by sorry
