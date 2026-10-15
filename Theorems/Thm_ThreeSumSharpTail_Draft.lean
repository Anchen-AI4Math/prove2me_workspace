import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
theorem ThreeSumSharpTail.binomial_entropy_bounds (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ r) :
    Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r)) / (r + 1) ≤ (Nat.choose r k : ℝ) ∧
    (Nat.choose r k : ℝ) ≤ Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r)) := by sorry

theorem ThreeSumSharpTail.sharp_normalized_tail (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    ((∑ d ∈ Finset.Icc (⌈θ * (m : ℝ)⌉₊) m, ThreeSumSharpTail.boxCount c m d : ℕ) : ℝ) /
        (ThreeSumSharpTail.boxCount c m 0 : ℝ) ≤
      ((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
        Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ) := by sorry

theorem ThreeSumSharpTail.sharp_saving_strict (c θ : ℝ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    0 < ThreeSumSharpTail.oldSaving c θ ∧
    ThreeSumSharpTail.oldSaving c θ < ThreeSumSharpTail.sharpSaving c θ := by sorry

theorem ThreeSumSharpTail.admissible_parameters_solve_3sum
    (c : ℕ) (θ : ℝ) (a s r : ℚ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (henc : (a : ℝ) * (ThreeSumSharpTail.encodingExponent c + ThreeSumSharpTail.sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < ThreeSumSharpTail.sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent θ)
    (hprime : Real.log 7 / Real.log 2 + 3 * (a : ℝ) / 2 < 3 - (a : ℝ) * s / 2)
    (hbuild : 2 + (a : ℝ) * (1 + (s : ℝ) / 2) < 3 - (a : ℝ) * s / 2)
    (hr : 2 - a * s / 4 < r) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry

theorem ThreeSumSharpTail.explicit_parameter_certificate :
    (0.05665 : ℝ) * (ThreeSumSharpTail.encodingExponent 21 + ThreeSumSharpTail.sharpSaving 21 0.11202) < 1 ∧
    (0.06945 : ℝ) < ThreeSumSharpTail.sharpSaving 21 0.11202 ∧
    (0.06945 : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent 0.11202 ∧
    Real.log 7 / Real.log 2 + 3 * (0.05665 : ℝ) / 2 < 3 - 0.05665 * 0.06945 / 2 ∧
    2 + (0.05665 : ℝ) * (1 + 0.06945 / 2) < 3 - 0.05665 * 0.06945 / 2 ∧
    (2 - (0.05665 : ℚ) * 0.06945 / 4) = 1.999016414375 ∧
    (1.999017 : ℚ) - (2 - 0.05665 * 0.06945 / 4) = 0.000000585625 := by sorry

theorem ThreeSumSharpTail.threeSum_1999017 :
    EndStatement.ThreeSum.SolvedInTime 1.999017 := by sorry
