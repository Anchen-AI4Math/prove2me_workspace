import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ThreeSumSharpTail

noncomputable def entropy (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

noncomputable def oldSaving (c θ : ℝ) : ℝ :=
  θ * Real.log ((c - 1) / 9) / Real.log 4

noncomputable def sharpSaving (c θ : ℝ) : ℝ :=
  (c * entropy (1 / c) - c * entropy ((1 - θ) / c) - θ * Real.log 9) / Real.log 4

noncomputable def queryExponent (θ : ℝ) : ℝ :=
  (entropy θ + θ * Real.log 9) / Real.log 4

noncomputable def encodingExponent (c : ℝ) : ℝ :=
  (c * Real.log 10 - c * entropy (1 / c) / 2 - (c - 1) * Real.log 3) / Real.log 4

def boxCount (c m d : ℕ) : ℕ :=
  Nat.choose (c * m) (m - d) * 9 ^ (c * m - m + d)

end ThreeSumSharpTail
