import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PiIrrationality

/-- The epsilon formulation of an upper bound on the irrationality measure of pi.
The threshold may depend on the positive epsilon, but is uniform in p and q. -/
def UpperBound (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ Q : ℕ,
      ∀ (p : ℤ) (q : ℕ), 0 < q → Q ≤ q →
        1 / (q : ℝ) ^ (B + ε) <
          |Real.pi - (p : ℝ) / (q : ℝ)|

end PiIrrationality
