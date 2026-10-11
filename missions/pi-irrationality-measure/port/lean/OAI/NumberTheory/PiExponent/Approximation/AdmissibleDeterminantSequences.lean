import OAI.NumberTheory.PiExponent.Approximation.DeterminantSequences
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixGeometry
import OAI.NumberTheory.PiExponent.Analysis.AnalyticAggregate

namespace OAI.PiExponent

open Filter Topology DeterminantContradiction

/-- The exact scalar sequence obligation currently open in the bound-two campaign.
Its witnesses come from interpolation minors, rather than from the eventual-bound
theorem, so the proof does not depend on the platform node which consumes it. -/
theorem pi_approximation_determinant_sequences
    (nu : ℝ) (hnu : 2 < nu)
    (hbad : ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ),
      Q ≤ q ∧ |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu)) :
    ∃ theta x ear ean collisionLimit : ℝ,
      ∃ b d err collision : ℕ → ℝ,
        ear + ean < nu * (x - theta) - (1 - theta) ∧
        1 + ear + ean < collisionLimit ∧
        Tendsto err atTop (𝓝 0) ∧
        Tendsto collision atTop (𝓝 collisionLimit) ∧
        (∀ᶠ n in atTop, 0 ≤ b n) ∧
        (∀ᶠ n in atTop, b n ≤ theta) ∧
        (∀ᶠ n in atTop, -(1 - b n) - ear ≤ d n) ∧
        (∀ᶠ n in atTop,
          d n ≤ ean + err n + max (-collision n) (-nu * (x - b n))) := by
  obtain ⟨data⟩ := exists_admissible_parameters nu Arithmetic.lcmConstant collisionConstant
    hnu Arithmetic.lcmConstant_pos collisionConstant_pos hbad
  exact determinant_sequences_of_fixed_data AdmissibleMatrixInterpolation.globalInterpolation
    LiteralAnalytic.analyticAggregate nu hnu data

end OAI.PiExponent
