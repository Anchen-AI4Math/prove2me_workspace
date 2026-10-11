import OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction

namespace OAI.PiExponent

noncomputable section
open Filter Topology DeterminantContradiction

/-- Sample cofinal interpolation heights and their nonzero minors to obtain the
scalar sequence interface used by the campaign's current open leaf. -/
theorem determinant_sequences_of_fixed_data
    (hgeometry : GlobalInterpolationStatement) (hanalytic : AnalyticAggregateStatement)
    (nu : ℝ) (hnu : 2 < nu) (data : FixedData nu) :
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
  classical
  obtain ⟨error, herror, hupper⟩ := hanalytic nu hnu data
  choose H hH hsurj using fun n : ℕ => hgeometry nu hnu data ((n : ℝ) + 1)
  have hgrowth : Tendsto H atTop atTop := by
    apply tendsto_atTop.mpr
    intro bound
    refine eventually_atTop.mpr ⟨Nat.ceil bound, fun n hn => ?_⟩
    have hcast : bound ≤ (n : ℝ) := (Nat.le_ceil bound).trans (by exact_mod_cast hn)
    linarith [hH n]
  have hpositive (n : ℕ) : 0 < H n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hH n]
  choose selection hinjective hdet using fun n : ℕ =>
    InterpolationMatrix.exists_full_row_minor_of_surjective (actualMatrix data (H n))
      (hsurj n)
  have hminor (n : ℕ) : (actualMinor data (H n) (selection n)).det ≠ 0 := hdet n
  refine ⟨(data.base.theta : ℝ), (data.base.A : ℝ) * (1 - data.base.eta),
    data.arithmeticError, data.analyticError, DeterminantContradiction.collisionLimit data,
    (fun n => actualMean data (H n)),
    (fun n => Real.log ‖(actualMinor data (H n) (selection n)).det‖ /
      ((actualRowCount data (H n) : ℝ) * H n)),
    (fun n => error (H n)), (fun n => collisionRate data (H n)),
    data.error_sum_lt_gap, data.collision_exceeds_error_sum,
    herror.comp hgrowth, (tendsto_collisionRate data).comp hgrowth, ?_, ?_, ?_, ?_⟩
  · exact Eventually.of_forall fun n => (actualMean_bounds data (H n) (hpositive n)).1
  · exact Eventually.of_forall fun n => (actualMean_bounds data (H n) (hpositive n)).2
  · exact Eventually.of_forall fun n =>
      actual_minor_arithmetic_lower_bound data (H n) (hpositive n) (selection n) (hminor n)
  · filter_upwards [hgrowth.eventually hupper] with n hn
    exact hn (selection n) (hminor n)

end
end OAI.PiExponent
