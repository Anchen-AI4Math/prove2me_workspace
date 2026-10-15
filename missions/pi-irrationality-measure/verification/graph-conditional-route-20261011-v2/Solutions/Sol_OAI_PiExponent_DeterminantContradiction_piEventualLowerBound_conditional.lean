import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_exists_admissible_parameters_source017
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_no_fixed_data_of_interpolation_and_analytic_aggregate

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    (hgeometry : GlobalInterpolationStatement) (hanalytic : AnalyticAggregateStatement) :
    PiEventualLowerBound := by
  intro nu hnu
  by_contra h
  push Not at h
  have hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
    intro Q
    obtain ⟨p, q, hq, herr⟩ := h (max Q 2) (le_max_right _ _)
    exact ⟨p, q, (le_max_left _ _).trans hq, herr.le⟩
  obtain ⟨d⟩ := OAI.PiExponent.exists_admissible_parameters_source017 nu Arithmetic.lcmConstant collisionConstant
    hnu Arithmetic.lcmConstant_pos collisionConstant_pos hbad
  exact no_fixed_data_of_interpolation_and_analytic_aggregate hgeometry hanalytic nu hnu d
