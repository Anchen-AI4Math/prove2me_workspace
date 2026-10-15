theorem actual_minor_analytic_bound {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      d.analyticError + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) := by
  have hQ : (0 : ℝ) < translationTermCount d.m d.v0 H := by
    unfold translationTermCount
    positivity
  have hc : (Fintype.card (ChoiceFamily d H) : ℝ) ≤
      (translationTermCount d.m d.v0 H : ℝ) ^ actualRowCount d H := by
    exact_mod_cast card_choiceFamily_le d H
  have hb := DeterminantAnalyticBound.log_norm_sum_le
    (fun f : ChoiceFamily d H => (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det)
    (actualMinor d H selection).det (actualRowCount_pos d hH) hH hQ hc
    (actual_minor_expansion d selection) hne (norm_actual_summand_le d hnu hH selection)
  convert! hb using 1
  unfold analyticRemainder
  ring