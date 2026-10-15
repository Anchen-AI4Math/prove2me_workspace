theorem norm_actual_summand_le {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det‖ ≤
    Real.exp ((actualRowCount d H : ℝ) * H *
      (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  by_cases hs : (∏ r, choiceScalar d r (f r)) = 0
  · simp [hs, Real.exp_nonneg]
  have hmono : (actualRowCount d H : ℝ) * H * actualMean d H ≤ ∑ r, indexWeight d (f r).1 := by
    rw [← sum_rowWeight_eq d hH]
    apply Finset.sum_le_sum
    intro r _
    apply rowWeight_le_indexWeight_of_ne_zero d r (f r)
    exact Finset.prod_ne_zero_iff.mp hs r (Finset.mem_univ r)
  have hb := DeterminantAnalyticBound.translated_summand_bound
    (fun r => (f r).1) (fun A : Transverse d H => indexWeight d A)
    (∏ r, choiceScalar d r (f r)) (choiceMatrix d selection f).det
    hH d.base.A_pos.le d.base.eta_pos.le hnu collisionConstant_pos.le
    (by exact_mod_cast lowIndexCount_pos d hH)
    (indexWeight_nonneg d) hmono (low_transverse_capacity d H)
    (norm_scalar_product_le d hnu hH f) (norm_choiceMatrix_le d hH selection f)
  convert! hb using 1
  congr 1
  unfold AdmissibleParameters.analyticError collisionRate collisionConstant actualRowCount
  ring_nf