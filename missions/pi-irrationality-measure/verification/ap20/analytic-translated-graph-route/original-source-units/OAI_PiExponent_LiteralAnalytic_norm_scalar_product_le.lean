theorem norm_scalar_product_le {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (f : ChoiceFamily d H) :
    ‖∏ r, choiceScalar d r (f r)‖ ≤ Real.exp
      (-nu * ((∑ r, indexWeight d (f r).1) - (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by
  rw [norm_prod]
  apply (Finset.prod_le_prod₀ (fun r _ => norm_nonneg _) (fun r _ => norm_choiceScalar_le d hnu r (f r))).trans
  rw [← Real.exp_sum]
  apply le_of_eq
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_rowWeight_eq d hH]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
  ring_nf