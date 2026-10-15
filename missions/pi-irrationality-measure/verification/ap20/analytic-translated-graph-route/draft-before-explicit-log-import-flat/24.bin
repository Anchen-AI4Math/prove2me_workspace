theorem sum_rowWeight_eq {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H * actualMean d H := by
  have hM : (actualRowCount d H : ℝ) ≠ 0 := by exact_mod_cast (actualRowCount_pos d hH).ne'
  unfold actualMean MatrixArithmetic.meanRowWeight
  change (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H *
    (MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H /
      ((actualRowCount d H : ℝ) * H))
  rw [mul_div_cancel₀ _ (mul_ne_zero hM hH.ne')]
  unfold MatrixArithmetic.rowWeightedSum rowWeight MatrixTranslationBounds.weight beta fixedWeights
  simp only [InterpolationMatrix.exponentVector_apply, mul_comm]