theorem rowWeight_le_indexWeight_of_ne_zero {nu : ℝ} (d : FixedData nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) (ht : choiceScalar d r t ≠ 0) :
    rowWeight d r ≤ indexWeight d t.1 := by
  have h := RowTranslation.rowScalar_ne_zero_le _ _ _ _ _ _ ht
  unfold rowWeight indexWeight MatrixTranslationBounds.weight
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by exact_mod_cast h i)
    (fixedWeights_pos d i).le