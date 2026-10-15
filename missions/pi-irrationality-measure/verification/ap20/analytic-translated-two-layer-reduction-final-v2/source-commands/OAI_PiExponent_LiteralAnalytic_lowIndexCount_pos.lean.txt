theorem lowIndexCount_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < lowIndexCount d H := by
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 0, ?_⟩
  apply (mem_realWeightedSimplex (fixedWeights_pos d)).mpr
  simp only [Nat.cast_zero, mul_zero, Finset.sum_const_zero]
  exact mul_nonneg d.base.A_pos.le hH.le