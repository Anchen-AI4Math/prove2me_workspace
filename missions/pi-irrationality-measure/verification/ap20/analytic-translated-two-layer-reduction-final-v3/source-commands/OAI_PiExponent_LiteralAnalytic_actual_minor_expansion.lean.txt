theorem actual_minor_expansion {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det =
      ∑ f : ChoiceFamily d H, (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det := by
  classical
  have hp : ∀ r c : Row d H,
      (MatrixTranslation.periodMonomial r.1.val logarithmicPeriod
        ((selection c).1 0) (fun i => (selection c).1 i.succ)).support ⊆
        MatrixTranslation.transverseIndices (fixedWeights d) H := by
    intro r c
    apply MatrixTranslation.periodMonomial_support_subset _ _ _ _ _ _ (fixedWeights_pos d)
    have hc := InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c)
    have hz : 0 ≤ (d.w0 : ℝ) * ((selection c).1 0 : ℝ) :=
      mul_nonneg d.w0_pos.le (Nat.cast_nonneg _)
    linarith
  have he := MatrixTranslation.det_matrix_translation
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (fun r : Row d H => r.1.val) (fun r => r.2.1 0) logarithmicPeriod
    (fun r i => r.2.1 i.succ) (fun c => (selection c).1 0)
    (fun c i => (selection c).1 i.succ) (MatrixTranslation.transverseIndices (fixedWeights d) H) hp
  convert! he using 1