theorem card_choiceFamily_le {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Fintype.card (ChoiceFamily d H) ≤ translationTermCount d.m d.v0 H ^ actualRowCount d H := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _r : Row d H, translationTermCount d.m d.v0 H := by
      apply Finset.prod_le_prod'
      intro r _
      exact MatrixTranslation.row_term_count (fixedWeights d) H d.v0
        (fun i => by change 1 ≤ MatrixArithmetic.logWeights (finiteDenominators d) i
                     rw [logWeights_eq]; exact d.x_one_le _)
        (beta d r) (r.2.1 0) (rowOrder_le d r)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, actualRowCount]