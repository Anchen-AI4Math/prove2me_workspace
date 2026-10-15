theorem norm_choiceMatrix_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) * (∑ A : Transverse d H,
        (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
  have horders : ((∑ r : Row d H, (r.2.1 0 - ((f r).2.2 : ℕ)) : ℕ) : ℝ) ≤
      (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ r : Row d H, H / (d.v0 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        exact le_trans (by exact_mod_cast Nat.sub_le (r.2.1 0) ((f r).2.2 : ℕ)) (rowOrder_le d r)
      _ = _ := by simp; ring_nf
  have hb := formal_period_collision_bound (fun r => (f r).1) (fun A : Transverse d H => A.1)
    (fun r => r.1.val) (fun r => r.2.1 0 - ((f r).2.2 : ℕ))
    (fun c => (selection c).1 0) (fun c i => (selection c).1 i.succ) (fixedWeights d)
    (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) hH d.w0_pos d.wstar_pos (fixedWeights_lower d)
    (fun r => r.1.isLt)
    (fun c => InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c)) horders
  convert! hb using 1