theorem actualRowCount_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < actualRowCount d H :=
  MatrixArithmetic.actual_row_card_pos (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) d.v0_pos d.base.theta_pos hH
    (fixedWeights_pos d)