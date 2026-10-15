theorem tendsto_collisionRemainder_of_normalized_pow {M : ℝ → ℕ} {d : ℕ} {L : ℝ}
    (hM : Tendsto (fun H : ℝ => (M H : ℝ) / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H => Collision.collisionRemainder (M H) H) atTop (𝓝 0) := by
  convert tendsto_log_add_div_of_normalized_pow hM hL
    (Real.log 2 / 4 - Real.log (1 - Collision.collisionRatio)) using 1
  funext H
  unfold Collision.collisionRemainder
  congr 1
  ring