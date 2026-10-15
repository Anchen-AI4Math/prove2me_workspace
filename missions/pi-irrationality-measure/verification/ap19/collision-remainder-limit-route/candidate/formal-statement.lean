theorem OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow {M : ℝ → ℕ} {d : ℕ} {L : ℝ}
    (hM : Tendsto (fun H : ℝ => (M H : ℝ) / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H => Collision.collisionRemainder (M H) H) atTop (𝓝 0) := by
  sorry
