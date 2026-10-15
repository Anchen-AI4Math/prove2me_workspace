theorem tendsto_log_add_div_of_normalized_pow {f : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ d) atTop (𝓝 L)) (hL : 0 < L) (C : ℝ) :
    Tendsto (fun H : ℝ => (Real.log (f H) + C) / H) atTop (𝓝 0) := by
  have h := (tendsto_log_div_of_normalized_pow hf hL).add
    (tendsto_id.const_div_atTop C)
  simpa only [add_zero, add_div, id_eq] using h