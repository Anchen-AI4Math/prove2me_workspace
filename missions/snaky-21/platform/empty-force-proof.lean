import Theorems.Thm_OAI_Snaky21_certificate21_correct
open OAI.Snaky21 OAI.SnakyPrototype

theorem solution : CanForce 21 ∅ ∅ := by
  have hc := certificate21_correct
  have hf := hc.1.2.2 ∅ ∅ (by rw [hc.2.1.1]) (by simp)
  rw [hc.2.1.2.1] at hf
  exact hf
