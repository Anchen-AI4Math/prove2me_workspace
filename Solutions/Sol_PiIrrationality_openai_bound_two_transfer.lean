import OAI.NumberTheory.PiExponent.Main
import Definitions.Def_PiIrrationality_UpperBound

-- Local integration target. The source import will be platformized only after
-- the complete source closure and its axioms have passed verification.
theorem solution : PiIrrationality.UpperBound (2 : ℝ) := by
  intro ε hε
  obtain ⟨Q, hQ, hLower⟩ :=
    OAI.PiExponent.pi_eventual_lower_bound (2 + ε / 2) (by linarith)
  refine ⟨Q, ?_⟩
  intro p q _hqpos hq
  have hqTwo : 2 ≤ q := hQ.trans hq
  have hqOne : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg q)]
  exact (Real.rpow_lt_rpow_of_exponent_lt hqOne
    (by linarith : -(2 + ε) < -(2 + ε / 2))).trans_le (hLower p q hq)

#print axioms solution
