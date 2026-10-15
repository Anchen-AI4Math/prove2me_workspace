import Submission.ThreeSum.RawCostExponent

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum.Parameters

theorem solution {r : ℝ} (hr : 0 < r)
    (hcost : ∀ t ∈ ThreeSum1960614.costs, t < r) :
    (∀ t ∈ ThreeSum1960614.costs, t ≤ rawCostExponent) ∧ rawCostExponent < r := by
  rw [← actual_costLedger_eq] at hcost ⊢
  exact ⟨all_costs_le_raw_exponent,raw_exponent_lt_of_costs_lt hr hcost⟩

#print axioms solution
