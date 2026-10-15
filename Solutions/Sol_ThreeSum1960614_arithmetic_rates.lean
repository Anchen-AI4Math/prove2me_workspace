import Submission.ThreeSum.ArithmeticStageBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum.Parameters ThreeSum.ArithmeticStageBounds

theorem solution {r : ℚ} (hr : 0 ≤ r) (C k : ℕ)
    (hcost : ∀ t ∈ ThreeSum1960614.costs, t < (r : ℝ)) :
    EndStatement.BigO (combinedBudget C k) r := by
  exact combined_endStatementBigO_at hr C k
    (by simpa only [actual_costLedger_eq] using hcost)

#print axioms solution
#print axioms arithmetic_powerBound
#print axioms offset_powerBound
#print axioms normalization_powerBound
