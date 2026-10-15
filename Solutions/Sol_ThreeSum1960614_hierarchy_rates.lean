import Submission.ThreeSum.HierarchyScales

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum.Parameters ThreeSum.Scales ThreeSum.CostLedger ThreeSum.HierarchyScales Filter
open scoped Topology

theorem solution :
    (∀ d : ℝ, 0 < d → ∀ᶠ n : ℕ in atTop,
      (queryTerms n 0 : ℝ) ≤ (n : ℝ)^(epsilon*entropy initialTheta+d)) ∧
    Tendsto (fun n : ℕ => Real.log (bandCount n : ℝ)/Real.log n) atTop
      (𝓝 (1-epsilon*(E+bandShift))) := by
  exact ⟨fun _ hd => initial_query_eventually_le hd,bandCount_log_rate⟩

#print axioms solution
