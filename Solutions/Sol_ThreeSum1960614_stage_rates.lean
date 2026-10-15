import Submission.ThreeSum.StageBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum.Parameters ThreeSum.StageBounds ThreeSum.MassScales
  ThreeSum.Scales ThreeSum.TrimScales
open Filter
open scoped Topology

/-- The six concrete work counts, conditional on the explicit finite mass inequalities. -/
theorem solution {W H P H1 : ℕ → ℕ} {r : ℝ} (C k : ℕ)
    (hcost : ∀ t ∈ ThreeSum1960614.costs, t < r)
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    ∀ᶠ n : ℕ in atTop, (amplifiedCoreWork C W H n : ℝ) ≤ (n : ℝ)^r := by
  exact amplifiedCoreWork_eventually_at C k (by simpa only [actual_costLedger_eq] using hcost)
    hW hscore hinit hmod

#print axioms solution
#print axioms all_costs_lt_certificate
#print axioms table_powerBound
#print axioms encoder_powerBound
#print axioms boxes_powerBound
#print axioms initial_powerBound
#print axioms active_powerBound
#print axioms terminal_powerBound
