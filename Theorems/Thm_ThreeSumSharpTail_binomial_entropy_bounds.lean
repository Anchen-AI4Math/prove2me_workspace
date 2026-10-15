import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators


theorem ThreeSumSharpTail.binomial_entropy_bounds (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ r) :
    Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r)) / (r + 1) ≤ (Nat.choose r k : ℝ) ∧
    (Nat.choose r k : ℝ) ≤ Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r)) := by sorry
