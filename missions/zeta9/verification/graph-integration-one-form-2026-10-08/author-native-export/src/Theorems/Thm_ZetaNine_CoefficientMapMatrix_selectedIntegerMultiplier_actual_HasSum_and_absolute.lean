import Definitions.Def_ZetaNine_CoefficientMapMatrix

set_option autoImplicit false
open scoped BigOperators Matrix
open Polynomial ZetaNine ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapKernelBridge

theorem ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ))
        ((b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖):= by sorry
