import Definitions.Def_ZetaNine_CoefficientMapMatrix
import Theorems.Thm_ZetaNine_CoefficientMapKernelBridge_inverseMultiplier_actual_HasSum_and_absolute

/-! Pure uncompiled SOURCE for a substantive existing Matrix-node decomposition.
The child is the general actual five-output inverse HasSum theorem.
The proof specializes the genuine selected row, not the parent theorem itself. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Matrix Topology
open Finset Polynomial Filter

namespace ZetaNine.GraphBridge.MatrixGraph
open CoefficientMapMatrix CoefficientMapKernelBridge

theorem selected_prescribedL_exact (b a : ℤ) :
    prescribedL (selectedIntegerOutput b a) =
      (b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9 := by
  norm_num [prescribedL, selectedIntegerOutput, Fin.ext_iff]

end ZetaNine.GraphBridge.MatrixGraph

namespace ZetaNine.CoefficientMapMatrix

theorem selectedIntegerMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ))
        ((b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖) := by
  simpa only [selectedIntegerMultiplier, GraphBridge.MatrixGraph.selected_prescribedL_exact] using
    CoefficientMapKernelBridge.inverseMultiplier_actual_HasSum_and_absolute
      n hn2 hn (selectedIntegerOutput b a)

end ZetaNine.CoefficientMapMatrix
