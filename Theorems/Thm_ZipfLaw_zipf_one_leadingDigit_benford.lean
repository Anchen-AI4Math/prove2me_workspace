import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipf_one_leadingDigit_benford (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ (Finset.Icc 1 N).filter (fun k => leadingDigit k = d), zipfPMF N 1 k)
      Filter.atTop (nhds (Real.logb 10 (1 + 1 / (d : ℝ)))) := by sorry

end ZipfLaw
