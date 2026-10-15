import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipfMandelbrotPMF_hasSum_one (q s : ℝ) (hq : 0 ≤ q) (hs : 1 < s) :
    HasSum (fun k : ℕ => zipfMandelbrotPMF q s k) 1 := by sorry

end ZipfLaw
