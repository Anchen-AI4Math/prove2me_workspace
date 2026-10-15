import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem zipf_genHarmonic_tendsto_zeta (s : ℝ) (hs : 1 < s) :
    Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
      (nhds (riemannZeta s)) := by sorry

end ZipfLaw
