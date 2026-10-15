import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexFloor
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexUnweighted
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

namespace OAI

open Filter
open scoped Topology

namespace PiExponent.DeterminantContradiction

theorem tendsto_collisionRate_source017 {nu : ℝ} (d : FixedData nu) :
    Tendsto (collisionRate d) atTop (𝓝 (collisionLimit d)) := by
  sorry

end PiExponent.DeterminantContradiction

end OAI

