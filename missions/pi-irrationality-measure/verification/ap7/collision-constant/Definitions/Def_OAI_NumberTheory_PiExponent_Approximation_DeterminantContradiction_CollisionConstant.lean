import Mathlib

namespace OAI

open Filter
open scoped Topology

namespace PiExponent.DeterminantContradiction

noncomputable def collisionConstant : ℝ := Real.log 2 / 4

theorem collisionConstant_pos : 0 < collisionConstant := by
  unfold collisionConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

end PiExponent.DeterminantContradiction

end OAI
