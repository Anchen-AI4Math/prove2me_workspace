import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData


namespace OAI.PiExponent.Collision

open scoped BigOperators

noncomputable def collisionRatio : ℝ := Real.exp (-Real.log 2 / 2)

end OAI.PiExponent.Collision

namespace OAI.PiExponent.Collision

open scoped BigOperators

noncomputable def collisionRemainder (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log M + Real.log 2 / 4 - Real.log (1 - collisionRatio)) / H

end OAI.PiExponent.Collision

namespace OAI.PiExponent

open Filter Topology

noncomputable def translationTermCount (m : ℕ) (v H : ℝ) : ℕ :=
  (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1)

end OAI.PiExponent

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators Topology
open Filter
open DeterminantContradiction

noncomputable def analyticRemainder {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  Collision.collisionRemainder (actualRowCount d H) H +
    Real.log (translationTermCount d.m d.v0 H : ℝ) / H

end OAI.PiExponent.LiteralAnalytic
