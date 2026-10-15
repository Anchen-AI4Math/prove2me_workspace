import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Theorems.Thm_ThreeSum1960614_uniform_entropy_bound

namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters

open _root_.Set
theorem ThreeSum1960614.Machine.ThreeSum.Parameters.switch_entropy_bound {a t mu : ℝ}
    (ha : a ∈ Icc (0 : ℝ) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction) (ht : t ∈ Icc (0 : ℝ) (1/2))
    (hmu : 0 < mu) (hswitch : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.phi t < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.switchThreshold a+9/((1-a)*mu)) :
    (1-a)*_root_.ThreeSum.Parameters.entropy t < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio*(1+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving-2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)+9*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio/mu := by sorry
