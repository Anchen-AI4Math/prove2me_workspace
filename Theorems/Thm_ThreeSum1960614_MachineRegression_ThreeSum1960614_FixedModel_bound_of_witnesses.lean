import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_MachineRegression_Submission_ThreeSum_FixedModelAlgebra
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Analysis.Calculus.MeanValue
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

namespace ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel
end ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
open _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel


theorem ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.bound_of_witnesses (e b S th terminal ratio R : ℝ)
    (hmodel : _root_.ThreeSum1960614.ModelFeasible 232 e b S th terminal ratio R)
    (hE : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.e0 ≤ _root_.ThreeSum1960614.E 232) (hk : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0 ≤ _root_.ThreeSum1960614.kappa 232) (hrho : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0 ≤ ratio)
    (hgamma : th ≤ _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split → _root_.ThreeSum1960614.gamma 232 th ≤ _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.gammaCap)
    (hentropy : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split ≤ th → _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.entropyFloor ≤ _root_.ThreeSum1960614.entropy th) : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.lowerTarget < R := by sorry
