import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Analysis
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

namespace ThreeSum1960614.MachineRegression

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
namespace ThreeSum1960614.FixedModel

def e0 : ℝ := 4648781151243719/1000000000000000
def k0 : ℝ := 778993608289/500000000000000
def ratio0 : ℝ := 34881106835777/125000000000000
def split : ℝ := 252561863698173/6250000000000000
def gammaCap : ℝ := 318487605190926/1000000000000000
def entropyFloor : ℝ := 244168410993740/1000000000000000
def savingCap : ℝ := 193175572822/1000000000000
def a : ℝ := 1-2*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0
def A : ℝ := 1/2-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0
def C : ℝ := _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.e0-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A
def lowerTarget : ℝ := 196061349120/100000000000



end ThreeSum1960614.FixedModel

end

end ThreeSum1960614.MachineRegression
