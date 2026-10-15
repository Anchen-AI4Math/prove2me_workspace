import Definitions.Def_ThreeSum1960614_Analysis

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
def a : ℝ := 1-2*ratio0
def A : ℝ := 1/2-k0-ratio0
def C : ℝ := a*e0-A
def lowerTarget : ℝ := 196061349120/100000000000



end ThreeSum1960614.FixedModel
