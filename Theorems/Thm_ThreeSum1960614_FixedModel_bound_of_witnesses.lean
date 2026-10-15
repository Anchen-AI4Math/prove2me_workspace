import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_FixedModelAlgebra
import Definitions.Def_ThreeSum1960614_ModelWitnessPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

open ThreeSum1960614 ThreeSum1960614.FixedModel


theorem ThreeSum1960614.FixedModel.bound_of_witnesses (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R)
    (hE : e0 ≤ E 232) (hk : k0 ≤ kappa 232) (hrho : ratio0 ≤ ratio)
    (hgamma : th ≤ split → gamma 232 th ≤ gammaCap)
    (hentropy : split ≤ th → entropyFloor ≤ entropy th) : lowerTarget < R := by sorry
