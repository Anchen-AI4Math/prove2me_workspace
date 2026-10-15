import Submission.ThreeSum.FixedModelAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614 ThreeSum1960614.FixedModel

theorem solution (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R)
    (hE : e0 ≤ E 232) (hk : k0 ≤ kappa 232) (hrho : ratio0 ≤ ratio)
    (hgamma : th ≤ split → gamma 232 th ≤ gammaCap)
    (hentropy : split ≤ th → entropyFloor ≤ entropy th) : lowerTarget < R :=
  bound_of_witnesses e b S th terminal ratio R hmodel hE hk hrho hgamma hentropy

#print axioms solution
