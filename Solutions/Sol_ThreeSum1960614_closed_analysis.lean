import Closed3Sum.quartic_parameter_certificate
import Closed3Sum.integer_schedule
import Closed3Sum.local_cover_bounds
import Closed3Sum.executable_scale_limits

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem solution : ∀ z ∈ costs, z < (target : ℝ) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hc,ht⟩ := ThreeSum1960614.quartic_parameter_certificate
  intro z hz
  exact (hc z hz).trans ht

#print axioms ThreeSum1960614.quartic_parameter_certificate
#print axioms ThreeSum1960614.integer_schedule
#print axioms ThreeSum1960614.executable_scale_limits
#print axioms ThreeSum1960614.local_cover_bounds
#print axioms solution
