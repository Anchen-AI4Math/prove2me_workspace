import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI
namespace PiExponent
open Filter Topology

theorem determinant_bounds_inconsistent
    (nu theta x b ear ean err collision d : ℝ)
    (hnu : 1 < nu) (hb0 : 0 ≤ b) (hb : b ≤ theta)
    (hgap : ear + ean + err < nu * (x - theta) - (1 - theta))
    (hcollision : 1 + ear + ean + err < collision)
    (hlower : -(1 - b) - ear ≤ d)
    (hupper : d ≤ ean + err + max (-collision) (-nu * (x - b))) : False := by
  sorry

end PiExponent
end OAI
