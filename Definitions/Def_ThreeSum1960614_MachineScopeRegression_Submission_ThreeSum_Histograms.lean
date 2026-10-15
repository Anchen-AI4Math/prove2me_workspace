import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_Balancing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Finset
end Finset
namespace ThreeSum.Histograms
end ThreeSum.Histograms
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms
end ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms

namespace ThreeSum1960614.MachineScopeRegression

/-!
# Exact histogram and correlation counts

All weights are natural multiplicities.  In particular, raw A incidences and
repeated selected-map occurrences need not be deduplicated to use these
identities. The common offset is chosen from the actual key histograms.
-/

namespace ThreeSum.Histograms

open _root_.Finset
open scoped _root_.BigOperators

variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) (k : G) : ℕ :=
  ∑ i ∈ I, if key i = k then weight i else 0



def pairMass (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G)
    (weightL : ι → ℕ) (weightR : τ → ℕ) (d : G) : ℕ :=
  ∑ i ∈ I, ∑ j ∈ J, if right j - left i = d then weightL i * weightR j else 0











end ThreeSum.Histograms

end ThreeSum1960614.MachineScopeRegression
