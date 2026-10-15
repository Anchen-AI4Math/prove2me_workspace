import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_Balancing
import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_Histograms
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

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms

open _root_.Finset
open scoped _root_.BigOperators
variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.selected_pairMass_bound [Inhabited G]
    (keys : List G) (hkeys : ∀ d, d ∈ keys)
    (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G)
    (weightL : ι → ℕ) (weightR : τ → ℕ) :
    Fintype.card G * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.pairMass I J left right weightL weightR
      (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.chooseOffset keys (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram J right weightR) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram I left weightL)) ≤
        (∑ i ∈ I, weightL i) * (∑ j ∈ J, weightR j) := by sorry
