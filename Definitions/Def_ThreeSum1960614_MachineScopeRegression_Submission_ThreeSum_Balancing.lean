import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith

namespace Finset
end Finset
namespace ThreeSum.Balancing
end ThreeSum.Balancing
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing
end ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing

namespace ThreeSum1960614.MachineScopeRegression

/-! # An exact global offset chosen by a cyclic correlation -/

namespace ThreeSum.Balancing

open _root_.Finset
open scoped _root_.BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

def correlation (F H : G → ℕ) (d : G) : ℕ := ∑ k, F k * H (k - d)





/-- An actual finite minimum search, using the supplied order for ties. -/
def chooseOffset [Inhabited G] (keys : List G) (F H : G → ℕ) : G :=
  (keys.argmin (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation F H)).getD default





end ThreeSum.Balancing

end ThreeSum1960614.MachineScopeRegression
