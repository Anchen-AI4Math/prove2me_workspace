import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_Bands
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

namespace ThreeSum.Bands
end ThreeSum.Bands
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands
end ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands

variable {I J K : Type*}
theorem ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.tripleOwner_injective
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    (hA : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated alo ahi) (hB : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated blo bhi) (hC : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated clo chi)
    {p q : I × (J × K)} (hp : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Relevant alo ahi blo bhi clo chi p)
    (hq : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Relevant alo ahi blo bhi clo chi q)
    (heq : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.tripleOwner alo blo bhi clo p = _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.tripleOwner alo blo bhi clo q) : p = q := by sorry
