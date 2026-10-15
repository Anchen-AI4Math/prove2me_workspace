import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_BinarySearch_locate_complete


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandEnumeration.Family
end ThreeSum.BandEnumeration.Family


theorem ThreeSum.BandEnumeration.candidate_owner : ∀ (A B C : ThreeSum.BandEnumeration.Family) (t : ThreeSum.BandEnumeration.Triple A B C)
  (ht : ThreeSum.BandEnumeration.relevant A B C t),
  @Eq.{1} (Option.{0} (ThreeSum.BandEnumeration.Triple A B C))
    (ThreeSum.BandEnumeration.candidate A B C (ThreeSum.BandEnumeration.owner A B C t))
    (@Option.some.{0} (ThreeSum.BandEnumeration.Triple A B C) t) := by
  sorry

