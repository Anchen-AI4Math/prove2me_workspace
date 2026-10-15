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
import Theorems.Thm_ThreeSum_BinarySearch_locate_sound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandEnumeration.Family
end ThreeSum.BandEnumeration.Family


theorem ThreeSum.BandEnumeration.Family.lookup_sound : ∀ (A : ThreeSum.BandEnumeration.Family) (x : Int) (i : A.Index)
  (h : @Eq.{1} (Option.{0} A.Index) (A.lookup x) (@Option.some.{0} A.Index i)),
  And (@LE.le.{0} Int Int.instLEInt (A.lo i) x) (@LE.le.{0} Int Int.instLEInt x (A.hi i)) := by
  sorry

