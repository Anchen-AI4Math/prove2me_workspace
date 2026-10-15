import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log
import Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false


theorem ThreeSum.BinarySearch.locate_sound : ∀ (lo hi : Nat → Int) (n : Nat) (x : Int)
  (hsorted :
    ∀ (i j : Nat),
      @LE.le.{0} Nat instLENat i j → @LT.lt.{0} Nat instLTNat j n → @LE.le.{0} Int Int.instLEInt (lo i) (lo j))
  {i : Nat} (h : @Eq.{1} (Option.{0} Nat) (ThreeSum.BinarySearch.locate lo hi n x) (@Option.some.{0} Nat i)),
  And (@LT.lt.{0} Nat instLTNat i n)
    (And (@LE.le.{0} Int Int.instLEInt (lo i) x) (@LE.le.{0} Int Int.instLEInt x (hi i))) := by
  sorry

