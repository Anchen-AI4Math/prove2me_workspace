import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false


theorem ThreeSum.BinarySearch.upperSearch_correct : ∀ (f : Nat → Int) (x : Int) (n fuel lo hi : Nat)
  (hsorted :
    ∀ (i j : Nat),
      @LE.le.{0} Nat instLENat i j → @LT.lt.{0} Nat instLTNat j n → @LE.le.{0} Int Int.instLEInt (f i) (f j))
  (hlo : @LE.le.{0} Nat instLENat lo hi) (hhi : @LE.le.{0} Nat instLENat hi n)
  (hwidth :
    @LT.lt.{0} Nat instLTNat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) hi lo)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) fuel))
  (hlower : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i lo → @LE.le.{0} Int Int.instLEInt (f i) x)
  (hupper :
    ∀ (i : Nat), @LE.le.{0} Nat instLENat hi i → @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Int Int.instLTInt x (f i)),
  ThreeSum.BinarySearch.Partition f x n (ThreeSum.BinarySearch.upperSearch f x fuel lo hi) := by
  sorry

