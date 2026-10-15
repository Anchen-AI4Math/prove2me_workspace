import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false


theorem ThreeSum.Arithmetic.small_lift_exists : ∀ {P a b c : Int} (hP : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) P)
  (ha0 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) a)
  (haP : @LT.lt.{0} Int Int.instLTInt a P)
  (hb0 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) b)
  (hbP : @LT.lt.{0} Int Int.instLTInt b P)
  (hc0 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) c)
  (hcP : @LT.lt.{0} Int Int.instLTInt c P)
  (hdiv :
    @Dvd.dvd.{0} Int Int.instDvd P
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) c b) a)),
  ∃ (j : Int),
    And (ThreeSum.Arithmetic.SmallLift j)
      (@Eq.{1} Int (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) c b)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) a
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) j P))) := by
  sorry

