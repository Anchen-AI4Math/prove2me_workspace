import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.PrimeChain.sum_scores_le : ∀ {ι : Type u_1} (T : Finset.{u_1} ι) (difference : ι → Int) (weight : Int → Nat)
  (hzero :
    @Eq.{1} Nat (weight (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (C : Finset.{0} Nat) (q K : Nat)
  (hdivisors :
    ∀ (i : ι),
      @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) T i →
        @Ne.{1} Int (difference i) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @LE.le.{0} Nat instLENat
            (@Finset.card.{0} Nat ({p ∈ C | @Dvd.dvd.{0} Nat Nat.instDvd p (difference i).natAbs})) K),
  @LE.le.{0} Nat instLENat
    (∑ p ∈ C,
      @ThreeSum.PrimeChain.score.{u_1} ι T difference weight
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q p))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) K
      (@ThreeSum.PrimeChain.score.{u_1} ι T difference weight q)) := by
  sorry

