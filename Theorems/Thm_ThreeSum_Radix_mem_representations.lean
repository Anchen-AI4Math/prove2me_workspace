import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Radix_radix_divisibility


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Radix.mem_representations : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] [inst_1 : DecidableEq.{u_1 + 1} Ω] (p : Int)
  (hp : @Ne.{1} Int p (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (left right : Ω → Int) (j : Nat)
  (a b : Int) (xs : List.{u_1} Ω),
  Iff
    (@Membership.mem.{u_1, u_1} (List.{u_1} Ω) (Finset.{u_1} (List.{u_1} Ω))
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (List.{u_1} Ω)) (List.{u_1} Ω)
        (@Finset.instSetLike.{u_1} (List.{u_1} Ω)))
      (@ThreeSum.Radix.representations.{u_1} Ω inst inst_1 p left right j a b) xs)
    (And (@Eq.{1} Nat (@List.length.{u_1} Ω xs) j)
      (And
        (@Dvd.dvd.{0} Int Int.instDvd
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p j)
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a
            (@ThreeSum.Radix.positionalHash.{u_1} Ω p left xs)))
        (@Dvd.dvd.{0} Int Int.instDvd
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p j)
          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) b
            (@ThreeSum.Radix.positionalHash.{u_1} Ω p right xs))))) := by
  sorry

