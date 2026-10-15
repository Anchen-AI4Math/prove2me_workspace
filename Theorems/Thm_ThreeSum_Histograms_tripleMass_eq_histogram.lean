import Definitions.Def_ThreeSum1962Source_Bundle01
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
import Theorems.Thm_ThreeSum_Histograms_correlation_histograms


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2 u_3 u_4

theorem ThreeSum.Histograms.tripleMass_eq_histogram : ∀ {ι : Type u_1} {τ : Type u_2} {ν : Type u_3} {G : Type u_4} [inst : AddCommGroup.{u_4} G] [inst_1 : Fintype.{u_4} G]
  [inst_2 : DecidableEq.{u_4 + 1} G] (A : Finset.{u_1} ι) (B : Finset.{u_2} τ) (C : Finset.{u_3} ν) (a : ι → G)
  (b : τ → G) (c : ν → G) (wa : ι → Nat) (wb : τ → Nat) (wc : ν → Nat),
  @Eq.{1} Nat (@ThreeSum.Histograms.tripleMass.{u_1, u_2, u_3, u_4} ι τ ν G inst inst_2 A B C a b c wa wb wc)
    (∑ i ∈ A,
      @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (wa i)
        (@ThreeSum.Balancing.correlation.{u_4} G inst inst_1
          (@ThreeSum.Histograms.histogram.{u_3, u_4} ν G inst_2 C c wc)
          (@ThreeSum.Histograms.histogram.{u_2, u_4} τ G inst_2 B b wb) (a i))) := by
  sorry

