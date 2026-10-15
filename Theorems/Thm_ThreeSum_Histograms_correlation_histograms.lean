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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2 u_4

theorem ThreeSum.Histograms.correlation_histograms : ∀ {ι : Type u_1} {τ : Type u_2} {G : Type u_4} [inst : AddCommGroup.{u_4} G] [inst_1 : Fintype.{u_4} G]
  [inst_2 : DecidableEq.{u_4 + 1} G] (I : Finset.{u_1} ι) (J : Finset.{u_2} τ) (left : ι → G) (right : τ → G)
  (weightL : ι → Nat) (weightR : τ → Nat) (d : G),
  @Eq.{1} Nat
    (@ThreeSum.Balancing.correlation.{u_4} G inst inst_1
      (@ThreeSum.Histograms.histogram.{u_2, u_4} τ G inst_2 J right weightR)
      (@ThreeSum.Histograms.histogram.{u_1, u_4} ι G inst_2 I left weightL) d)
    (@ThreeSum.Histograms.pairMass.{u_1, u_2, u_4} ι τ G inst inst_2 I J left right weightL weightR d) := by
  sorry

