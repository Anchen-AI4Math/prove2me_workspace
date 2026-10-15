import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false


theorem ThreeSum.SubsetAddress.layerRank_injective : ∀ {L k m n : Nat} (hm : ThreeSum.SubsetAddress.IsMask L k m) (hn : ThreeSum.SubsetAddress.IsMask L k n)
  (he : @Eq.{1} Nat (ThreeSum.SubsetAddress.layerRank L k m) (ThreeSum.SubsetAddress.layerRank L k n)), @Eq.{1} Nat m n := by
  sorry

