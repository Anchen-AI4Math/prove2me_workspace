import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false


theorem ThreeSum.BoxStages.partialZeta_eq_boxSum : ∀ {L : Nat} (weight : Finset.{0} (Fin L) → Int) (flags processed : Finset.{0} (Fin L)),
  @Eq.{1} Int (@ThreeSum.Subset.partialZeta.{0} (Fin L) (instDecidableEqFin L) processed weight flags)
    (@ThreeSum.SparseBoxes.boxSum.{0} (Fin L) (@Fin.instLinearOrder L) flags
      (@Inter.inter.{0} (Finset.{0} (Fin L)) (@Finset.instInter.{0} (Fin L) (instDecidableEqFin L)) flags processed)
      weight) := by
  sorry

