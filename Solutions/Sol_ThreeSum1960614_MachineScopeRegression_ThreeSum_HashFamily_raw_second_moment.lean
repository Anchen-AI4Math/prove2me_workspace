import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_hashMap_surjective
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_jointPair_card_le_cube
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_linear_fiber_card
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_oneHot_four_independent
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_sum_incidenceCount_sq

namespace ThreeSum.HashFamily
end ThreeSum.HashFamily
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily
end ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

namespace ThreeSum1960614.MachineScopeRegression

/-!
# The actual one-hot hash family

This file develops the dependence classification of the binary one-hot hash
vectors used in the local cover. Hash weights are independent field elements
at coordinate/symbol pairs. The independence statements concern this concrete
family, not an assumed random oracle.
-/

namespace ThreeSum.HashFamily

open scoped _root_.BigOperators

variable {α K : Type*}



theorem exists_coordinate_ne {s t : α → Bool} (hst : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra h
  push Not at h
  exact hst (funext h)

section Relations

variable [Ring K]

/-- Two distinct one-hot words have no nontrivial linear relation. -/
theorem two_relation {s t : α → Bool} (hst : s ≠ t) {a b : K}
    (h : ∀ p, a * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot s p + b * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot t p = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨i, hi⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.exists_coordinate_ne hst
  have ha := h (i, s i)
  have hb := h (i, t i)
  simpa [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot, hi, Ne.symm hi] using And.intro ha hb





end Relations

section LinearIndependence

variable [Field K]

theorem oneHot_two_independent {s t : α → Bool} (hst : s ≠ t) :
    LinearIndependent K ![_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) s, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot t] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.two_relation hst (a := g 0) (b := g 1) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ] using hp)
  fin_cases i <;> simp_all





end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]









/-- The exact joint-output count for independent hash coefficient rows. -/
theorem hash_fiber_card [Fintype K] [DecidableEq K] [DecidableEq σ] [DecidableEq ι]
    {v : ι → σ → K}
    (hv : LinearIndependent K v) (target : ι → K) :
    Fintype.card K ^ Fintype.card ι *
        (Finset.univ.filter (fun w : σ → K => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap v w = target)).card =
      Fintype.card K ^ Fintype.card σ := by
  classical
  simpa using _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.linear_fiber_card (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap v) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap_surjective hv) target

end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]



theorem hashValue_eq_dotProduct (w : α × Bool → K) (s : α → Bool) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue w s = ∑ p, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) s p * w p := by
  classical
  simp [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot, Fintype.sum_prod_type]

theorem hashValue_family (v : ι → α → Bool) (w : α × Bool → K)
    [Fintype ι] :
    (fun i => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue w (v i)) = _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap (fun i => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) (v i)) w := by
  funext i
  exact _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue_eq_dotProduct w (v i)

end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





theorem wordEvent_eq_linear_fiber {r : ℕ}
    (words : Fin r → α → Bool) (target : Fin r → K) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent words target =
      Finset.univ.filter (fun w => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap (fun i => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) (words i)) w = target) := by
  ext w
  simp only [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue_family]
  exact funext_iff.symm

/-- Exact uniform joint count, instantiated with the actual one-hot family. -/
theorem wordEvent_card {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K)
    (hwords : LinearIndependent K (fun i => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) (words i))) :
    Fintype.card K ^ r * (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent words target).card =
      Fintype.card (α × Bool → K) := by
  rw [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent_eq_linear_fiber]
  simpa using _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hash_fiber_card hwords target





theorem pairEvent_eq (s t : α → Bool) (a b : K) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent s t a b = _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent ![s, t] ![a, b] := by
  ext w
  simp [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent, Fin.forall_fin_succ]



theorem pairEvent_card {s t : α → Bool} (hst : s ≠ t) (a b : K) :
    Fintype.card K ^ 2 * (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent s t a b).card =
      Fintype.card (α × Bool → K) := by
  rw [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent_eq]
  apply _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent_card
  convert _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot_two_independent (K := K) hst using 1
  funext i
  fin_cases i <;> rfl





theorem jointPair_card_four {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) (a b : K) :
    Fintype.card K ^ 4 * (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent s t a b ∩ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent u v a b).card =
      Fintype.card (α × Bool → K) := by
  have he : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent s t a b ∩ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent u v a b =
      _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent ![s, t, u, v] ![a, b, a, b] := by
    ext w
    simp [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent, Fin.forall_fin_succ, and_assoc]
  rw [he]
  apply _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent_card
  convert _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot_four_independent (K := K) hst hsu hsv htu htv huv hm using 1
  funext i
  fin_cases i <;> rfl





end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]











end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]









theorem joint_pair_charge (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f) (a b : K) (e f : E) :
    Fintype.card K ^ 4 *
        (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left e) (right e) a b ∩ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left f) (right f) a b).card ≤
      Fintype.card (α × Bool → K) *
        (1 + (if e = f then Fintype.card K ^ 2 else 0) +
          (if f ∈ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.badPartners left right e then Fintype.card K else 0)) := by
  by_cases hef : e = f
  · subst f
    have hc := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent_card (hcross e e) a b
    have heq : Fintype.card K ^ 4 * (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left e) (right e) a b).card =
        Fintype.card (α × Bool → K) * Fintype.card K ^ 2 := by
      calc
        _ = Fintype.card K ^ 2 *
            (Fintype.card K ^ 2 * (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left e) (right e) a b).card) := by ring
        _ = _ := by rw [hc]; ring
    simp only [Finset.inter_self, ite_true, heq]
    apply Nat.mul_le_mul_left
    omega
  · have hpair : (left e, right e) ≠ (left f, right f) := fun h => hef (hinj h)
    by_cases hbad : f ∈ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.badPartners left right e
    · have hc := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.jointPair_card_le_cube (hcross e e) (hcross e f)
        (Ne.symm (hcross f e)) (hcross f f) hpair a b
      calc
        _ = Fintype.card K * (Fintype.card K ^ 3 *
            (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left e) (right e) a b ∩ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left f) (right f) a b).card) := by ring
        _ ≤ Fintype.card K * Fintype.card (α × Bool → K) := Nat.mul_le_mul_left _ hc
        _ ≤ _ := by
          simp only [if_neg hef, if_pos hbad, add_zero]
          rw [Nat.mul_comm (Fintype.card K)]
          exact Nat.mul_le_mul_left _ (by omega)
    · have hn : left e ≠ left f ∧ right e ≠ right f ∧
          _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.outputMask left right e ≠ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.outputMask left right f := by
        simpa [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.badPartners, not_or] using hbad
      have hm : ∃ i, (left e i == right e i) ≠ (left f i == right f i) :=
        _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.exists_coordinate_ne hn.2.2
      have hc := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.jointPair_card_four (hcross e e) hn.1 (hcross e f)
        (Ne.symm (hcross f e)) hn.2.1 (hcross f f) hm a b
      simp only [if_neg hef, if_neg hbad, add_zero, mul_one, hc]
      rfl





end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





















end SeparableTrimming

section TrimmedGraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





end TrimmedGraphMoments

end ThreeSum.HashFamily

end ThreeSum1960614.MachineScopeRegression

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

open scoped _root_.BigOperators
variable {α K : Type*}
open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
/-- Full second moment, derived by counting the exceptional partner classes.
`B` bounds the number of shared-endpoint or same-output partners per edge;
the local graph instantiation takes `B = 2*Delta + G`. -/
theorem solution (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.badPartners left right e).card ≤ B) (a b : K) :
    Fintype.card K ^ 4 *
        (∑ w, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount (fun e => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left e) (right e) a b) w ^ 2) ≤
      Fintype.card (α × Bool → K) *
        (Fintype.card E * Fintype.card K ^ 2 + Fintype.card E ^ 2 +
          Fintype.card E * B * Fintype.card K) := by
  have hrow : ∀ e : E, (∑ f : E, Fintype.card K ^ 4 *
      (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left e) (right e) a b ∩ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left f) (right f) a b).card) ≤
      Fintype.card (α × Bool → K) * (Fintype.card E + Fintype.card K ^ 2 + B * Fintype.card K) := by
    intro e
    calc
      _ ≤ ∑ f : E, Fintype.card (α × Bool → K) *
          (1 + (if e = f then Fintype.card K ^ 2 else 0) +
            (if f ∈ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.badPartners left right e then Fintype.card K else 0)) :=
        Finset.sum_le_sum (fun f hf => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.joint_pair_charge left right hinj hcross a b e f)
      _ = Fintype.card (α × Bool → K) *
          (Fintype.card E + Fintype.card K ^ 2 + (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.badPartners left right e).card * Fintype.card K) := by
        rw [← Finset.mul_sum]
        congr 1
        simp [Finset.sum_add_distrib]
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hB e)) _
  calc
    _ = ∑ e : E, ∑ f : E, Fintype.card K ^ 4 *
        (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left e) (right e) a b ∩ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left f) (right f) a b).card := by
      rw [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.sum_incidenceCount_sq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.mul_sum ..
    _ ≤ ∑ _e : E, Fintype.card (α × Bool → K) *
        (Fintype.card E + Fintype.card K ^ 2 + B * Fintype.card K) :=
      Finset.sum_le_sum (fun e he => hrow e)
    _ = _ := by simp; ring

#print axioms solution
