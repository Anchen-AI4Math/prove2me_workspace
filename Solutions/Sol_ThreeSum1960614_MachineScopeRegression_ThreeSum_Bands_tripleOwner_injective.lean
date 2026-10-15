import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_Bands
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

namespace ThreeSum.Bands
end ThreeSum.Bands
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands
end ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands

namespace ThreeSum1960614.MachineScopeRegression

/-!
# The quadratic cardinal bound for relevant sorted-band triples

The proof is an explicit injection.  A relevant A interval either contains
the lower endpoint of a B/C difference interval, or its own lower endpoint
cuts that rectangle.  For a fixed cut, interval intersections inject into
the endpoints of the two families.

This file proves the combinatorial output bound and solution coverage.
It does not assign that bound to a cubic filtering implementation.
-/

namespace ThreeSum.Bands

variable {I J K : Type*}



theorem interval_unique {lo hi : I → ℤ} (hs : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated lo hi)
    {i j : I} {x : ℤ} (hi0 : lo i ≤ x) (hi1 : x ≤ hi i)
    (hj0 : lo j ≤ x) (hj1 : x ≤ hi j) : i = j := by
  by_contra hne
  rcases hs i j hne with h | h <;> omega

theorem separated_shift {lo hi : I → ℤ} (hs : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated lo hi) (t : ℤ) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated (fun i => t + lo i) (fun i => t + hi i) := by
  intro i j hne
  change t + hi i < t + lo j ∨ t + hi j < t + lo i
  rcases hs i j hne with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)







theorem overlapOwner_injective {alo ahi : I → ℤ} {blo bhi : J → ℤ}
    (hA : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated alo ahi) (hB : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated blo bhi)
    {p q : I × J} (hp : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Overlap alo ahi blo bhi p) (hq : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Overlap alo ahi blo bhi q)
    (heq : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.overlapOwner alo blo p = _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.overlapOwner alo blo q) : p = q := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  unfold _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.overlapOwner at heq
  dsimp only at heq
  change alo i ≤ bhi j ∧ blo j ≤ ahi i at hp
  change alo k ≤ bhi l ∧ blo l ≤ ahi k at hq
  by_cases h : alo i ≤ blo j
  · by_cases h' : alo k ≤ blo l
    · simp only [if_pos h, if_pos h'] at heq
      have hj : j = l := Sum.inr.inj heq
      subst l
      have hi : i = k := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.interval_unique hA h hp.2 h' hq.2
      subst k
      rfl
    · simp [h, h'] at heq
  · by_cases h' : alo k ≤ blo l
    · simp [h, h'] at heq
    · simp only [if_neg h, if_neg h'] at heq
      have hi : i = k := Sum.inl.inj heq
      subst k
      have hj : j = l := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.interval_unique hB (by omega) hp.1 (by omega) hq.1
      subst l
      rfl















end ThreeSum.Bands

end ThreeSum1960614.MachineScopeRegression

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands

variable {I J K : Type*}
theorem solution
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    (hA : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated alo ahi) (hB : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated blo bhi) (hC : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Separated clo chi)
    {p q : I × (J × K)} (hp : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Relevant alo ahi blo bhi clo chi p)
    (hq : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Relevant alo ahi blo bhi clo chi q)
    (heq : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.tripleOwner alo blo bhi clo p = _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.tripleOwner alo blo bhi clo q) : p = q := by
  rcases p with ⟨i, j, k⟩
  rcases q with ⟨i', j', k'⟩
  change alo i ≤ chi k - blo j ∧ clo k - bhi j ≤ ahi i at hp
  change alo i' ≤ chi k' - blo j' ∧ clo k' - bhi j' ≤ ahi i' at hq
  unfold _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.tripleOwner at heq
  dsimp only at heq
  by_cases h : alo i < clo k - bhi j
  · by_cases h' : alo i' < clo k' - bhi j'
    · simp only [if_pos h, if_pos h'] at heq
      have hjk : (j, k) = (j', k') := Sum.inl.inj heq
      have hj := congrArg Prod.fst hjk
      have hk := congrArg Prod.snd hjk
      dsimp only at hj hk
      subst j'
      subst k'
      have hi : i = i' := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.interval_unique hA (by omega) hp.2 (by omega) hq.2
      subst i'
      rfl
    · simp [h, h'] at heq
  · by_cases h' : alo i' < clo k' - bhi j'
    · simp [h, h'] at heq
    · simp only [if_neg h, if_neg h'] at heq
      have he := Sum.inr.inj heq
      have hi := congrArg Prod.fst he
      dsimp only at hi
      subst i'
      have ho := congrArg Prod.snd he
      dsimp only at ho
      have hOverlap : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Overlap (fun j => alo i + blo j) (fun j => alo i + bhi j) clo chi (j, k) := by
        constructor <;> dsimp only <;> omega
      have hOverlap' : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Overlap (fun j => alo i + blo j) (fun j => alo i + bhi j) clo chi (j', k') := by
        constructor <;> dsimp only <;> omega
      have hjk := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.overlapOwner_injective (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.separated_shift hB (alo i)) hC hOverlap hOverlap' ho
      cases hjk
      rfl

#print axioms solution
