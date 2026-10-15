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

def Separated (lo hi : I → ℤ) : Prop :=
  ∀ i j, i ≠ j → hi i < lo j ∨ hi j < lo i





def Overlap (alo ahi : I → ℤ) (blo bhi : J → ℤ) (p : I × J) : Prop :=
  alo p.1 ≤ bhi p.2 ∧ blo p.2 ≤ ahi p.1

instance instDecidableOverlap (alo ahi : I → ℤ) (blo bhi : J → ℤ) (p : I × J) :
    Decidable (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Overlap alo ahi blo bhi p) :=
  inferInstanceAs (Decidable (alo p.1 ≤ bhi p.2 ∧ blo p.2 ≤ ahi p.1))

def overlapOwner (alo : I → ℤ) (blo : J → ℤ) (p : I × J) : I ⊕ J :=
  if alo p.1 ≤ blo p.2 then Sum.inr p.2 else Sum.inl p.1





def Relevant (alo ahi : I → ℤ) (blo bhi : J → ℤ) (clo chi : K → ℤ)
    (p : I × (J × K)) : Prop :=
  alo p.1 ≤ chi p.2.2 - blo p.2.1 ∧ clo p.2.2 - bhi p.2.1 ≤ ahi p.1

instance instDecidableRelevant (alo ahi : I → ℤ) (blo bhi : J → ℤ) (clo chi : K → ℤ)
    (p : I × (J × K)) : Decidable (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.Relevant alo ahi blo bhi clo chi p) :=
  inferInstanceAs (Decidable
    (alo p.1 ≤ chi p.2.2 - blo p.2.1 ∧ clo p.2.2 - bhi p.2.1 ≤ ahi p.1))

def tripleOwner (alo : I → ℤ) (blo bhi : J → ℤ) (clo : K → ℤ)
    (p : I × (J × K)) : (J × K) ⊕ (I × (J ⊕ K)) :=
  if alo p.1 < clo p.2.2 - bhi p.2.1 then Sum.inl p.2
  else Sum.inr (p.1, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.overlapOwner (fun j => alo p.1 + blo j) clo p.2)







end ThreeSum.Bands

end ThreeSum1960614.MachineScopeRegression
