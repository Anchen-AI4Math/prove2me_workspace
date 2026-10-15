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

def oneHot [Zero K] [One K] (s : α → Bool) : α × Bool → K :=
  fun p => if s p.1 = p.2 then 1 else 0



section Relations

variable [Ring K]







end Relations

section LinearIndependence

variable [Field K]







end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]

/-- The linear map associated with any concrete list of hash coefficient
vectors. This is the ordinary row-by-weight product. -/
noncomputable def hashMap (v : ι → σ → K) : (σ → K) →ₗ[K] (ι → K) := by
  classical
  exact LinearMap.pi (fun i => dotProductEquiv K σ (v i))









end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]

/-- One independent weight for each coordinate/symbol pair. -/
def hashValue (w : α × Bool → K) (s : α → Bool) : K :=
  ∑ i, w (i, s i)





end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]



/-- The simultaneous prescribed hashes of a concrete word tuple. -/
def wordEvent {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K) :
    Finset (α × Bool → K) :=
  Finset.univ.filter (fun w => ∀ i, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue w (words i) = target i)







def pairEvent (s t : α → Bool) (a b : K) : Finset (α × Bool → K) :=
  Finset.univ.filter (fun w => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue w s = a ∧ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue w t = b)

















end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]

/-- Number of represented edges in one weight assignment. -/
def incidenceCount (events : E → Finset Ω) (w : Ω) : ℕ :=
  (Finset.univ.filter (fun e => w ∈ events e)).card









end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

def outputMask (left right : E → α → Bool) (e : E) : α → Bool :=
  fun i => left e i == right e i

def badPartners (left right : E → α → Bool) (e : E) : Finset E :=
  Finset.univ.filter (fun f => left e = left f ∨ right e = right f ∨
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.outputMask left right e = _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.outputMask left right f)











end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

def bucketSize (vertices : Finset (α → Bool)) (w : α × Bool → K) (target : K) : ℕ :=
  (vertices.filter (fun s => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue w s = target)).card













def trimmedPairEvent (s t : α → Bool) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool)) (B : ℕ) :
    Finset (α × Bool → K) :=
  (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent s t a b).filter (fun w =>
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.bucketSize leftVertices w a ≤ B ∧ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.bucketSize rightVertices w b ≤ B)





end SeparableTrimming

section TrimmedGraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





end TrimmedGraphMoments

end ThreeSum.HashFamily

end ThreeSum1960614.MachineScopeRegression
