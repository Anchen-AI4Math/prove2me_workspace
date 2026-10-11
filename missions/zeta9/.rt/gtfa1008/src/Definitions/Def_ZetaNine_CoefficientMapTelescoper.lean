import Definitions.Def_ZetaNine_CoefficientMapAggregate

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Finset Polynomial Filter

namespace ZetaNine.CoefficientMapTelescoper

open scoped BigOperators Topology
open Finset Polynomial Filter
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate

def prefixSum (c : ℕ → ℚ) (j : ℕ) : ℚ := ∑ i ∈ range (j + 1), c i

def cumulativeCoefficient (n j s : ℕ) (W : ℚ[X]) : ℚ :=
  prefixSum (fun i => weightedLocalCoefficient n i s W) j

def telescoper (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  ∑ j ∈ range n, ∑ s ∈ Icc 1 9, cumulativeCoefficient n j s W / (t + (j : ℚ)) ^ s

def telescoperNumerator (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range n, ∑ s ∈ Icc 1 9,
    C (cumulativeCoefficient n j s W) * partialBasis (n - 1) j s

def rootNode (n : ℕ) (i : Fin (n + 1) ⊕ Fin (n + 1)) : ℚ :=
  match i with
  | .inl k => (k.val : ℚ) + 1
  | .inr k => -(n : ℚ) - (k.val : ℚ)

def rootPolynomial (n : ℕ) : ℚ[X] :=
  ∏ i : Fin (n + 1) ⊕ Fin (n + 1), (X - C (rootNode n i))

end ZetaNine.CoefficientMapTelescoper
