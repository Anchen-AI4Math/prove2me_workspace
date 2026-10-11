import Definitions.Def_ZetaNine_CoefficientMapPartialFractions


set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapReflection

open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity CoefficientMapPartialFractions

def reflectionVariable (n : ℕ) : ℚ[X] := -X - C (n : ℚ)

def rho (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n j s W

def StrongProperMultiplier (n : ℕ) (W : ℚ[X]) : Prop :=
  2 * n + 2 * W.natDegree ≤ 9 * (n + 1) - 2

def partialBasis (n j s : ℕ) : ℚ[X] :=
  clearedPolePolynomial n j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)

end ZetaNine.CoefficientMapReflection
