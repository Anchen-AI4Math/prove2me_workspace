import Definitions.Def_ZetaNine_CoefficientMapPartialFractions
import Definitions.Def_ZetaNine_HarmonicStability
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFiniteSum

open scoped BigOperators
open Finset Polynomial
open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions

def rho (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n j s W

def constantTerm (n : ℕ) (W : ℚ[X]) : ℚ :=
  -(∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    CoefficientMapJet.weightedLocalCoefficient n j s W * harmonicPower s j)

def finiteL (n T : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ t ∈ Icc 1 T, CoefficientMap.weightedR n W (t : ℚ)

def shiftedTail (n T : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    CoefficientMapJet.weightedLocalCoefficient n j s W *
      (harmonicPower s (T + j) - harmonicPower s T)

end ZetaNine.CoefficientMapFiniteSum
