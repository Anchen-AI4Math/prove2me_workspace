import Mathlib
import Definitions.Def_ZetaNine_CoefficientMap
import Definitions.Def_ZetaNine_AnalyticPhase
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine

namespace ZetaNine.AnalyticMomentBounds

def actualMomentTerm (n r k : ℕ) : ℝ :=
  (CoefficientMap.actualR n (k : ℚ) : ℝ) *
    ((k : ℝ) * ((k : ℝ) + (n : ℝ))) ^ r

def actualMomentSequence (n r m : ℕ) : ℝ := actualMomentTerm n r (m + 1)

def actualMoment (n r : ℕ) : ℝ := ∑' m : ℕ, actualMomentSequence n r m

def tailPower (n r : ℕ) : ℕ := 7 * n + 9 - 2 * r

def tailCoefficient (n r : ℕ) : ℝ :=
  (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n * (3 / 2 : ℝ) ^ r

end ZetaNine.AnalyticMomentBounds

namespace ZetaNine.AnalyticUniformMomentBound
open AnalyticMomentBounds

def tailWeightConstant (r : ℕ) : ℝ :=
  (9 / 7 : ℝ) * (3 / 2 : ℝ) ^ r / (2 : ℝ) ^ (9 - 2 * r)

def tailMajorant (n r : ℕ) : ℝ :=
  tailCoefficient n r / (2 * (n : ℝ)) ^ tailPower n r * (9 / 7 : ℝ) /
    (n : ℝ) ^ (2 * r)

def tailExponent : ℝ := 7 + 6 * Real.log 2

def momentBoundConstant : ℝ := 5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7

end ZetaNine.AnalyticUniformMomentBound

namespace ZetaNine.AnalyticWeightedBound
open AnalyticMomentBounds AnalyticUniformMomentBound

def actualWeightedSequence (n : ℕ) (W : ℚ[X]) (m : ℕ) : ℝ :=
  (CoefficientMap.weightedR n W ((m + 1 : ℕ) : ℚ) : ℝ)

def weightedCoefficientHeight (n : ℕ) (W : ℚ[X]) : ℝ :=
  ∑ r ∈ range 5, |(W.coeff r : ℝ)| * (n : ℝ) ^ (2 * r)

def analyticPrefactor (n : ℕ) : ℝ :=
  momentBoundConstant * ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n)

def uniformError (n : ℕ) : ℝ :=
  (Real.log momentBoundConstant + 10 * Real.log ((n : ℝ) + 1)) / (n : ℝ)

end ZetaNine.AnalyticWeightedBound
