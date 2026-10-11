import Solutions.Sol_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute
import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology Matrix
open Finset Polynomial Filter
namespace ZetaNine.HarmonicStability
open scoped BigOperators
/-- Natural logarithm of the reduced positive rational denominator. -/
noncomputable def independent_complete_value_001 (q : ℚ) : ℝ := Real.log (q.den : ℝ)
end ZetaNine.HarmonicStability


namespace ZetaNine.HarmonicStability
open scoped BigOperators
/-- The generalized harmonic rational number, including `N=0` and `s=0`. -/
def independent_complete_value_002 (s N : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℚ) ^ s
end ZetaNine.HarmonicStability


namespace ZetaNine.CoefficientMap
open scoped BigOperators
open Finset
open Polynomial
def independent_complete_value_003 (n : ℕ) (t : ℚ) : ℚ :=
  (n.factorial : ℚ) ^ 7 *
    (∏ i ∈ range n, (t - ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (t + n + ((i : ℚ) + 1)))
end ZetaNine.CoefficientMap


namespace ZetaNine.CoefficientMap
open scoped BigOperators
open Finset
open Polynomial
def independent_complete_value_004 (n : ℕ) (t : ℚ) : ℚ :=
  ∏ k ∈ range (n + 1), (t + k)
end ZetaNine.CoefficientMap


namespace ZetaNine.CoefficientMap
open scoped BigOperators
open Finset
open Polynomial
def independent_complete_value_005 (n : ℕ) (t : ℚ) : ℚ := numerator n t / poleProduct n t ^ 9
end ZetaNine.CoefficientMap


namespace ZetaNine.CoefficientMap
open scoped BigOperators
open Finset
open Polynomial
def independent_complete_value_006 (n j : ℕ) (t : ℚ) : ℚ :=
  ∏ k ∈ (range (n + 1)).erase j, (t + k)
end ZetaNine.CoefficientMap


namespace ZetaNine.CoefficientMap
open scoped BigOperators
open Finset
open Polynomial
def independent_complete_value_007 (n j : ℕ) (t : ℚ) : ℚ :=
  numerator n t / clearedPoleProduct n j t ^ 9
end ZetaNine.CoefficientMap


namespace ZetaNine.CoefficientMap
open scoped BigOperators
open Finset
open Polynomial
def independent_complete_value_008 (n j : ℕ) : ℚ := clearedR n j (-(j : ℚ))
end ZetaNine.CoefficientMap


namespace ZetaNine.CoefficientMap
open scoped BigOperators
open Finset
open Polynomial
def independent_complete_value_009 (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  actualR n t * W.eval (t * (t + n))
end ZetaNine.CoefficientMap


namespace ZetaNine.CoefficientMap
open scoped BigOperators
open Finset
open Polynomial
def independent_complete_value_010 (n j : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  clearedR n j t * W.eval (t * (t + n))
end ZetaNine.CoefficientMap


namespace ZetaNine.CoefficientMap
open scoped BigOperators
open Finset
open Polynomial
def independent_complete_value_011 (n j : ℕ) (W : ℚ[X]) : ℚ :=
  clearedWeightedR n j W (-(j : ℚ))
end ZetaNine.CoefficientMap


namespace ZetaNine.CoefficientMapAggregate
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
def independent_complete_value_012 (n : ℕ) (W : ℚ[X]) (i : Fin 5) : ℚ :=
  match i.val with
  | 0 => CoefficientMapFiniteSum.constantTerm n W
  | 1 => CoefficientMapFiniteSum.rho n 3 W
  | 2 => CoefficientMapFiniteSum.rho n 5 W
  | 3 => CoefficientMapFiniteSum.rho n 7 W
  | _ => CoefficientMapFiniteSum.rho n 9 W
end ZetaNine.CoefficientMapAggregate


namespace ZetaNine.CoefficientMapAggregate
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
def independent_complete_value_013 (a : Fin 5 → ℚ) : ℚ[X] :=
  ∑ i : Fin 5, C (a i) * X ^ i.val
end ZetaNine.CoefficientMapAggregate


namespace ZetaNine.CoefficientMapAggregate
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
def independent_complete_value_014 (W : ℚ[X]) (i : Fin 5) : ℚ := W.coeff i.val
end ZetaNine.CoefficientMapAggregate


namespace ZetaNine.CoefficientMapAggregate
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
def independent_complete_value_015 (n : ℕ) : ℚ[X] →ₗ[ℚ] (Fin 5 → ℚ) where
  toFun := aggregate n
  map_add' := aggregate_add n
  map_smul' := aggregate_smul n
end ZetaNine.CoefficientMapAggregate


namespace ZetaNine.CoefficientMapAggregate
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
def independent_complete_value_016 : (Fin 5 → ℚ) →ₗ[ℚ] ℚ[X] where
  toFun := coordinatePolynomial
  map_add' := coordinatePolynomial_add
  map_smul' := coordinatePolynomial_smul
end ZetaNine.CoefficientMapAggregate


namespace ZetaNine.CoefficientMapAggregate
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
def independent_complete_value_017 (n : ℕ) : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) :=
  (aggregateLinearMap n).comp coordinateLinearMap
end ZetaNine.CoefficientMapAggregate


namespace ZetaNine.CoefficientMapFiniteSum
open scoped BigOperators
open Finset Polynomial
open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions
def independent_complete_value_018 (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n j s W
end ZetaNine.CoefficientMapFiniteSum


namespace ZetaNine.CoefficientMapFiniteSum
open scoped BigOperators
open Finset Polynomial
open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions
def independent_complete_value_019 (n : ℕ) (W : ℚ[X]) : ℚ :=
  -(∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    CoefficientMapJet.weightedLocalCoefficient n j s W * harmonicPower s j)
end ZetaNine.CoefficientMapFiniteSum


namespace ZetaNine.CoefficientMapFiniteSum
open scoped BigOperators
open Finset Polynomial
open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions
def independent_complete_value_020 (n T : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ t ∈ Icc 1 T, CoefficientMap.weightedR n W (t : ℚ)
end ZetaNine.CoefficientMapFiniteSum


namespace ZetaNine.CoefficientMapFiniteSum
open scoped BigOperators
open Finset Polynomial
open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions
def independent_complete_value_021 (n T : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    CoefficientMapJet.weightedLocalCoefficient n j s W *
      (harmonicPower s (T + j) - harmonicPower s T)
end ZetaNine.CoefficientMapFiniteSum


namespace ZetaNine.CoefficientMapInjectivity
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_022 (n : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) *
    (∏ i ∈ range n, (X - C ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)))
end ZetaNine.CoefficientMapInjectivity


namespace ZetaNine.CoefficientMapInjectivity
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_023 (n : ℕ) : ℚ[X] := X * (X + C (n : ℚ))
end ZetaNine.CoefficientMapInjectivity


namespace ZetaNine.CoefficientMapInjectivity
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_024 (n : ℕ) (W : ℚ[X]) : ℚ[X] := baseNumerator n * W.comp (baseU n)
end ZetaNine.CoefficientMapInjectivity


namespace ZetaNine.CoefficientMapInjectivity
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_025 (n : ℕ) : ℚ[X] := ∏ j ∈ range (n + 1), (X + C (j : ℚ))
end ZetaNine.CoefficientMapInjectivity


namespace ZetaNine.CoefficientMapInjectivity
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_026 (n : ℕ) (W : ℚ[X]) : Prop :=
  ∀ j ≤ n, ∀ s, 1 ≤ s → s ≤ 9 →
    CoefficientMapJet.weightedLocalCoefficient n j s W = 0
end ZetaNine.CoefficientMapInjectivity


namespace ZetaNine.CoefficientMapInjectivity
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_027 (n : ℕ) (W : ℚ[X]) : Prop :=
  2 * n + 2 * W.natDegree < 9 * (n + 1)
end ZetaNine.CoefficientMapInjectivity


namespace ZetaNine.CoefficientMapInjectivity
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_028 (n : ℕ) (W : ℚ[X]) : Fin (n + 1) → Fin 9 → ℚ :=
  fun j s => CoefficientMapJet.weightedLocalCoefficient n j.val (s.val + 1) W
end ZetaNine.CoefficientMapInjectivity


namespace ZetaNine.CoefficientMapJet
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_029 (j : ℕ) : ℚ[X] := X - C (j : ℚ)
end ZetaNine.CoefficientMapJet


namespace ZetaNine.CoefficientMapJet
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_030 (n j : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) *
    (∏ i ∈ range n, (shiftedVariable j - C ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (shiftedVariable j + C (n : ℚ) + C ((i : ℚ) + 1)))
end ZetaNine.CoefficientMapJet


namespace ZetaNine.CoefficientMapJet
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_031 (n j : ℕ) : ℚ[X] :=
  ∏ k ∈ (range (n + 1)).erase j, (shiftedVariable j + C (k : ℚ))
end ZetaNine.CoefficientMapJet


namespace ZetaNine.CoefficientMapJet
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_032 (n j : ℕ) : ℚ[X] := shiftedVariable j * (shiftedVariable j + C (n : ℚ))
end ZetaNine.CoefficientMapJet


namespace ZetaNine.CoefficientMapJet
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_033 (n j : ℕ) : ℤ[X] :=
  C (-(j : ℤ) * (n - j : ℕ)) + C ((n : ℤ) - 2 * j) * X + X ^ 2
end ZetaNine.CoefficientMapJet


namespace ZetaNine.CoefficientMapJet
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_034 (n j : ℕ) : PowerSeries ℚ :=
  (shiftedNumerator n j : PowerSeries ℚ) *
    ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹
end ZetaNine.CoefficientMapJet


namespace ZetaNine.CoefficientMapJet
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_035 (n j : ℕ) (W : ℚ[X]) : PowerSeries ℚ :=
  clearedSeries n j * (W.comp (localU n j) : PowerSeries ℚ)
end ZetaNine.CoefficientMapJet


namespace ZetaNine.CoefficientMapJet
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_036 (n j s : ℕ) : ℚ := PowerSeries.coeff (9 - s) (clearedSeries n j)
end ZetaNine.CoefficientMapJet


namespace ZetaNine.CoefficientMapJet
open scoped BigOperators
open Finset Polynomial
def independent_complete_value_037 (n j s : ℕ) (W : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (weightedClearedSeries n j W)
end ZetaNine.CoefficientMapJet


namespace ZetaNine.CoefficientMapKernelBridge
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper
def independent_complete_value_038 (n : ℕ) (t : ℚ) : ℚ := ∏ k ∈ range n, (t - ((k : ℚ) + 1))
end ZetaNine.CoefficientMapKernelBridge


namespace ZetaNine.CoefficientMapKernelBridge
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper
def independent_complete_value_039 (n : ℕ) (t : ℚ) : ℚ := ∏ k ∈ range n, (t + (n : ℚ) + ((k : ℚ) + 1))
end ZetaNine.CoefficientMapKernelBridge


namespace ZetaNine.CoefficientMapKernelBridge
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper
def independent_complete_value_040 (n : ℕ) (t : ℚ) : ℚ := (t - (n : ℚ) - 1) * (t + (n : ℚ)) ^ 10
end ZetaNine.CoefficientMapKernelBridge


namespace ZetaNine.CoefficientMapKernelBridge
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper
def independent_complete_value_041 (n : ℕ) (t : ℚ) : ℚ := t ^ 10 * (t + 2 * (n : ℚ) + 1)
end ZetaNine.CoefficientMapKernelBridge


namespace ZetaNine.CoefficientMapKernelBridge
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper
def independent_complete_value_042 (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    (Fin 5 → ℚ) ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  LinearEquiv.ofBijective (quarticAggregateLinearMap n) (original_five_dimensional_map_bijective n hn2 hn)
end ZetaNine.CoefficientMapKernelBridge


namespace ZetaNine.CoefficientMapKernelBridge
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper
def independent_complete_value_043 (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) : ℚ[X] :=
  coordinatePolynomial ((actualAggregateEquiv n hn2 hn).symm b)
end ZetaNine.CoefficientMapKernelBridge


namespace ZetaNine.CoefficientMapKernelBridge
open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper
def independent_complete_value_044 (b : Fin 5 → ℚ) : ℝ :=
  (b 0 : ℝ) +
    ((b 1 : ℝ) * CoefficientMapSummation.zetaReal 3 +
     (b 2 : ℝ) * CoefficientMapSummation.zetaReal 5 +
     (b 3 : ℝ) * CoefficientMapSummation.zetaReal 7 +
     (b 4 : ℝ) * CoefficientMapSummation.zetaReal 9)
end ZetaNine.CoefficientMapKernelBridge


namespace ZetaNine.CoefficientMapMatrix
open scoped BigOperators Matrix
open Polynomial
open CoefficientMapAggregate CoefficientMapKernelBridge
def independent_complete_value_045 (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => aggregate n (X ^ i.val) j
end ZetaNine.CoefficientMapMatrix


namespace ZetaNine.CoefficientMapMatrix
open scoped BigOperators Matrix
open Polynomial
open CoefficientMapAggregate CoefficientMapKernelBridge
/-- The genuine two selected output directions are B and rho9. -/
def independent_complete_value_046 : Matrix (Fin 2) (Fin 5) ℚ :=
  fun i j => if i = 0 then (if j = 0 then 1 else 0) else (if j = 4 then 1 else 0)
end ZetaNine.CoefficientMapMatrix


namespace ZetaNine.CoefficientMapMatrix
open scoped BigOperators Matrix
open Polynomial
open CoefficientMapAggregate CoefficientMapKernelBridge
def independent_complete_value_047 (b a : ℤ) : Fin 2 → ℚ :=
  fun i => if i = 0 then (b : ℚ) else (a : ℚ)
end ZetaNine.CoefficientMapMatrix


namespace ZetaNine.CoefficientMapMatrix
open scoped BigOperators Matrix
open Polynomial
open CoefficientMapAggregate CoefficientMapKernelBridge
def independent_complete_value_048 (b a : ℤ) : Fin 5 → ℚ :=
  fun j => if j = 0 then (b : ℚ) else if j = 4 then (a : ℚ) else 0
end ZetaNine.CoefficientMapMatrix


namespace ZetaNine.CoefficientMapMatrix
open scoped BigOperators Matrix
open Polynomial
open CoefficientMapAggregate CoefficientMapKernelBridge
def independent_complete_value_049 (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) : ℚ[X] :=
  inverseMultiplier n hn2 hn (selectedIntegerOutput b a)
end ZetaNine.CoefficientMapMatrix


namespace ZetaNine.CoefficientMapPartialFractions
open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity
def independent_complete_value_050 (n j : ℕ) : ℚ[X] :=
  ∏ k ∈ (range (n + 1)).erase j, (X + C (k : ℚ))
end ZetaNine.CoefficientMapPartialFractions


namespace ZetaNine.CoefficientMapPartialFractions
open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity
def independent_complete_value_051 (n j : ℕ) (W : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc 9 (CoefficientMapJet.weightedClearedSeries n j W)
end ZetaNine.CoefficientMapPartialFractions


namespace ZetaNine.CoefficientMapPartialFractions
open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity
def independent_complete_value_052 (n j : ℕ) (W : ℚ[X]) : ℚ[X] :=
  clearedPolePolynomial n j ^ 9 * (localTruncation n j W).comp (X + C (j : ℚ))
end ZetaNine.CoefficientMapPartialFractions


namespace ZetaNine.CoefficientMapPartialFractions
open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity
def independent_complete_value_053 (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    C (CoefficientMapJet.weightedLocalCoefficient n j s W) *
      clearedPolePolynomial n j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)
end ZetaNine.CoefficientMapPartialFractions


namespace ZetaNine.CoefficientMapPartialFractions
open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity
def independent_complete_value_054 (n j : ℕ) (W : ℚ[X]) : PowerSeries ℚ :=
  ((partialNumerator n W).comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) *
    ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹
end ZetaNine.CoefficientMapPartialFractions


namespace ZetaNine.CoefficientMapReflection
open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity CoefficientMapPartialFractions
def independent_complete_value_055 (n : ℕ) : ℚ[X] := -X - C (n : ℚ)
end ZetaNine.CoefficientMapReflection


namespace ZetaNine.CoefficientMapReflection
open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity CoefficientMapPartialFractions
def independent_complete_value_056 (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n j s W
end ZetaNine.CoefficientMapReflection


namespace ZetaNine.CoefficientMapReflection
open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity CoefficientMapPartialFractions
def independent_complete_value_057 (n : ℕ) (W : ℚ[X]) : Prop :=
  2 * n + 2 * W.natDegree ≤ 9 * (n + 1) - 2
end ZetaNine.CoefficientMapReflection


namespace ZetaNine.CoefficientMapReflection
open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity CoefficientMapPartialFractions
def independent_complete_value_058 (n j s : ℕ) : ℚ[X] :=
  clearedPolePolynomial n j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)
end ZetaNine.CoefficientMapReflection


namespace ZetaNine.CoefficientMapShiftDegree
open Polynomial
def independent_complete_value_059 (n : ℕ) : ℚ[X] := (X - C ((n : ℚ) + 1)) * (X + C (n : ℚ)) ^ 10
end ZetaNine.CoefficientMapShiftDegree


namespace ZetaNine.CoefficientMapShiftDegree
open Polynomial
def independent_complete_value_060 (n : ℕ) : ℚ[X] := X ^ 10 * (X + C (2 * (n : ℚ) + 1))
end ZetaNine.CoefficientMapShiftDegree


namespace ZetaNine.CoefficientMapShiftDegree
open Polynomial
def independent_complete_value_061 (n : ℕ) (H : ℚ[X]) : ℚ[X] :=
  shiftA n * H - shiftB n * H.comp (X + C 1)
end ZetaNine.CoefficientMapShiftDegree


namespace ZetaNine.CoefficientMapSummation
open scoped BigOperators Topology
open Finset Polynomial Filter
open HarmonicStability CoefficientMapInjectivity CoefficientMapReflection
def independent_complete_value_062 (s : ℕ) : ℝ := (riemannZeta (s : ℂ)).re
end ZetaNine.CoefficientMapSummation


namespace ZetaNine.CoefficientMapSummation
open scoped BigOperators Topology
open Finset Polynomial Filter
open HarmonicStability CoefficientMapInjectivity CoefficientMapReflection
def independent_complete_value_063 (n : ℕ) (W : ℚ[X]) : ℝ :=
  (CoefficientMapFiniteSum.constantTerm n W : ℝ) +
    ((CoefficientMapFiniteSum.rho n 3 W : ℝ) * zetaReal 3 +
     (CoefficientMapFiniteSum.rho n 5 W : ℝ) * zetaReal 5 +
     (CoefficientMapFiniteSum.rho n 7 W : ℝ) * zetaReal 7 +
     (CoefficientMapFiniteSum.rho n 9 W : ℝ) * zetaReal 9)
end ZetaNine.CoefficientMapSummation


namespace ZetaNine.CoefficientMapSummation
open scoped BigOperators Topology
open Finset Polynomial Filter
open HarmonicStability CoefficientMapInjectivity CoefficientMapReflection
def independent_complete_value_064 (n : ℕ) (W : ℚ[X]) (t : ℕ) : ℝ :=
  (CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ)
end ZetaNine.CoefficientMapSummation


namespace ZetaNine.CoefficientMapTelescoper
open scoped BigOperators Topology
open Finset Polynomial Filter
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate
def independent_complete_value_065 (c : ℕ → ℚ) (j : ℕ) : ℚ := ∑ i ∈ range (j + 1), c i
end ZetaNine.CoefficientMapTelescoper


namespace ZetaNine.CoefficientMapTelescoper
open scoped BigOperators Topology
open Finset Polynomial Filter
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate
def independent_complete_value_066 (n j s : ℕ) (W : ℚ[X]) : ℚ :=
  prefixSum (fun i => weightedLocalCoefficient n i s W) j
end ZetaNine.CoefficientMapTelescoper


namespace ZetaNine.CoefficientMapTelescoper
open scoped BigOperators Topology
open Finset Polynomial Filter
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate
def independent_complete_value_067 (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  ∑ j ∈ range n, ∑ s ∈ Icc 1 9, cumulativeCoefficient n j s W / (t + (j : ℚ)) ^ s
end ZetaNine.CoefficientMapTelescoper


namespace ZetaNine.CoefficientMapTelescoper
open scoped BigOperators Topology
open Finset Polynomial Filter
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate
def independent_complete_value_068 (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range n, ∑ s ∈ Icc 1 9,
    C (cumulativeCoefficient n j s W) * partialBasis (n - 1) j s
end ZetaNine.CoefficientMapTelescoper


namespace ZetaNine.CoefficientMapTelescoper
open scoped BigOperators Topology
open Finset Polynomial Filter
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate
def independent_complete_value_069 (n : ℕ) (i : Fin (n + 1) ⊕ Fin (n + 1)) : ℚ :=
  match i with
  | .inl k => (k.val : ℚ) + 1
  | .inr k => -(n : ℚ) - (k.val : ℚ)
end ZetaNine.CoefficientMapTelescoper


namespace ZetaNine.CoefficientMapTelescoper
open scoped BigOperators Topology
open Finset Polynomial Filter
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate
def independent_complete_value_070 (n : ℕ) : ℚ[X] :=
  ∏ i : Fin (n + 1) ⊕ Fin (n + 1), (X - C (rootNode n i))
end ZetaNine.CoefficientMapTelescoper

open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
theorem independent_full_function_rfl_001 : ZetaNine.HarmonicStability.logDen = ZetaNine.HarmonicStability.independent_complete_value_001 := rfl
theorem independent_full_function_rfl_002 : ZetaNine.HarmonicStability.harmonicPower = ZetaNine.HarmonicStability.independent_complete_value_002 := rfl
theorem independent_full_function_rfl_003 : ZetaNine.CoefficientMap.numerator = ZetaNine.CoefficientMap.independent_complete_value_003 := rfl
theorem independent_full_function_rfl_004 : ZetaNine.CoefficientMap.poleProduct = ZetaNine.CoefficientMap.independent_complete_value_004 := rfl
theorem independent_full_function_rfl_005 : ZetaNine.CoefficientMap.actualR = ZetaNine.CoefficientMap.independent_complete_value_005 := rfl
theorem independent_full_function_rfl_006 : ZetaNine.CoefficientMap.clearedPoleProduct = ZetaNine.CoefficientMap.independent_complete_value_006 := rfl
theorem independent_full_function_rfl_007 : ZetaNine.CoefficientMap.clearedR = ZetaNine.CoefficientMap.independent_complete_value_007 := rfl
theorem independent_full_function_rfl_008 : ZetaNine.CoefficientMap.leadingPoleCoefficient = ZetaNine.CoefficientMap.independent_complete_value_008 := rfl
theorem independent_full_function_rfl_009 : ZetaNine.CoefficientMap.weightedR = ZetaNine.CoefficientMap.independent_complete_value_009 := rfl
theorem independent_full_function_rfl_010 : ZetaNine.CoefficientMap.clearedWeightedR = ZetaNine.CoefficientMap.independent_complete_value_010 := rfl
theorem independent_full_function_rfl_011 : ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient = ZetaNine.CoefficientMap.independent_complete_value_011 := rfl
theorem independent_full_function_rfl_012 : ZetaNine.CoefficientMapAggregate.aggregate = ZetaNine.CoefficientMapAggregate.independent_complete_value_012 := rfl
theorem independent_full_function_rfl_013 : ZetaNine.CoefficientMapAggregate.coordinatePolynomial = ZetaNine.CoefficientMapAggregate.independent_complete_value_013 := rfl
theorem independent_full_function_rfl_014 : ZetaNine.CoefficientMapAggregate.polynomialCoordinates = ZetaNine.CoefficientMapAggregate.independent_complete_value_014 := rfl
theorem independent_full_function_rfl_015 : ZetaNine.CoefficientMapAggregate.aggregateLinearMap = ZetaNine.CoefficientMapAggregate.independent_complete_value_015 := rfl
theorem independent_full_function_rfl_016 : ZetaNine.CoefficientMapAggregate.coordinateLinearMap = ZetaNine.CoefficientMapAggregate.independent_complete_value_016 := rfl
theorem independent_full_function_rfl_017 : ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap = ZetaNine.CoefficientMapAggregate.independent_complete_value_017 := rfl
theorem independent_full_function_rfl_018 : ZetaNine.CoefficientMapFiniteSum.rho = ZetaNine.CoefficientMapFiniteSum.independent_complete_value_018 := rfl
theorem independent_full_function_rfl_019 : ZetaNine.CoefficientMapFiniteSum.constantTerm = ZetaNine.CoefficientMapFiniteSum.independent_complete_value_019 := rfl
theorem independent_full_function_rfl_020 : ZetaNine.CoefficientMapFiniteSum.finiteL = ZetaNine.CoefficientMapFiniteSum.independent_complete_value_020 := rfl
theorem independent_full_function_rfl_021 : ZetaNine.CoefficientMapFiniteSum.shiftedTail = ZetaNine.CoefficientMapFiniteSum.independent_complete_value_021 := rfl
theorem independent_full_function_rfl_022 : ZetaNine.CoefficientMapInjectivity.baseNumerator = ZetaNine.CoefficientMapInjectivity.independent_complete_value_022 := rfl
theorem independent_full_function_rfl_023 : ZetaNine.CoefficientMapInjectivity.baseU = ZetaNine.CoefficientMapInjectivity.independent_complete_value_023 := rfl
theorem independent_full_function_rfl_024 : ZetaNine.CoefficientMapInjectivity.weightedNumerator = ZetaNine.CoefficientMapInjectivity.independent_complete_value_024 := rfl
theorem independent_full_function_rfl_025 : ZetaNine.CoefficientMapInjectivity.polePolynomial = ZetaNine.CoefficientMapInjectivity.independent_complete_value_025 := rfl
theorem independent_full_function_rfl_026 : ZetaNine.CoefficientMapInjectivity.AllLocalCoefficientsZero = ZetaNine.CoefficientMapInjectivity.independent_complete_value_026 := rfl
theorem independent_full_function_rfl_027 : ZetaNine.CoefficientMapInjectivity.ProperMultiplier = ZetaNine.CoefficientMapInjectivity.independent_complete_value_027 := rfl
theorem independent_full_function_rfl_028 : ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap = ZetaNine.CoefficientMapInjectivity.independent_complete_value_028 := rfl
theorem independent_full_function_rfl_029 : ZetaNine.CoefficientMapJet.shiftedVariable = ZetaNine.CoefficientMapJet.independent_complete_value_029 := rfl
theorem independent_full_function_rfl_030 : ZetaNine.CoefficientMapJet.shiftedNumerator = ZetaNine.CoefficientMapJet.independent_complete_value_030 := rfl
theorem independent_full_function_rfl_031 : ZetaNine.CoefficientMapJet.shiftedClearedDenominator = ZetaNine.CoefficientMapJet.independent_complete_value_031 := rfl
theorem independent_full_function_rfl_032 : ZetaNine.CoefficientMapJet.localU = ZetaNine.CoefficientMapJet.independent_complete_value_032 := rfl
theorem independent_full_function_rfl_033 : ZetaNine.CoefficientMapJet.integerLocalU = ZetaNine.CoefficientMapJet.independent_complete_value_033 := rfl
theorem independent_full_function_rfl_034 : ZetaNine.CoefficientMapJet.clearedSeries = ZetaNine.CoefficientMapJet.independent_complete_value_034 := rfl
theorem independent_full_function_rfl_035 : ZetaNine.CoefficientMapJet.weightedClearedSeries = ZetaNine.CoefficientMapJet.independent_complete_value_035 := rfl
theorem independent_full_function_rfl_036 : ZetaNine.CoefficientMapJet.localCoefficient = ZetaNine.CoefficientMapJet.independent_complete_value_036 := rfl
theorem independent_full_function_rfl_037 : ZetaNine.CoefficientMapJet.weightedLocalCoefficient = ZetaNine.CoefficientMapJet.independent_complete_value_037 := rfl
theorem independent_full_function_rfl_038 : ZetaNine.CoefficientMapKernelBridge.positiveProduct = ZetaNine.CoefficientMapKernelBridge.independent_complete_value_038 := rfl
theorem independent_full_function_rfl_039 : ZetaNine.CoefficientMapKernelBridge.negativeProduct = ZetaNine.CoefficientMapKernelBridge.independent_complete_value_039 := rfl
theorem independent_full_function_rfl_040 : ZetaNine.CoefficientMapKernelBridge.aValue = ZetaNine.CoefficientMapKernelBridge.independent_complete_value_040 := rfl
theorem independent_full_function_rfl_041 : ZetaNine.CoefficientMapKernelBridge.bValue = ZetaNine.CoefficientMapKernelBridge.independent_complete_value_041 := rfl
theorem independent_full_function_rfl_042 : ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv = ZetaNine.CoefficientMapKernelBridge.independent_complete_value_042 := rfl
theorem independent_full_function_rfl_043 : ZetaNine.CoefficientMapKernelBridge.inverseMultiplier = ZetaNine.CoefficientMapKernelBridge.independent_complete_value_043 := rfl
theorem independent_full_function_rfl_044 : ZetaNine.CoefficientMapKernelBridge.prescribedL = ZetaNine.CoefficientMapKernelBridge.independent_complete_value_044 := rfl
theorem independent_full_function_rfl_045 : ZetaNine.CoefficientMapMatrix.actualFMatrix = ZetaNine.CoefficientMapMatrix.independent_complete_value_045 := rfl
theorem independent_full_function_rfl_046 : ZetaNine.CoefficientMapMatrix.selectionMatrix = ZetaNine.CoefficientMapMatrix.independent_complete_value_046 := rfl
theorem independent_full_function_rfl_047 : ZetaNine.CoefficientMapMatrix.selectedIntegerPair = ZetaNine.CoefficientMapMatrix.independent_complete_value_047 := rfl
theorem independent_full_function_rfl_048 : ZetaNine.CoefficientMapMatrix.selectedIntegerOutput = ZetaNine.CoefficientMapMatrix.independent_complete_value_048 := rfl
theorem independent_full_function_rfl_049 : ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier = ZetaNine.CoefficientMapMatrix.independent_complete_value_049 := rfl
theorem independent_full_function_rfl_050 : ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial = ZetaNine.CoefficientMapPartialFractions.independent_complete_value_050 := rfl
theorem independent_full_function_rfl_051 : ZetaNine.CoefficientMapPartialFractions.localTruncation = ZetaNine.CoefficientMapPartialFractions.independent_complete_value_051 := rfl
theorem independent_full_function_rfl_052 : ZetaNine.CoefficientMapPartialFractions.partialBlock = ZetaNine.CoefficientMapPartialFractions.independent_complete_value_052 := rfl
theorem independent_full_function_rfl_053 : ZetaNine.CoefficientMapPartialFractions.partialNumerator = ZetaNine.CoefficientMapPartialFractions.independent_complete_value_053 := rfl
theorem independent_full_function_rfl_054 : ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries = ZetaNine.CoefficientMapPartialFractions.independent_complete_value_054 := rfl
theorem independent_full_function_rfl_055 : ZetaNine.CoefficientMapReflection.reflectionVariable = ZetaNine.CoefficientMapReflection.independent_complete_value_055 := rfl
theorem independent_full_function_rfl_056 : ZetaNine.CoefficientMapReflection.rho = ZetaNine.CoefficientMapReflection.independent_complete_value_056 := rfl
theorem independent_full_function_rfl_057 : ZetaNine.CoefficientMapReflection.StrongProperMultiplier = ZetaNine.CoefficientMapReflection.independent_complete_value_057 := rfl
theorem independent_full_function_rfl_058 : ZetaNine.CoefficientMapReflection.partialBasis = ZetaNine.CoefficientMapReflection.independent_complete_value_058 := rfl
theorem independent_full_function_rfl_059 : ZetaNine.CoefficientMapShiftDegree.shiftA = ZetaNine.CoefficientMapShiftDegree.independent_complete_value_059 := rfl
theorem independent_full_function_rfl_060 : ZetaNine.CoefficientMapShiftDegree.shiftB = ZetaNine.CoefficientMapShiftDegree.independent_complete_value_060 := rfl
theorem independent_full_function_rfl_061 : ZetaNine.CoefficientMapShiftDegree.shiftDifference = ZetaNine.CoefficientMapShiftDegree.independent_complete_value_061 := rfl
theorem independent_full_function_rfl_062 : ZetaNine.CoefficientMapSummation.zetaReal = ZetaNine.CoefficientMapSummation.independent_complete_value_062 := rfl
theorem independent_full_function_rfl_063 : ZetaNine.CoefficientMapSummation.exactL = ZetaNine.CoefficientMapSummation.independent_complete_value_063 := rfl
theorem independent_full_function_rfl_064 : ZetaNine.CoefficientMapSummation.actualSeries = ZetaNine.CoefficientMapSummation.independent_complete_value_064 := rfl
theorem independent_full_function_rfl_065 : ZetaNine.CoefficientMapTelescoper.prefixSum = ZetaNine.CoefficientMapTelescoper.independent_complete_value_065 := rfl
theorem independent_full_function_rfl_066 : ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient = ZetaNine.CoefficientMapTelescoper.independent_complete_value_066 := rfl
theorem independent_full_function_rfl_067 : ZetaNine.CoefficientMapTelescoper.telescoper = ZetaNine.CoefficientMapTelescoper.independent_complete_value_067 := rfl
theorem independent_full_function_rfl_068 : ZetaNine.CoefficientMapTelescoper.telescoperNumerator = ZetaNine.CoefficientMapTelescoper.independent_complete_value_068 := rfl
theorem independent_full_function_rfl_069 : ZetaNine.CoefficientMapTelescoper.rootNode = ZetaNine.CoefficientMapTelescoper.independent_complete_value_069 := rfl
theorem independent_full_function_rfl_070 : ZetaNine.CoefficientMapTelescoper.rootPolynomial = ZetaNine.CoefficientMapTelescoper.independent_complete_value_070 := rfl

run_meta do
  for (name,aliasName) in [(`ZetaNine.HarmonicStability.logDen, `ZetaNine.HarmonicStability.independent_complete_value_001), (`ZetaNine.HarmonicStability.harmonicPower, `ZetaNine.HarmonicStability.independent_complete_value_002), (`ZetaNine.CoefficientMap.numerator, `ZetaNine.CoefficientMap.independent_complete_value_003), (`ZetaNine.CoefficientMap.poleProduct, `ZetaNine.CoefficientMap.independent_complete_value_004), (`ZetaNine.CoefficientMap.actualR, `ZetaNine.CoefficientMap.independent_complete_value_005), (`ZetaNine.CoefficientMap.clearedPoleProduct, `ZetaNine.CoefficientMap.independent_complete_value_006), (`ZetaNine.CoefficientMap.clearedR, `ZetaNine.CoefficientMap.independent_complete_value_007), (`ZetaNine.CoefficientMap.leadingPoleCoefficient, `ZetaNine.CoefficientMap.independent_complete_value_008), (`ZetaNine.CoefficientMap.weightedR, `ZetaNine.CoefficientMap.independent_complete_value_009), (`ZetaNine.CoefficientMap.clearedWeightedR, `ZetaNine.CoefficientMap.independent_complete_value_010), (`ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient, `ZetaNine.CoefficientMap.independent_complete_value_011), (`ZetaNine.CoefficientMapAggregate.aggregate, `ZetaNine.CoefficientMapAggregate.independent_complete_value_012), (`ZetaNine.CoefficientMapAggregate.coordinatePolynomial, `ZetaNine.CoefficientMapAggregate.independent_complete_value_013), (`ZetaNine.CoefficientMapAggregate.polynomialCoordinates, `ZetaNine.CoefficientMapAggregate.independent_complete_value_014), (`ZetaNine.CoefficientMapAggregate.aggregateLinearMap, `ZetaNine.CoefficientMapAggregate.independent_complete_value_015), (`ZetaNine.CoefficientMapAggregate.coordinateLinearMap, `ZetaNine.CoefficientMapAggregate.independent_complete_value_016), (`ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap, `ZetaNine.CoefficientMapAggregate.independent_complete_value_017), (`ZetaNine.CoefficientMapFiniteSum.rho, `ZetaNine.CoefficientMapFiniteSum.independent_complete_value_018), (`ZetaNine.CoefficientMapFiniteSum.constantTerm, `ZetaNine.CoefficientMapFiniteSum.independent_complete_value_019), (`ZetaNine.CoefficientMapFiniteSum.finiteL, `ZetaNine.CoefficientMapFiniteSum.independent_complete_value_020), (`ZetaNine.CoefficientMapFiniteSum.shiftedTail, `ZetaNine.CoefficientMapFiniteSum.independent_complete_value_021), (`ZetaNine.CoefficientMapInjectivity.baseNumerator, `ZetaNine.CoefficientMapInjectivity.independent_complete_value_022), (`ZetaNine.CoefficientMapInjectivity.baseU, `ZetaNine.CoefficientMapInjectivity.independent_complete_value_023), (`ZetaNine.CoefficientMapInjectivity.weightedNumerator, `ZetaNine.CoefficientMapInjectivity.independent_complete_value_024), (`ZetaNine.CoefficientMapInjectivity.polePolynomial, `ZetaNine.CoefficientMapInjectivity.independent_complete_value_025), (`ZetaNine.CoefficientMapInjectivity.AllLocalCoefficientsZero, `ZetaNine.CoefficientMapInjectivity.independent_complete_value_026), (`ZetaNine.CoefficientMapInjectivity.ProperMultiplier, `ZetaNine.CoefficientMapInjectivity.independent_complete_value_027), (`ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap, `ZetaNine.CoefficientMapInjectivity.independent_complete_value_028), (`ZetaNine.CoefficientMapJet.shiftedVariable, `ZetaNine.CoefficientMapJet.independent_complete_value_029), (`ZetaNine.CoefficientMapJet.shiftedNumerator, `ZetaNine.CoefficientMapJet.independent_complete_value_030), (`ZetaNine.CoefficientMapJet.shiftedClearedDenominator, `ZetaNine.CoefficientMapJet.independent_complete_value_031), (`ZetaNine.CoefficientMapJet.localU, `ZetaNine.CoefficientMapJet.independent_complete_value_032), (`ZetaNine.CoefficientMapJet.integerLocalU, `ZetaNine.CoefficientMapJet.independent_complete_value_033), (`ZetaNine.CoefficientMapJet.clearedSeries, `ZetaNine.CoefficientMapJet.independent_complete_value_034), (`ZetaNine.CoefficientMapJet.weightedClearedSeries, `ZetaNine.CoefficientMapJet.independent_complete_value_035), (`ZetaNine.CoefficientMapJet.localCoefficient, `ZetaNine.CoefficientMapJet.independent_complete_value_036), (`ZetaNine.CoefficientMapJet.weightedLocalCoefficient, `ZetaNine.CoefficientMapJet.independent_complete_value_037), (`ZetaNine.CoefficientMapKernelBridge.positiveProduct, `ZetaNine.CoefficientMapKernelBridge.independent_complete_value_038), (`ZetaNine.CoefficientMapKernelBridge.negativeProduct, `ZetaNine.CoefficientMapKernelBridge.independent_complete_value_039), (`ZetaNine.CoefficientMapKernelBridge.aValue, `ZetaNine.CoefficientMapKernelBridge.independent_complete_value_040), (`ZetaNine.CoefficientMapKernelBridge.bValue, `ZetaNine.CoefficientMapKernelBridge.independent_complete_value_041), (`ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv, `ZetaNine.CoefficientMapKernelBridge.independent_complete_value_042), (`ZetaNine.CoefficientMapKernelBridge.inverseMultiplier, `ZetaNine.CoefficientMapKernelBridge.independent_complete_value_043), (`ZetaNine.CoefficientMapKernelBridge.prescribedL, `ZetaNine.CoefficientMapKernelBridge.independent_complete_value_044), (`ZetaNine.CoefficientMapMatrix.actualFMatrix, `ZetaNine.CoefficientMapMatrix.independent_complete_value_045), (`ZetaNine.CoefficientMapMatrix.selectionMatrix, `ZetaNine.CoefficientMapMatrix.independent_complete_value_046), (`ZetaNine.CoefficientMapMatrix.selectedIntegerPair, `ZetaNine.CoefficientMapMatrix.independent_complete_value_047), (`ZetaNine.CoefficientMapMatrix.selectedIntegerOutput, `ZetaNine.CoefficientMapMatrix.independent_complete_value_048), (`ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier, `ZetaNine.CoefficientMapMatrix.independent_complete_value_049), (`ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial, `ZetaNine.CoefficientMapPartialFractions.independent_complete_value_050), (`ZetaNine.CoefficientMapPartialFractions.localTruncation, `ZetaNine.CoefficientMapPartialFractions.independent_complete_value_051), (`ZetaNine.CoefficientMapPartialFractions.partialBlock, `ZetaNine.CoefficientMapPartialFractions.independent_complete_value_052), (`ZetaNine.CoefficientMapPartialFractions.partialNumerator, `ZetaNine.CoefficientMapPartialFractions.independent_complete_value_053), (`ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries, `ZetaNine.CoefficientMapPartialFractions.independent_complete_value_054), (`ZetaNine.CoefficientMapReflection.reflectionVariable, `ZetaNine.CoefficientMapReflection.independent_complete_value_055), (`ZetaNine.CoefficientMapReflection.rho, `ZetaNine.CoefficientMapReflection.independent_complete_value_056), (`ZetaNine.CoefficientMapReflection.StrongProperMultiplier, `ZetaNine.CoefficientMapReflection.independent_complete_value_057), (`ZetaNine.CoefficientMapReflection.partialBasis, `ZetaNine.CoefficientMapReflection.independent_complete_value_058), (`ZetaNine.CoefficientMapShiftDegree.shiftA, `ZetaNine.CoefficientMapShiftDegree.independent_complete_value_059), (`ZetaNine.CoefficientMapShiftDegree.shiftB, `ZetaNine.CoefficientMapShiftDegree.independent_complete_value_060), (`ZetaNine.CoefficientMapShiftDegree.shiftDifference, `ZetaNine.CoefficientMapShiftDegree.independent_complete_value_061), (`ZetaNine.CoefficientMapSummation.zetaReal, `ZetaNine.CoefficientMapSummation.independent_complete_value_062), (`ZetaNine.CoefficientMapSummation.exactL, `ZetaNine.CoefficientMapSummation.independent_complete_value_063), (`ZetaNine.CoefficientMapSummation.actualSeries, `ZetaNine.CoefficientMapSummation.independent_complete_value_064), (`ZetaNine.CoefficientMapTelescoper.prefixSum, `ZetaNine.CoefficientMapTelescoper.independent_complete_value_065), (`ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient, `ZetaNine.CoefficientMapTelescoper.independent_complete_value_066), (`ZetaNine.CoefficientMapTelescoper.telescoper, `ZetaNine.CoefficientMapTelescoper.independent_complete_value_067), (`ZetaNine.CoefficientMapTelescoper.telescoperNumerator, `ZetaNine.CoefficientMapTelescoper.independent_complete_value_068), (`ZetaNine.CoefficientMapTelescoper.rootNode, `ZetaNine.CoefficientMapTelescoper.independent_complete_value_069), (`ZetaNine.CoefficientMapTelescoper.rootPolynomial, `ZetaNine.CoefficientMapTelescoper.independent_complete_value_070)] do
    let .defnInfo d ← getConstInfo name | throwError "Original is not actual Definition"
    let .defnInfo a ← getConstInfo aliasName | throwError "Source-body alias is not actual Definition"
    let te ← isDefEq d.type a.type
    let ve ← isDefEq d.value a.value
    unless te && ve do throwError "Complete Definition including proof fields differs: {name}"
    let axs ← Lean.collectAxioms aliasName
    IO.println (Json.mkObj [("kind",Json.str "independent_complete_definition_kernel"),
      ("declaration",Json.str name.toString),("alias",Json.str aliasName.toString),
      ("type_kernel_equal",toJson te),("full_value_kernel_equal",toJson ve),
      ("original_type_expression_repr",Json.str (reprStr d.type)),
      ("alias_type_expression_repr",Json.str (reprStr a.type)),
      ("original_complete_value_expression_repr",Json.str (reprStr d.value)),
      ("alias_complete_value_expression_repr",Json.str (reprStr a.value)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  for name in [`independent_full_function_rfl_001, `independent_full_function_rfl_002, `independent_full_function_rfl_003, `independent_full_function_rfl_004, `independent_full_function_rfl_005, `independent_full_function_rfl_006, `independent_full_function_rfl_007, `independent_full_function_rfl_008, `independent_full_function_rfl_009, `independent_full_function_rfl_010, `independent_full_function_rfl_011, `independent_full_function_rfl_012, `independent_full_function_rfl_013, `independent_full_function_rfl_014, `independent_full_function_rfl_015, `independent_full_function_rfl_016, `independent_full_function_rfl_017, `independent_full_function_rfl_018, `independent_full_function_rfl_019, `independent_full_function_rfl_020, `independent_full_function_rfl_021, `independent_full_function_rfl_022, `independent_full_function_rfl_023, `independent_full_function_rfl_024, `independent_full_function_rfl_025, `independent_full_function_rfl_026, `independent_full_function_rfl_027, `independent_full_function_rfl_028, `independent_full_function_rfl_029, `independent_full_function_rfl_030, `independent_full_function_rfl_031, `independent_full_function_rfl_032, `independent_full_function_rfl_033, `independent_full_function_rfl_034, `independent_full_function_rfl_035, `independent_full_function_rfl_036, `independent_full_function_rfl_037, `independent_full_function_rfl_038, `independent_full_function_rfl_039, `independent_full_function_rfl_040, `independent_full_function_rfl_041, `independent_full_function_rfl_042, `independent_full_function_rfl_043, `independent_full_function_rfl_044, `independent_full_function_rfl_045, `independent_full_function_rfl_046, `independent_full_function_rfl_047, `independent_full_function_rfl_048, `independent_full_function_rfl_049, `independent_full_function_rfl_050, `independent_full_function_rfl_051, `independent_full_function_rfl_052, `independent_full_function_rfl_053, `independent_full_function_rfl_054, `independent_full_function_rfl_055, `independent_full_function_rfl_056, `independent_full_function_rfl_057, `independent_full_function_rfl_058, `independent_full_function_rfl_059, `independent_full_function_rfl_060, `independent_full_function_rfl_061, `independent_full_function_rfl_062, `independent_full_function_rfl_063, `independent_full_function_rfl_064, `independent_full_function_rfl_065, `independent_full_function_rfl_066, `independent_full_function_rfl_067, `independent_full_function_rfl_068, `independent_full_function_rfl_069, `independent_full_function_rfl_070] do
    let .thmInfo t ← getConstInfo name | throwError "Expected actual rfl theorem"
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind",Json.str "independent_complete_function_rfl"),
      ("declaration",Json.str name.toString),("full_type_expression_repr",Json.str (reprStr t.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
