import Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs
import Oracle.CoefficientMapFormalTransportOutputs
import Solutions.OutputsMatrixV2
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
noncomputable section
open scoped BigOperators Matrix
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapFiniteSum
open ZetaNine.CoefficientMapConnection ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapFormalTransportOutputs
namespace OutputsPlatformWhole
theorem whole_00_connectionPair : ZetaNine.CoefficientMapFormalTransportData.connectionPair = OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionPair := by rfl
theorem whole_01_connectionP : ZetaNine.CoefficientMapFormalTransportData.connectionP = OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionP := by rfl
theorem whole_02_connectionQ : ZetaNine.CoefficientMapFormalTransportData.connectionQ = OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionQ := by rfl
theorem whole_03_connectionGamma : ZetaNine.CoefficientMapFormalTransportData.connectionGamma = OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionGamma := by rfl
theorem whole_04_remainderNumerator : ZetaNine.CoefficientMapFormalTransportData.remainderNumerator = OutputsPlatformOracle.CoefficientMapFormalTransportData.remainderNumerator := by rfl
theorem whole_05_shiftedRemainderNumerator : ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator = OutputsPlatformOracle.CoefficientMapFormalTransportData.shiftedRemainderNumerator := by rfl
theorem whole_06_numeratorClearedSeries : ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries = OutputsPlatformOracle.CoefficientMapFormalTransportData.numeratorClearedSeries := by rfl
theorem whole_07_numeratorLocalCoefficient : ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient = OutputsPlatformOracle.CoefficientMapFormalTransportData.numeratorLocalCoefficient := by rfl
theorem whole_08_remainderCoefficient : ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient = OutputsPlatformOracle.CoefficientMapFormalTransportData.remainderCoefficient := by rfl
theorem whole_09_extendedOldCoefficient : ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient = OutputsPlatformOracle.CoefficientMapFormalTransportData.extendedOldCoefficient := by rfl
theorem whole_10_extendedRemainderCoefficient : ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient = OutputsPlatformOracle.CoefficientMapFormalTransportData.extendedRemainderCoefficient := by rfl
theorem whole_11_previousRemainderCoefficient : ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient = OutputsPlatformOracle.CoefficientMapFormalTransportData.previousRemainderCoefficient := by rfl
theorem whole_12_rho : ZetaNine.CoefficientMapFiniteSum.rho = OutputsPlatformOracle.CoefficientMapFiniteSum.rho := by rfl
theorem whole_13_constantTerm : ZetaNine.CoefficientMapFiniteSum.constantTerm = OutputsPlatformOracle.CoefficientMapFiniteSum.constantTerm := by rfl
theorem whole_14_aggregate : ZetaNine.CoefficientMapAggregate.aggregate = OutputsPlatformOracle.CoefficientMapAggregate.aggregate := by rfl
theorem whole_15_aggregateLinearMap : ZetaNine.CoefficientMapAggregate.aggregateLinearMap = OutputsPlatformOracle.CoefficientMapAggregate.aggregateLinearMap := by rfl
theorem whole_16_quarticAggregateLinearMap : ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap = OutputsPlatformOracle.CoefficientMapAggregate.quarticAggregateLinearMap := by rfl
theorem whole_17_actualFMatrix : ZetaNine.CoefficientMapMatrix.actualFMatrix = OutputsPlatformOracle.CoefficientMapMatrix.actualFMatrix := by rfl
theorem whole_18_parameterScale : ZetaNine.CoefficientMapParameterShift.parameterScale = OutputsPlatformOracle.CoefficientMapParameterShift.parameterScale := by rfl
theorem whole_19_connectionRemainder : ZetaNine.CoefficientMapParameterShift.connectionRemainder = OutputsPlatformOracle.CoefficientMapParameterShift.connectionRemainder := by rfl
end OutputsPlatformWhole
namespace OutputsPlatformBoundary
theorem minimum_B (r : Fin 5) : constantTerm 3 (X ^ r.val) = constantTerm 1 (connectionP 1 r) :=
  actual_chosen_constantTerm_transport 1 (by decide) r
theorem minimum_all_coordinates (r : Fin 5) : aggregate 3 (X ^ r.val) = aggregate 1 (connectionP 1 r) :=
  actual_chosen_five_output_transport 1 (by decide) r
theorem minimum_LEFT_matrix : actualFMatrix 3 = connectionGamma 1 * actualFMatrix 1 :=
  actual_five_output_matrix_transport 1 (by decide)
theorem even_LEFT_matrix : actualFMatrix 4 = connectionGamma 2 * actualFMatrix 2 :=
  actual_five_output_matrix_transport 2 (by decide)
theorem odd_LEFT_matrix : actualFMatrix 5 = connectionGamma 3 * actualFMatrix 3 :=
  actual_five_output_matrix_transport 3 (by decide)
theorem maximum_remainder_degree :
    (∑ j ∈ range 3, ∑ s ∈ Icc 1 9, remainderCoefficient 1 j s (X ^ 9) / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 :=
  remainder_boundary_sum_zero 1 (by decide) (X ^ 9) (by norm_num)
theorem excluded_zero_parameter : weightedR 0 (1 : ℚ[X]) 1 = 1 := by
  norm_num [weightedR, actualR, numerator, poleProduct]
theorem empty_harmonic_successor (s : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range 0, f j * ZetaNine.HarmonicStability.harmonicPower s (j + 1)) = 0 := by simp
theorem maximum_quartic_degree :
    (∑ j ∈ range 2, ∑ s ∈ Icc 1 9, weightedLocalCoefficient 1 j s (X ^ 4) / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 :=
  weighted_boundary_sum_zero 1 (by decide) (X ^ 4) (by norm_num)
end OutputsPlatformBoundary
