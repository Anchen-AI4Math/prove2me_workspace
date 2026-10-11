import missions.zeta9.formalization.CoefficientMapFormalTransportOutputs
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
noncomputable section
open scoped BigOperators Matrix
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMap ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapFiniteSum
open ZetaNine.CoefficientMapConnection ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapFormalTransportOutputs
namespace OutputsIndependentFormula
def connectionPair (n : ℕ) (r : Fin 5) : ℚ[X] × ℚ[X] :=
  if hn : 1 ≤ n then Classical.choose (ZetaNine.CoefficientMapConnection.connection_five_systems_unique n hn r).exists else (0,0)
def connectionP (n : ℕ) (r : Fin 5) : ℚ[X] := (ZetaNine.CoefficientMapFormalTransportData.connectionPair n r).1
def connectionQ (n : ℕ) (r : Fin 5) : ℚ[X] := (ZetaNine.CoefficientMapFormalTransportData.connectionPair n r).2
def connectionGamma (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ := fun r l => (ZetaNine.CoefficientMapFormalTransportData.connectionP n r).coeff l.val
def remainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) * (∏ i ∈ range n, (X - C ((i : ℚ) + 2))) *
    (∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1))) * q.comp (ZetaNine.CoefficientMapConnection.connectionV n)
def shiftedRemainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  (ZetaNine.CoefficientMapFormalTransportData.remainderNumerator n q).comp (X + 1)
def numeratorClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  ((A.comp (ZetaNine.CoefficientMapJet.shiftedVariable j) : ℚ[X]) : PowerSeries ℚ) *
    ((ZetaNine.CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹
def numeratorLocalCoefficient (m j s : ℕ) (A : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries m j A)
def remainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient (n + 1) j s
    (ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator n q)
def extendedOldCoefficient (n j s : ℕ) (P : ℚ[X]) : ℚ :=
  if 1 ≤ j ∧ j ≤ n + 1 then ZetaNine.CoefficientMapJet.weightedLocalCoefficient n (j - 1) s P else 0
def extendedRemainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  if j ≤ n + 1 then ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient n j s q else 0
def previousRemainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  if j = 0 then 0 else ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient n (j - 1) s q
def rho (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W
def constantTerm (n : ℕ) (W : ℚ[X]) : ℚ :=
  -(∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9, ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W * ZetaNine.HarmonicStability.harmonicPower s j)
def aggregate (n : ℕ) (W : ℚ[X]) (i : Fin 5) : ℚ :=
  match i.val with
  | 0 => ZetaNine.CoefficientMapFiniteSum.constantTerm n W
  | 1 => ZetaNine.CoefficientMapFiniteSum.rho n 3 W
  | 2 => ZetaNine.CoefficientMapFiniteSum.rho n 5 W
  | 3 => ZetaNine.CoefficientMapFiniteSum.rho n 7 W
  | _ => ZetaNine.CoefficientMapFiniteSum.rho n 9 W
def aggregateLinearMap (n : ℕ) : ℚ[X] →ₗ[ℚ] (Fin 5 → ℚ) where
  toFun := ZetaNine.CoefficientMapAggregate.aggregate n
  map_add' := ZetaNine.CoefficientMapAggregate.aggregate_add n
  map_smul' := ZetaNine.CoefficientMapAggregate.aggregate_smul n
def quarticAggregateLinearMap (n : ℕ) : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) :=
  (ZetaNine.CoefficientMapAggregate.aggregateLinearMap n).comp ZetaNine.CoefficientMapAggregate.coordinateLinearMap
def actualFMatrix (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => ZetaNine.CoefficientMapAggregate.aggregate n (X ^ i.val) j
end OutputsIndependentFormula
namespace OutputsIndependentWhole
theorem whole_connectionPair : ZetaNine.CoefficientMapFormalTransportData.connectionPair = OutputsIndependentFormula.connectionPair := by rfl
theorem whole_connectionP : ZetaNine.CoefficientMapFormalTransportData.connectionP = OutputsIndependentFormula.connectionP := by rfl
theorem whole_connectionQ : ZetaNine.CoefficientMapFormalTransportData.connectionQ = OutputsIndependentFormula.connectionQ := by rfl
theorem whole_connectionGamma : ZetaNine.CoefficientMapFormalTransportData.connectionGamma = OutputsIndependentFormula.connectionGamma := by rfl
theorem whole_remainderNumerator : ZetaNine.CoefficientMapFormalTransportData.remainderNumerator = OutputsIndependentFormula.remainderNumerator := by rfl
theorem whole_shiftedRemainderNumerator : ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator = OutputsIndependentFormula.shiftedRemainderNumerator := by rfl
theorem whole_numeratorClearedSeries : ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries = OutputsIndependentFormula.numeratorClearedSeries := by rfl
theorem whole_numeratorLocalCoefficient : ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient = OutputsIndependentFormula.numeratorLocalCoefficient := by rfl
theorem whole_remainderCoefficient : ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient = OutputsIndependentFormula.remainderCoefficient := by rfl
theorem whole_extendedOldCoefficient : ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient = OutputsIndependentFormula.extendedOldCoefficient := by rfl
theorem whole_extendedRemainderCoefficient : ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient = OutputsIndependentFormula.extendedRemainderCoefficient := by rfl
theorem whole_previousRemainderCoefficient : ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient = OutputsIndependentFormula.previousRemainderCoefficient := by rfl
theorem whole_rho : ZetaNine.CoefficientMapFiniteSum.rho = OutputsIndependentFormula.rho := by rfl
theorem whole_constantTerm : ZetaNine.CoefficientMapFiniteSum.constantTerm = OutputsIndependentFormula.constantTerm := by rfl
theorem whole_aggregate : ZetaNine.CoefficientMapAggregate.aggregate = OutputsIndependentFormula.aggregate := by rfl
theorem whole_aggregateLinearMap : ZetaNine.CoefficientMapAggregate.aggregateLinearMap = OutputsIndependentFormula.aggregateLinearMap := by rfl
theorem whole_quarticAggregateLinearMap : ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap = OutputsIndependentFormula.quarticAggregateLinearMap := by rfl
theorem whole_actualFMatrix : ZetaNine.CoefficientMapMatrix.actualFMatrix = OutputsIndependentFormula.actualFMatrix := by rfl
end OutputsIndependentWhole
namespace OutputsIndependentExpected
theorem expected_weightedR_eval_one_zero (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) :
    weightedR n W 1 = 0 := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.weightedR_eval_one_zero n hn W

theorem expected_quartic_properMultiplier (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    ProperMultiplier n W := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.quartic_properMultiplier n W hW

theorem expected_weighted_boundary_sum_zero (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      weightedLocalCoefficient n j s W / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.weighted_boundary_sum_zero n hn W hW

theorem expected_remainder_boundary_sum_zero (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) :
    (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
      remainderCoefficient n j s q / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.remainder_boundary_sum_zero n hn q hq

theorem expected_sum_extendedOldCoefficient_harmonic (n s : ℕ) (P : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedOldCoefficient n j s P * harmonicPower s j) =
      ∑ j ∈ range (n + 1), weightedLocalCoefficient n j s P * harmonicPower s (j + 1) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedOldCoefficient_harmonic n s P

theorem expected_sum_extendedRemainderCoefficient_harmonic (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedRemainderCoefficient n j s q * harmonicPower s j) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q * harmonicPower s j := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedRemainderCoefficient_harmonic n s q

theorem expected_sum_previousRemainderCoefficient_harmonic (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), previousRemainderCoefficient n j s q * harmonicPower s j) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q * harmonicPower s (j + 1) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.sum_previousRemainderCoefficient_harmonic n s q

theorem expected_sum_harmonic_succ (N s : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range N, f j * harmonicPower s (j + 1)) =
      (∑ j ∈ range N, f j * harmonicPower s j) +
        ∑ j ∈ range N, f j / (((j + 1 : ℕ) : ℚ) ^ s) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.sum_harmonic_succ N s f

theorem expected_actual_chosen_harmonic_order_transport (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    (∑ j ∈ range (n + 3), weightedLocalCoefficient (n + 2) j s (X ^ r.val) * harmonicPower s j) =
      (∑ j ∈ range (n + 1), weightedLocalCoefficient n j s (connectionP n r) * harmonicPower s j) +
      (∑ j ∈ range (n + 1), weightedLocalCoefficient n j s (connectionP n r) /
        (((j + 1 : ℕ) : ℚ) ^ s)) -
      (∑ j ∈ range (n + 2), remainderCoefficient n j s (connectionQ n r) /
        (((j + 1 : ℕ) : ℚ) ^ s)) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_harmonic_order_transport n hn r s hs1 hs9

theorem expected_actual_chosen_constantTerm_correction (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r) -
      (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s (connectionP n r) / (((j + 1 : ℕ) : ℚ) ^ s)) +
      (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
        remainderCoefficient n j s (connectionQ n r) / (((j + 1 : ℕ) : ℚ) ^ s)) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_correction n hn r

theorem expected_actual_chosen_constantTerm_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport n hn r

theorem expected_actual_chosen_five_output_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    aggregate (n + 2) (X ^ r.val) = aggregate n (connectionP n r) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport n hn r

theorem expected_actual_chosen_Gamma_row_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    aggregate n (connectionP n r) = connectionGamma n r ᵥ* actualFMatrix n := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_Gamma_row_transport n hn r

theorem expected_actual_five_output_matrix_transport (n : ℕ) (hn : 1 ≤ n) :
    actualFMatrix (n + 2) = connectionGamma n * actualFMatrix n := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport n hn

theorem expected_n_one_five_output_transport (r : Fin 5) :
    aggregate 3 (X ^ r.val) = aggregate 1 (connectionP 1 r) := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.n_one_five_output_transport r

theorem expected_n_one_matrix_transport :
    actualFMatrix 3 = connectionGamma 1 * actualFMatrix 1 := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.n_one_matrix_transport

end OutputsIndependentExpected
namespace OutputsIndependentBoundary
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
end OutputsIndependentBoundary
