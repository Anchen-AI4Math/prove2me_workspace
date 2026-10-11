import missions.zeta9.formalization.CoefficientMapAggregate
import Lean

open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false
set_option maxHeartbeats 2200000

theorem agg_ind_actual_B_negative_harmonic (n : ℕ) (W : ℚ[X]) :
    aggregate n W 0 = -(∑ j ∈ range (n+1), ∑ s ∈ Icc 1 9,
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W *
        ZetaNine.HarmonicStability.harmonicPower s j) := rfl

theorem agg_ind_actual_five_odd_coordinates (n : ℕ) (W : ℚ[X]) :
    aggregate n W 1 = (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 3 W) ∧
    aggregate n W 2 = (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 5 W) ∧
    aggregate n W 3 = (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 7 W) ∧
    aggregate n W 4 = (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 9 W) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem agg_ind_general_rational_linearity (n : ℕ) (a b : ℚ) (W V : ℚ[X]) :
    aggregate n (a • W + b • V) = a • aggregate n W + b • aggregate n V := by
  rw [aggregate_add, aggregate_smul, aggregate_smul]

theorem agg_ind_zero_all_n (n : ℕ) : aggregate n (0 : ℚ[X]) = 0 :=
  (aggregateLinearMap n).map_zero

theorem agg_ind_coordinate_zero : coordinatePolynomial (0 : Fin 5 → ℚ) = 0 :=
  coordinateLinearMap.map_zero

theorem agg_ind_roundtrip_zero : coordinatePolynomial (polynomialCoordinates (0 : ℚ[X])) = 0 :=
  polynomial_restore 0 (by simp)

theorem agg_ind_roundtrip_nonmonic :
    coordinatePolynomial (polynomialCoordinates (C (3 : ℚ) * X ^ 4 + C 7)) = C 3 * X ^ 4 + C 7 := by
  apply polynomial_restore
  exact (natDegree_add_le _ _).trans (by simp)

theorem agg_ind_basis (i : Fin 5) : coordinatePolynomial (Pi.single i (1 : ℚ)) = X ^ i.val := by
  classical
  unfold coordinatePolynomial
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem agg_ind_quartic_restoration_kernel (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    aggregate n W = 0 ↔ quarticAggregateLinearMap n (polynomialCoordinates W) = 0 := by
  rw [quartic_aggregate_is_actual, polynomial_restore W hW]

theorem agg_ind_hasSum_zero_strong_even (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hf : aggregate n W = 0) :
    HasSum (fun k : ℕ => (ZetaNine.CoefficientMap.weightedR n W ((k+1 : ℕ) : ℚ) : ℝ)) 0 := by
  have h := actualSeries_hasSum_exactL n hn W hstrong
  rw [aggregate_zero_exactL n W hf] at h
  exact h

theorem agg_ind_all_rho_zero_strong_even (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hf : aggregate n W = 0) :
    ∀ s, 1 ≤ s → s ≤ 9 →
      (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) = 0 := by
  intro s hs1 hs9
  exact aggregate_zero_all_rho n hn W hstrong hf s hs1 hs9

theorem agg_ind_n_zero_series (W : ℚ[X]) :
    ZetaNine.CoefficientMapJet.weightedClearedSeries 0 0 W =
      (W.comp ((X : ℚ[X]) ^ 2) : PowerSeries ℚ) := by
  have hb : ZetaNine.CoefficientMapJet.clearedSeries 0 0 = 1 := by
    simp [ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator,
      ZetaNine.CoefficientMapJet.shiftedClearedDenominator]
  have hu : ZetaNine.CoefficientMapJet.localU 0 0 = (X : ℚ[X]) ^ 2 := by
    simp [ZetaNine.CoefficientMapJet.localU,ZetaNine.CoefficientMapJet.shiftedVariable,pow_two]
  simp only [ZetaNine.CoefficientMapJet.weightedClearedSeries,hb,hu,one_mul]

theorem agg_ind_n_zero_harmonic_constant (W : ℚ[X]) : aggregate 0 W 0 = 0 := by
  simp [aggregate,ZetaNine.CoefficientMapFiniteSum.constantTerm,ZetaNine.HarmonicStability.harmonicPower]

theorem agg_ind_n_zero_X_four_odd_rho (s : ℕ) (hs2 : 2 ≤ s) (hs9 : s ≤ 9) :
    ZetaNine.CoefficientMapFiniteSum.rho 0 s ((X : ℚ[X]) ^ 4) = 0 := by
  have hindex : 9-s ≠ 8 := by omega
  unfold ZetaNine.CoefficientMapFiniteSum.rho
  rw [Finset.sum_range_one,ZetaNine.CoefficientMapJet.weightedLocalCoefficient,agg_ind_n_zero_series]
  simp only [Polynomial.pow_comp,Polynomial.X_comp,map_pow,Polynomial.coe_X]
  rw [← pow_mul]
  norm_num [PowerSeries.coeff_X_pow,hindex,Ne.symm hindex]

theorem agg_ind_n_zero_X_four_F_zero : aggregate 0 ((X : ℚ[X]) ^ 4) = 0 := by
  funext i
  fin_cases i
  · exact agg_ind_n_zero_harmonic_constant _
  all_goals exact agg_ind_n_zero_X_four_odd_rho _ (by omega) (by omega)

theorem agg_ind_n_zero_X_four_rho1 : ZetaNine.CoefficientMapFiniteSum.rho 0 1 ((X : ℚ[X]) ^ 4) = 1 := by
  unfold ZetaNine.CoefficientMapFiniteSum.rho
  rw [Finset.sum_range_one,ZetaNine.CoefficientMapJet.weightedLocalCoefficient,agg_ind_n_zero_series]
  simp only [Polynomial.pow_comp,Polynomial.X_comp,map_pow,Polynomial.coe_X]
  rw [← pow_mul]
  norm_num

theorem agg_ind_n_zero_X_four_proper_not_strong :
    ProperMultiplier 0 ((X : ℚ[X]) ^ 4) ∧ ¬ StrongProperMultiplier 0 ((X : ℚ[X]) ^ 4) := by
  norm_num [ProperMultiplier,StrongProperMultiplier,Polynomial.natDegree_pow]

theorem agg_ind_n_zero_actual_F_not_injective : ¬ Function.Injective (aggregate 0) := by
  intro h
  have hz : (X : ℚ[X]) ^ 4 = 0 := h (agg_ind_n_zero_X_four_F_zero.trans (agg_ind_zero_all_n 0).symm)
  exact pow_ne_zero 4 X_ne_zero hz

theorem agg_ind_n_zero_quartic_F_nonzero_kernel :
    quarticAggregateLinearMap 0 (Pi.single (4 : Fin 5) (1 : ℚ)) = 0 ∧
      (Pi.single (4 : Fin 5) (1 : ℚ) : Fin 5 → ℚ) ≠ 0 := by
  constructor
  · rw [quartic_aggregate_is_actual,agg_ind_basis]
    exact agg_ind_n_zero_X_four_F_zero
  · intro h
    have hh := congrFun h (4 : Fin 5)
    norm_num at hh

theorem agg_ind_n_zero_X_three_output : aggregate 0 ((X : ℚ[X]) ^ 3) = Pi.single (1 : Fin 5) (1 : ℚ) := by
  funext i
  fin_cases i <;>
    norm_num [aggregate,ZetaNine.CoefficientMapFiniteSum.constantTerm,ZetaNine.HarmonicStability.harmonicPower,
      ZetaNine.CoefficientMapFiniteSum.rho,ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
      agg_ind_n_zero_series,Polynomial.pow_comp,Polynomial.X_comp,Polynomial.coe_pow,Polynomial.coe_X,
      ← pow_mul]

theorem agg_ind_n_zero_X_four_actual_sequence (k : ℕ) :
    actualSeries 0 ((X : ℚ[X]) ^ 4) k = 1 / ((k : ℝ)+1) := by
  have ht : ((k+1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hQ : ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 4) ((k+1 : ℕ) : ℚ) =
      1 / ((k+1 : ℕ) : ℚ) := by
    simp [ZetaNine.CoefficientMap.weightedR,ZetaNine.CoefficientMap.actualR,
      ZetaNine.CoefficientMap.numerator,ZetaNine.CoefficientMap.poleProduct]
    field_simp
  unfold actualSeries
  rw [hQ]
  push_cast
  rfl

theorem agg_ind_n_zero_F_zero_does_not_give_HasSum (L : ℝ) :
    aggregate 0 ((X : ℚ[X]) ^ 4) = 0 ∧ ¬ HasSum (actualSeries 0 ((X : ℚ[X]) ^ 4)) L := by
  refine ⟨agg_ind_n_zero_X_four_F_zero,?_⟩
  intro h
  have hshift : Summable (fun k : ℕ => 1 / ((k+1 : ℕ) : ℝ)) :=
    h.summable.congr (fun k => by simpa only [Nat.cast_add,Nat.cast_one] using agg_ind_n_zero_X_four_actual_sequence k)
  have hall : Summable (fun k : ℕ => 1 / (k : ℝ)) :=
    (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ)) 1).mp hshift
  exact Real.not_summable_one_div_natCast hall

run_meta do
  let emit (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let val ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("axioms",toJson (axs.toList.map Name.toString)),("definitionValue",val)]).compress
  for name in [
    `agg_ind_actual_B_negative_harmonic,`agg_ind_actual_five_odd_coordinates,`agg_ind_general_rational_linearity,
    `agg_ind_zero_all_n,`agg_ind_coordinate_zero,`agg_ind_roundtrip_zero,`agg_ind_roundtrip_nonmonic,
    `agg_ind_basis,`agg_ind_quartic_restoration_kernel,`agg_ind_hasSum_zero_strong_even,
    `agg_ind_all_rho_zero_strong_even,`agg_ind_n_zero_series,`agg_ind_n_zero_harmonic_constant,
    `agg_ind_n_zero_X_four_odd_rho,`agg_ind_n_zero_X_four_F_zero,`agg_ind_n_zero_X_four_rho1,
    `agg_ind_n_zero_X_four_proper_not_strong,`agg_ind_n_zero_actual_F_not_injective,
    `agg_ind_n_zero_quartic_F_nonzero_kernel,`agg_ind_n_zero_X_three_output,
    `agg_ind_n_zero_X_four_actual_sequence,`agg_ind_n_zero_F_zero_does_not_give_HasSum] do emit name
