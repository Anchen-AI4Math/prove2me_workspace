import missions.zeta9.formalization.CoefficientMapKernelBridge
import Lean
open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapAggregate
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapTelescoper
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false
noncomputable section

namespace IndependentKernel

theorem actual_A_B_definitions (n : ℕ) (t : ℚ) :
    aValue n t = (t - (n : ℚ) - 1) * (t + (n : ℚ)) ^ 10 ∧
      bValue n t = t ^ 10 * (t + 2 * (n : ℚ) + 1) := ⟨rfl,rfl⟩

theorem concrete_R_A_B_shift :
    ZetaNine.CoefficientMap.actualR 2 5 * ((5 - 2 - 1 : ℚ) * (5 + 2) ^ 10) =
      ZetaNine.CoefficientMap.actualR 2 4 * ((4 : ℚ) ^ 10 * (4 + 2 * 2 + 1)) := by
  norm_num [ZetaNine.CoefficientMap.actualR, ZetaNine.CoefficientMap.numerator,
    ZetaNine.CoefficientMap.poleProduct, Finset.prod_range_succ]

theorem true_R_A_factor (n : ℕ) (hn : 1 ≤ n) (t : ℚ)
    (hr : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.actualR n t * ((t - (n : ℚ) - 1) * (t + (n : ℚ)) ^ 10) =
      (n.factorial : ℚ) ^ 7 * (rootPolynomial n).eval t /
        (polePolynomial (n - 1)).eval t ^ 9 := actual_R_A_equals_Pzero n hn t hr

theorem actual_polynomial_bridge_no_supplied_shift_relation (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n)
    (W H : ℚ[X]) (hs : StrongProperMultiplier n W) (hz : aggregate n W = 0)
    (hH : telescoperNumerator n W = rootPolynomial n * H) :
    C ((n.factorial : ℚ) ^ 7) * W.comp (X * (X + C (n : ℚ))) =
      ((X - C ((n : ℚ) + 1)) * (X + C (n : ℚ)) ^ 10) * H -
        (X ^ 10 * (X + C (2 * (n : ℚ) + 1))) * H.comp (X + 1) := by
  simpa only [baseU, map_one] using kernel_actual_polynomial_relation n hn1 hn W H hs hz hH

theorem genuine_kernel_from_five_raw_entries (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hd : W.natDegree ≤ 4)
    (hb : ZetaNine.CoefficientMapFiniteSum.constantTerm n W = 0)
    (h3 : ZetaNine.CoefficientMapFiniteSum.rho n 3 W = 0)
    (h5 : ZetaNine.CoefficientMapFiniteSum.rho n 5 W = 0)
    (h7 : ZetaNine.CoefficientMapFiniteSum.rho n 7 W = 0)
    (h9 : ZetaNine.CoefficientMapFiniteSum.rho n 9 W = 0) : W = 0 := by
  exact original_quartic_aggregate_kernel_zero n hn2 hn W hd
    ((aggregate_zero_iff n W).mpr ⟨hb,h3,h5,h7,h9⟩)

theorem concrete_n_two_bijective : Function.Bijective (quarticAggregateLinearMap 2) :=
  original_five_dimensional_map_bijective 2 (by omega) (by norm_num)

theorem actual_equiv_toFun (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (a : Fin 5 → ℚ) :
    actualAggregateEquiv n hn2 hn a = aggregate n (coordinatePolynomial a) := rfl

theorem inverse_both_actual_coordinate_laws (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (a b : Fin 5 → ℚ) :
    aggregate n (coordinatePolynomial ((actualAggregateEquiv n hn2 hn).symm b)) = b ∧
      (actualAggregateEquiv n hn2 hn).symm (aggregate n (coordinatePolynomial a)) = a :=
  ⟨(actualAggregateEquiv n hn2 hn).apply_symm_apply b,
    (actualAggregateEquiv n hn2 hn).symm_apply_apply a⟩

theorem inverse_zero_exact (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    inverseMultiplier n hn2 hn 0 = 0 := by
  apply original_quartic_aggregate_kernel_zero n hn2 hn _
    (inverseMultiplier_natDegree_le n hn2 hn 0)
  exact inverseMultiplier_actual_aggregate n hn2 hn 0

theorem inverse_add_actual (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (a b : Fin 5 → ℚ) :
    inverseMultiplier n hn2 hn (a + b) = inverseMultiplier n hn2 hn a + inverseMultiplier n hn2 hn b := by
  unfold inverseMultiplier
  rw [map_add, coordinatePolynomial_add]

theorem inverse_smul_actual (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (c : ℚ) (b : Fin 5 → ℚ) :
    inverseMultiplier n hn2 hn (c • b) = c • inverseMultiplier n hn2 hn b := by
  unfold inverseMultiplier
  rw [map_smul, coordinatePolynomial_smul]

theorem all_five_inverse_outputs (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    ZetaNine.CoefficientMapFiniteSum.constantTerm n (inverseMultiplier n hn2 hn b) = b 0 ∧
      ZetaNine.CoefficientMapFiniteSum.rho n 3 (inverseMultiplier n hn2 hn b) = b 1 ∧
      ZetaNine.CoefficientMapFiniteSum.rho n 5 (inverseMultiplier n hn2 hn b) = b 2 ∧
      ZetaNine.CoefficientMapFiniteSum.rho n 7 (inverseMultiplier n hn2 hn b) = b 3 ∧
      ZetaNine.CoefficientMapFiniteSum.rho n 9 (inverseMultiplier n hn2 hn b) = b 4 := by
  have h := inverseMultiplier_actual_aggregate n hn2 hn b
  exact ⟨congrFun h 0,congrFun h 1,congrFun h 2,congrFun h 3,congrFun h 4⟩

theorem prescribed_target_actual_HasSum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    HasSum (fun k : ℕ => (ZetaNine.CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((k + 1 : ℕ) : ℚ) : ℝ))
      ((b 0 : ℝ) + ((b 1 : ℝ) * (riemannZeta (3 : ℂ)).re +
        (b 2 : ℝ) * (riemannZeta (5 : ℂ)).re + (b 3 : ℝ) * (riemannZeta (7 : ℂ)).re +
        (b 4 : ℝ) * (riemannZeta (9 : ℂ)).re)) := by
  simpa only [prescribedL, ZetaNine.CoefficientMapSummation.zetaReal, Nat.cast_ofNat] using
    (inverseMultiplier_actual_HasSum_and_absolute n hn2 hn b).1

theorem prescribed_target_absolute_sum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    Summable (fun k : ℕ => ‖(ZetaNine.CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((k + 1 : ℕ) : ℚ) : ℝ)‖) :=
  (inverseMultiplier_actual_HasSum_and_absolute n hn2 hn b).2

theorem pure_zeta_nine_nonzero_rational_quartic (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    ∃ W : ℚ[X], W.natDegree ≤ 4 ∧ W ≠ 0 ∧
      aggregate n W = Pi.single (4 : Fin 5) (1 : ℚ) ∧
      HasSum (fun k : ℕ => (ZetaNine.CoefficientMap.weightedR n W ((k + 1 : ℕ) : ℚ) : ℝ))
        (riemannZeta (9 : ℂ)).re ∧
      Summable (fun k : ℕ => ‖(ZetaNine.CoefficientMap.weightedR n W ((k + 1 : ℕ) : ℚ) : ℝ)‖) := by
  let b : Fin 5 → ℚ := Pi.single 4 1
  have hb : b ≠ 0 := by intro hz; have h := congrFun hz (4 : Fin 5); norm_num [b] at h
  have h := inverseMultiplier_actual_HasSum_and_absolute n hn2 hn b
  have hl : prescribedL b = (riemannZeta (9 : ℂ)).re := by
    simp [prescribedL,b,ZetaNine.CoefficientMapSummation.zetaReal]
  rw [hl] at h
  exact ⟨inverseMultiplier n hn2 hn b,inverseMultiplier_natDegree_le n hn2 hn b,
    inverseMultiplier_nonzero_of_output_nonzero n hn2 hn b hb,
    inverseMultiplier_actual_aggregate n hn2 hn b,h⟩

theorem integer_outputs_have_unique_rational_quartic (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℤ) : ∃! W : {W : ℚ[X] // W.natDegree ≤ 4},
      aggregate n W.val = fun i => (b i : ℚ) := every_exact_formal_output_has_unique_quartic n hn2 hn _

theorem original_integer_coefficients_injectivity (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W V : ℤ[X]) (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (heq : aggregate n (W.map (Int.castRingHom ℚ)) = aggregate n (V.map (Int.castRingHom ℚ))) :
    W.map (Int.castRingHom ℚ) = V.map (Int.castRingHom ℚ) :=
  original_quartic_aggregate_injective n hn2 hn _ _
    (le_trans Polynomial.natDegree_map_le hW) (le_trans Polynomial.natDegree_map_le hV) heq

theorem zero_n_nonzero_quartic_aggregate_kernel :
    aggregate 0 (X ^ 4 : ℚ[X]) = 0 ∧ (X ^ 4 : ℚ[X]) ≠ 0 := by
  constructor
  · funext i
    fin_cases i <;> norm_num [aggregate,ZetaNine.CoefficientMapFiniteSum.constantTerm,
      ZetaNine.CoefficientMapFiniteSum.rho,ZetaNine.HarmonicStability.harmonicPower,
      weightedLocalCoefficient,weightedClearedSeries,clearedSeries,shiftedNumerator,
      shiftedClearedDenominator,localU,shiftedVariable,Polynomial.pow_comp,Polynomial.X_comp,
      Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_X,←pow_two,←pow_mul]
  · exact pow_ne_zero 4 X_ne_zero

theorem zero_n_aggregate_quartic_not_injective : ¬Function.Injective (quarticAggregateLinearMap 0) := by
  intro hi
  let a : Fin 5 → ℚ := Pi.single 4 1
  have hp : coordinatePolynomial a = (X ^ 4 : ℚ[X]) := by
    classical
    unfold coordinatePolynomial a
    rw [Finset.sum_eq_single (4 : Fin 5)]
    · simp
    · intro j hj hji; simp [hji]
    · simp
  have hf : quarticAggregateLinearMap 0 a = quarticAggregateLinearMap 0 0 := by
    rw [quartic_aggregate_is_actual, hp, zero_n_nonzero_quartic_aggregate_kernel.1, map_zero]
  have h := congrFun (hi hf) (4 : Fin 5)
  norm_num [a] at h

theorem excluded_n_zero_and_odd_one : ¬(2 ≤ (0 : ℕ)) ∧ ¬Even (1 : ℕ) := by norm_num

end IndependentKernel

run_meta do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    if name.toString.startsWith "ZetaNine.CoefficientMapKernelBridge." ||
        name.toString.startsWith "IndependentKernel." then
      let suffix := name.toString.splitOn "." |>.getLast!
      if suffix.startsWith "_" then continue
      match ci with
      | .defnInfo _ | .thmInfo _ =>
        let typ ← ppExpr ci.type
        let axs ← Lean.collectAxioms name
        let value ← match ci with
          | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
          | _ => pure Json.null
        IO.println (Json.mkObj [("declaration",Json.str name.toString),("type",Json.str typ.pretty),
          ("axioms",toJson (axs.toList.map Name.toString)),("definitionValue",value)]).compress
      | _ => pure ()
