import Solutions.Sol_ZetaNine_CoefficientMapInjectivity_quartic_is_proper
import Lean

open Lean Meta Polynomial
open scoped BigOperators
open ZetaNine.CoefficientMapInjectivity
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

-- Independent exact domain and indexing checks, without aggregate outputs.
theorem independent_closed_zero_kernel (n : ℕ) (W : ℚ[X])
    (hp : 2 * n + 2 * W.natDegree < 9 * (n + 1))
    (hz : ∀ j ≤ n, ∀ s, 1 ≤ s → s ≤ 9 →
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W = 0) : W = 0 :=
  all_local_coefficients_zero_implies_zero n W hp hz

theorem independent_closed_array_injective (n : ℕ) :
    Function.Injective (fun W : {W : ℚ[X] // 2 * n + 2 * W.natDegree < 9 * (n + 1)} =>
      fun (j : Fin (n + 1)) (s : Fin 9) =>
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j.val (s.val + 1) W.val) :=
  fullLocalCoefficientMap_injective n

theorem independent_difference_proper (n : ℕ) (W V : ℚ[X])
    (hW : ProperMultiplier n W) (hV : ProperMultiplier n V) :
    ProperMultiplier n (W - V) := by
  have hdeg := Polynomial.natDegree_sub_le W V
  unfold ProperMultiplier at *
  rcases le_total W.natDegree V.natDegree with h | h
  · rw [max_eq_right h] at hdeg
    omega
  · rw [max_eq_left h] at hdeg
    omega

theorem independent_quartic_array (n : ℕ) (W V : ℚ[X])
    (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (h : fullLocalCoefficientMap n W = fullLocalCoefficientMap n V) : W = V := by
  have inj := independent_closed_array_injective n
  have heq := inj (a₁ := ⟨W, checked_quartic_is_proper n W hW⟩)
    (a₂ := ⟨V, checked_quartic_is_proper n V hV⟩) h
  exact congrArg Subtype.val heq

theorem independent_original_integer_quartic (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n)
    (W V : ℤ[X]) (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (h : fullLocalCoefficientMap n (W.map (Int.castRingHom ℚ)) =
      fullLocalCoefficientMap n (V.map (Int.castRingHom ℚ))) : W = V := by
  have heq := independent_quartic_array n (W.map (Int.castRingHom ℚ))
    (V.map (Int.castRingHom ℚ))
    (le_trans Polynomial.natDegree_map_le hW)
    (le_trans Polynomial.natDegree_map_le hV) h
  exact Polynomial.map_injective (Int.castRingHom ℚ)
    (by intro a b hab; exact Int.cast_injective hab) heq

theorem independent_n_zero_array (W V : ℚ[X]) (hW : W.natDegree ≤ 4)
    (hV : V.natDegree ≤ 4) (h : fullLocalCoefficientMap 0 W = fullLocalCoefficientMap 0 V) :
    W = V := independent_quartic_array 0 W V hW hV h

theorem independent_actual_rational_representation (n : ℕ) (W : ℚ[X]) (t : ℚ) :
    (weightedNumerator n W).eval t / ((polePolynomial n).eval t) ^ 9 =
      ZetaNine.CoefficientMap.weightedR n W t := by
  simp only [weightedNumerator, Polynomial.eval_mul, Polynomial.eval_comp,
    baseNumerator_eval, baseU, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C,
    polePolynomial, Polynomial.eval_prod, ZetaNine.CoefficientMap.weightedR,
    ZetaNine.CoefficientMap.actualR, ZetaNine.CoefficientMap.poleProduct]
  ring

-- The zero-polynomial case does not invoke degree divisibility on a zero RHS.
theorem independent_zero_multiplier_proper (n : ℕ) : ProperMultiplier n (0 : ℚ[X]) := by
  unfold ProperMultiplier
  simp only [Polynomial.natDegree_zero]
  omega

theorem independent_n_zero_series (W : ℚ[X]) :
    ZetaNine.CoefficientMapJet.weightedClearedSeries 0 0 W =
      (W.comp ((X : ℚ[X]) ^ 2) : PowerSeries ℚ) := by
  have hs : ZetaNine.CoefficientMapJet.clearedSeries 0 0 = 1 := by
    simp [ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator,
      ZetaNine.CoefficientMapJet.shiftedClearedDenominator]
  have hu : ZetaNine.CoefficientMapJet.localU 0 0 = (X : ℚ[X]) ^ 2 := by
    simp [ZetaNine.CoefficientMapJet.localU,
      ZetaNine.CoefficientMapJet.shiftedVariable, pow_two]
  simp only [ZetaNine.CoefficientMapJet.weightedClearedSeries, hs, hu, one_mul]

theorem independent_n_zero_quartic_proper : ProperMultiplier 0 ((X : ℚ[X]) ^ 4) := by
  norm_num [ProperMultiplier, Polynomial.natDegree_pow]

theorem independent_n_zero_nonzero_simple_pole :
    ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 0 1 ((X : ℚ[X]) ^ 4) = 1 := by
  rw [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, independent_n_zero_series]
  simp only [Polynomial.pow_comp, Polynomial.X_comp, map_pow, Polynomial.coe_X]
  rw [← pow_mul]
  norm_num

theorem independent_n_zero_quartic_no_two_degree_gap :
    ¬ (2 * 0 + 2 * ((X : ℚ[X]) ^ 4).natDegree + 2 ≤ 9 * (0 + 1)) := by
  norm_num [Polynomial.natDegree_pow]

theorem independent_n_zero_actual_simple_pole (t : ℚ) (ht : t ≠ 0) :
    ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 4) t = 1 / t := by
  simp [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct,
    Finset.prod_range_succ]
  field_simp

-- Dropping the degree condition is genuinely false: a polynomial part has no poles.
theorem independent_n_zero_nonproper_kernel :
    AllLocalCoefficientsZero 0 ((X : ℚ[X]) ^ 5) := by
  intro j hj s hs1 hs9
  have hj0 : j = 0 := by omega
  subst j
  have hindex : 9 - s ≠ 10 := by omega
  rw [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, independent_n_zero_series]
  simp only [Polynomial.pow_comp, Polynomial.X_comp, map_pow, Polynomial.coe_X]
  rw [← pow_mul]
  norm_num [PowerSeries.coeff_X_pow, hindex, Ne.symm hindex]

theorem independent_n_zero_nonproper_nonzero : (X : ℚ[X]) ^ 5 ≠ 0 :=
  pow_ne_zero _ Polynomial.X_ne_zero

theorem independent_n_zero_nonproper_bound : ¬ ProperMultiplier 0 ((X : ℚ[X]) ^ 5) := by
  norm_num [ProperMultiplier, Polynomial.natDegree_pow]

run_meta do
  let emit (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let value ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString)),
      ("definitionValue", value)]).compress
  for name in [
    `ZetaNine.CoefficientMapInjectivity.baseNumerator,
    `ZetaNine.CoefficientMapInjectivity.baseU,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator,
    `ZetaNine.CoefficientMapInjectivity.polePolynomial,
    `ZetaNine.CoefficientMapInjectivity.AllLocalCoefficientsZero,
    `ZetaNine.CoefficientMapInjectivity.ProperMultiplier,
    `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap,
    `ZetaNine.CoefficientMapInjectivity.baseNumerator_eval,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator_shift,
    `ZetaNine.CoefficientMapInjectivity.zero_local_jet_implies_shifted_numerator_divisibility,
    `ZetaNine.CoefficientMapInjectivity.zero_local_jet_implies_pole_divisibility,
    `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime,
    `ZetaNine.CoefficientMapInjectivity.all_zero_jets_imply_full_denominator_divisibility,
    `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree,
    `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree,
    `ZetaNine.CoefficientMapInjectivity.baseU_natDegree,
    `ZetaNine.CoefficientMapInjectivity.baseNumerator_ne_zero,
    `ZetaNine.CoefficientMapInjectivity.baseNumerator_natDegree_le,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator_natDegree_le,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator_zero_implies_multiplier_zero,
    `ZetaNine.CoefficientMapInjectivity.all_local_coefficients_zero_implies_zero,
    `ZetaNine.CoefficientMapInjectivity.weightedLocalCoefficient_sub,
    `ZetaNine.CoefficientMapInjectivity.local_coefficients_injective,
    `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap_injective,
    `ZetaNine.CoefficientMapInjectivity.checked_quartic_is_proper,
    `independent_closed_zero_kernel, `independent_closed_array_injective,
    `independent_difference_proper, `independent_quartic_array,
    `independent_original_integer_quartic, `independent_n_zero_array,
    `independent_actual_rational_representation, `independent_zero_multiplier_proper,
    `independent_n_zero_series, `independent_n_zero_quartic_proper,
    `independent_n_zero_nonzero_simple_pole, `independent_n_zero_quartic_no_two_degree_gap,
    `independent_n_zero_actual_simple_pole, `independent_n_zero_nonproper_kernel,
    `independent_n_zero_nonproper_nonzero, `independent_n_zero_nonproper_bound] do emit name
