import missions.zeta9.formalization.CoefficientMapKernelBridge
import Lean
open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapKernelBridge
set_option pp.fullNames true
set_option pp.universes false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem checked_actual_five_zero_coordinates_force_quartic_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4)
    (hB : ZetaNine.CoefficientMapFiniteSum.constantTerm n W = 0)
    (h3 : ZetaNine.CoefficientMapFiniteSum.rho n 3 W = 0)
    (h5 : ZetaNine.CoefficientMapFiniteSum.rho n 5 W = 0)
    (h7 : ZetaNine.CoefficientMapFiniteSum.rho n 7 W = 0)
    (h9 : ZetaNine.CoefficientMapFiniteSum.rho n 9 W = 0) : W = 0 :=
  original_quartic_aggregate_kernel_zero n hn2 hn W hW
    ((aggregate_zero_iff n W).mpr ⟨hB, h3, h5, h7, h9⟩)

theorem checked_nonzero_pure_zeta_nine_rational_lift (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    ∃ W : ℚ[X], W.natDegree ≤ 4 ∧ W ≠ 0 ∧
      aggregate n W = Pi.single (4 : Fin 5) (1 : ℚ) ∧
      HasSum (fun t : ℕ => (ZetaNine.CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ))
        (riemannZeta (9 : ℂ)).re ∧
      Summable (fun t : ℕ => ‖(ZetaNine.CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ)‖) := by
  let b : Fin 5 → ℚ := Pi.single 4 1
  have hb : b ≠ 0 := by
    intro h
    have he := congrFun h (4 : Fin 5)
    norm_num [b] at he
  have h := inverseMultiplier_actual_HasSum_and_absolute n hn2 hn b
  have hL : prescribedL b = (riemannZeta (9 : ℂ)).re := by
    simp [prescribedL, b, ZetaNine.CoefficientMapSummation.zetaReal]
  rw [hL] at h
  exact ⟨inverseMultiplier n hn2 hn b, inverseMultiplier_natDegree_le n hn2 hn b,
    inverseMultiplier_nonzero_of_output_nonzero n hn2 hn b hb,
    inverseMultiplier_actual_aggregate n hn2 hn b, h⟩

theorem checked_unique_integer_output_rational_lift (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℤ) : ∃! W : {W : ℚ[X] // W.natDegree ≤ 4}, aggregate n W.val = fun i => (b i : ℚ) :=
  every_exact_formal_output_has_unique_quartic n hn2 hn _

theorem checked_original_integer_quartic_injectivity (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W V : ℤ[X]) (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (heq : aggregate n (W.map (Int.castRingHom ℚ)) = aggregate n (V.map (Int.castRingHom ℚ))) :
    W.map (Int.castRingHom ℚ) = V.map (Int.castRingHom ℚ) :=
  original_quartic_aggregate_injective n hn2 hn _ _
    (le_trans Polynomial.natDegree_map_le hW) (le_trans Polynomial.natDegree_map_le hV) heq

theorem checked_actual_R_shift_ratio_right (n : ℕ) (t : ℚ) (ht : (n : ℚ) + 1 < t) :
    ZetaNine.CoefficientMap.actualR n (t + 1) / ZetaNine.CoefficientMap.actualR n t = bValue n t / aValue n (t + 1) := by
  have ht0 : (0 : ℚ) < t := by have hnn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n; linarith
  have hr : ∀ k ≤ n, t + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht0 (Nat.cast_nonneg k))
  have hr1 : ∀ k ≤ n, (t + 1) + (k : ℚ) ≠ 0 := by intro k hk; exact ne_of_gt (by positivity)
  have hR : ZetaNine.CoefficientMap.actualR n t ≠ 0 := actual_R_ne_zero_above_n n t (by linarith)
  have hA : aValue n (t + 1) ≠ 0 := by
    unfold aValue
    apply mul_ne_zero
    · exact ne_of_gt (by linarith)
    · apply pow_ne_zero
      exact ne_of_gt (by positivity)
  apply (div_eq_div_iff hR hA).mpr
  simpa only [mul_comm] using actual_R_shift_A_equals_R_B n t hr hr1

theorem checked_derived_inverse_both_laws (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (a b : Fin 5 → ℚ) :
    quarticAggregateLinearMap n ((actualAggregateEquiv n hn2 hn).symm b) = b ∧
      (actualAggregateEquiv n hn2 hn).symm (quarticAggregateLinearMap n a) = a :=
  ⟨(actualAggregateEquiv n hn2 hn).apply_symm_apply b, (actualAggregateEquiv n hn2 hn).symm_apply_apply a⟩

theorem checked_explicit_prescribed_L_absolute_HasSum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    HasSum (fun t : ℕ => (ZetaNine.CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ))
      ((b 0 : ℝ) + ((b 1 : ℝ) * (riemannZeta (3 : ℂ)).re +
        (b 2 : ℝ) * (riemannZeta (5 : ℂ)).re + (b 3 : ℝ) * (riemannZeta (7 : ℂ)).re +
        (b 4 : ℝ) * (riemannZeta (9 : ℂ)).re)) ∧
    Summable (fun t : ℕ => ‖(ZetaNine.CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖) := by
  simpa only [prescribedL, ZetaNine.CoefficientMapSummation.zetaReal, Nat.cast_ofNat] using
    inverseMultiplier_actual_HasSum_and_absolute n hn2 hn b

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
    `ZetaNine.CoefficientMapKernelBridge.positiveProduct,
    `ZetaNine.CoefficientMapKernelBridge.negativeProduct,
    `ZetaNine.CoefficientMapKernelBridge.aValue,
    `ZetaNine.CoefficientMapKernelBridge.bValue,
    `ZetaNine.CoefficientMapKernelBridge.finite_product_shift_identity,
    `ZetaNine.CoefficientMapKernelBridge.positiveProduct_shift,
    `ZetaNine.CoefficientMapKernelBridge.negativeProduct_shift,
    `ZetaNine.CoefficientMapKernelBridge.numerator_shift_identity,
    `ZetaNine.CoefficientMapKernelBridge.poleProduct_shift_identity,
    `ZetaNine.CoefficientMapKernelBridge.actual_R_shift_A_equals_R_B,
    `ZetaNine.CoefficientMapKernelBridge.rootPolynomial_numerator_factor,
    `ZetaNine.CoefficientMapKernelBridge.poleProduct_last_factor,
    `ZetaNine.CoefficientMapKernelBridge.actual_R_A_equals_Pzero,
    `ZetaNine.CoefficientMapKernelBridge.telescoper_quotient_as_R_A,
    `ZetaNine.CoefficientMapKernelBridge.actual_R_ne_zero_above_n,
    `ZetaNine.CoefficientMapKernelBridge.kernel_actual_polynomial_relation,
    `ZetaNine.CoefficientMapKernelBridge.original_quartic_aggregate_kernel_zero,
    `ZetaNine.CoefficientMapKernelBridge.original_quartic_aggregate_injective,
    `ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_injective,
    `ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_bijective,
    `ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv,
    `ZetaNine.CoefficientMapKernelBridge.every_exact_formal_output_has_unique_quartic,
    `ZetaNine.CoefficientMapKernelBridge.inverseMultiplier,
    `ZetaNine.CoefficientMapKernelBridge.prescribedL,
    `ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_natDegree_le,
    `ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_actual_aggregate,
    `ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_unique,
    `ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_nonzero_of_output_nonzero,
    `ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_exact_L,
    `ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_actual_HasSum_and_absolute,
    `checked_actual_five_zero_coordinates_force_quartic_zero,
    `checked_nonzero_pure_zeta_nine_rational_lift,
    `checked_unique_integer_output_rational_lift,
    `checked_original_integer_quartic_injectivity,
    `checked_actual_R_shift_ratio_right,
    `checked_derived_inverse_both_laws,
    `checked_explicit_prescribed_L_absolute_HasSum] do emit name
