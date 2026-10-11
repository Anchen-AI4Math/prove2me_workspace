import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapNumeratorPartialFractions

theorem checked_exact_generic_polynomial_endpoint (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) : A = numeratorPartialNumerator m A :=
  actual_numerator_polynomial_partial_fractions m A hproper

theorem checked_exact_generic_regular_point_endpoint (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) (t : ℚ)
    (hregular : ∀ k ≤ m, t + (k : ℚ) ≠ 0) :
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s :=
  actual_numerator_global_partial_fractions m A hproper t hregular

theorem checked_exact_generic_actual_jet_injectivity (m : ℕ) (A B : ℚ[X])
    (hA : A.natDegree < 9 * (m + 1)) (hB : B.natDegree < 9 * (m + 1))
    (hjets : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) : A = B :=
  actual_numerator_local_coefficients_injective m A B hA hB hjets

theorem checked_zero_actual_jet (m j s : ℕ) : numeratorLocalCoefficient m j s (0 : ℚ[X]) = 0 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries]

theorem checked_zero_numerator_reconstruction (m : ℕ) :
    (0 : ℚ[X]) = numeratorPartialNumerator m 0 :=
  actual_numerator_polynomial_partial_fractions m 0 (by simp)

theorem checked_m0_Aone_reconstruction : (1 : ℚ[X]) = numeratorPartialNumerator 0 1 :=
  actual_numerator_polynomial_partial_fractions 0 1 (by norm_num)

theorem checked_m0_critical_X8_reconstruction : (X ^ 8 : ℚ[X]) = numeratorPartialNumerator 0 (X ^ 8) :=
  actual_numerator_polynomial_partial_fractions 0 (X ^ 8) (by norm_num)

theorem checked_m0_X9_is_excluded : ¬ (X ^ 9 : ℚ[X]).natDegree < 9 * (0 + 1) := by norm_num

theorem checked_m0_highest_pole_of_one : numeratorLocalCoefficient 0 0 9 (1 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.shiftedVariable]

theorem checked_m0_simple_pole_of_X8 : numeratorLocalCoefficient 0 0 1 (X ^ 8 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.shiftedVariable]

theorem checked_m0_simple_pole_regular_PF (t : ℚ) (ht : t ≠ 0) :
    (1 : ℚ) / t = ∑ j ∈ range (0 + 1), ∑ s ∈ Icc 1 9,
      numeratorLocalCoefficient 0 j s (X ^ 8 : ℚ[X]) / (t + (j : ℚ)) ^ s := by
  have h := actual_numerator_global_partial_fractions 0 (X ^ 8) (by norm_num) t
    (by
      intro k hk
      have hk0 : k = 0 := by omega
      simpa only [hk0, Nat.cast_zero, add_zero] using ht)
  have he : (X ^ 8 : ℚ[X]).eval t / (polePolynomial 0).eval t ^ 9 = (1 : ℚ) / t := by
    have hp : (polePolynomial 0).eval t = t := by simp [polePolynomial]
    rw [hp]
    simp only [eval_pow, eval_X]
    field_simp [ht] <;> ring
  rw [he] at h
  exact h

theorem checked_two_pole_constant_reconstruction : (1 : ℚ[X]) = numeratorPartialNumerator 1 1 :=
  actual_numerator_polynomial_partial_fractions 1 1 (by norm_num)

theorem checked_actual_weighted_jets_agree (m j s : ℕ) (W : ℚ[X]) :
    numeratorLocalCoefficient m j s (weightedNumerator m W) =
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient m j s W :=
  numerator_local_coefficient_weighted_agreement m j s W

theorem checked_n1_q1_actual_shifted_remainder :
    shiftedRemainderNumerator 1 (1 : ℚ[X]) = (X + 1) ^ 2 - 4 := by
  norm_num [shiftedRemainderNumerator, remainderNumerator, Finset.prod_range_succ,
    Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, map_ofNat] <;> ring

theorem checked_n1_q1_actual_remainder_reconstruction :
    shiftedRemainderNumerator 1 (1 : ℚ[X]) =
      numeratorPartialNumerator 2 (shiftedRemainderNumerator 1 (1 : ℚ[X])) := by
  apply actual_numerator_polynomial_partial_fractions
  rw [checked_n1_q1_actual_shifted_remainder]
  have hd := Polynomial.natDegree_sub_le ((X + 1) ^ 2 : ℚ[X]) (4 : ℚ[X])
  have hf : ((X + 1) ^ 2 : ℚ[X]).natDegree = 2 := by
    rw [Polynomial.natDegree_pow]
    have hx : (X + 1 : ℚ[X]).natDegree = 1 := by
      simpa using Polynomial.natDegree_X_add_C (1 : ℚ)
    rw [hx]
  have hc : (4 : ℚ[X]).natDegree = 0 := by norm_num
  rw [hf, hc] at hd
  omega

-- Own author runtime full Expr audit; helper source copied and hash-bound, no objects borrowed.
-- The caller supplies imports and constant lists from frozen inputs plus actual
-- official graph/parser facts. PP is diagnostic, never the kernel equality gate.
open Lean Meta
set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true

private def emitIndependentDefinition (name : Name) : MetaM Unit := do
  let .defnInfo d ← getConstInfo name | throwError "Expected an actual definition: {name}"
  let typ ← ppExpr d.type
  let val ← ppExpr d.value
  let axs ← Lean.collectAxioms name
  IO.println (Json.mkObj [("kind",Json.str "definition_full_expression"),
    ("declaration",Json.str name.toString),
    ("level_parameters",toJson (d.levelParams.map Name.toString)),
    ("type_expression_repr",Json.str (reprStr d.type)),
    ("full_value_expression_repr",Json.str (reprStr d.value)),
    ("type_pp_diagnostic",Json.str typ.pretty),
    ("value_pp_with_proofs_diagnostic",Json.str val.pretty),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def checkIndependentNativeAlias (name aliasName : Name) : MetaM Unit := do
  let .defnInfo d ← getConstInfo name | throwError "Expected native definition"
  let .defnInfo a ← getConstInfo aliasName | throwError "Expected actual staged-byte alias definition"
  let typeEq ← isDefEq d.type a.type
  let fullValueEq ← isDefEq d.value a.value
  unless typeEq && fullValueEq do
    throwError "Whole definition kernel equality failed: {name} / {aliasName}"
  let axs ← Lean.collectAxioms aliasName
  IO.println (Json.mkObj [("kind",Json.str "native_alias_whole_value_kernel"),
    ("declaration",Json.str name.toString),("alias_declaration",Json.str aliasName.toString),
    ("type_kernel_equal",toJson typeEq),("full_value_kernel_equal",toJson fullValueEq),
    ("original_type_expression_repr",Json.str (reprStr d.type)),
    ("alias_type_expression_repr",Json.str (reprStr a.type)),
    ("original_full_value_expression_repr",Json.str (reprStr d.value)),
    ("alias_full_value_expression_repr",Json.str (reprStr a.value)),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def emitIndependentProof (name : Name) : MetaM Unit := do
  let ci ← getConstInfo name
  let typ ← ppExpr ci.type
  let axs ← Lean.collectAxioms name
  IO.println (Json.mkObj [("kind",Json.str "proof_full_type"),
    ("declaration",Json.str name.toString),
    ("full_type_expression_repr",Json.str (reprStr ci.type)),
    ("type_pp_diagnostic",Json.str typ.pretty),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

-- No run_meta block: no guessed declarations or silent claims of execution.

run_meta do
  emitIndependentProof `checked_exact_generic_polynomial_endpoint
  emitIndependentProof `checked_exact_generic_regular_point_endpoint
  emitIndependentProof `checked_exact_generic_actual_jet_injectivity
  emitIndependentProof `checked_zero_actual_jet
  emitIndependentProof `checked_zero_numerator_reconstruction
  emitIndependentProof `checked_m0_Aone_reconstruction
  emitIndependentProof `checked_m0_critical_X8_reconstruction
  emitIndependentProof `checked_m0_X9_is_excluded
  emitIndependentProof `checked_m0_highest_pole_of_one
  emitIndependentProof `checked_m0_simple_pole_of_X8
  emitIndependentProof `checked_m0_simple_pole_regular_PF
  emitIndependentProof `checked_two_pole_constant_reconstruction
  emitIndependentProof `checked_actual_weighted_jets_agree
  emitIndependentProof `checked_n1_q1_actual_shifted_remainder
  emitIndependentProof `checked_n1_q1_actual_remainder_reconstruction
  let actual ← getConstInfo `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions
  let explicit ← getConstInfo `checked_exact_generic_polynomial_endpoint
  let eq ← isDefEq actual.type explicit.type
  unless eq do throwError "Exact generic endpoint type mismatch"
  IO.println (Json.mkObj [("kind",Json.str "explicit_endpoint_type_kernel"),("source",Json.str "ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions"),("control",Json.str "checked_exact_generic_polynomial_endpoint"),("whole_type_kernel_equal",toJson eq),("actual_type_repr",Json.str (reprStr actual.type)),("explicit_type_repr",Json.str (reprStr explicit.type))]).compress
  let actual ← getConstInfo `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions
  let explicit ← getConstInfo `checked_exact_generic_regular_point_endpoint
  let eq ← isDefEq actual.type explicit.type
  unless eq do throwError "Exact generic endpoint type mismatch"
  IO.println (Json.mkObj [("kind",Json.str "explicit_endpoint_type_kernel"),("source",Json.str "ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions"),("control",Json.str "checked_exact_generic_regular_point_endpoint"),("whole_type_kernel_equal",toJson eq),("actual_type_repr",Json.str (reprStr actual.type)),("explicit_type_repr",Json.str (reprStr explicit.type))]).compress
  let actual ← getConstInfo `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective
  let explicit ← getConstInfo `checked_exact_generic_actual_jet_injectivity
  let eq ← isDefEq actual.type explicit.type
  unless eq do throwError "Exact generic endpoint type mismatch"
  IO.println (Json.mkObj [("kind",Json.str "explicit_endpoint_type_kernel"),("source",Json.str "ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective"),("control",Json.str "checked_exact_generic_actual_jet_injectivity"),("whole_type_kernel_equal",toJson eq),("actual_type_repr",Json.str (reprStr actual.type)),("explicit_type_repr",Json.str (reprStr explicit.type))]).compress
