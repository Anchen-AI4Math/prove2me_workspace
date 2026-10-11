import Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_global
import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapNumeratorPartialFractions

namespace NativeSourceByteAliases
/-- Genuine formal jet for an arbitrary numerator, not an abstract array. -/
def numeratorClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  ((A.comp (ZetaNine.CoefficientMapJet.shiftedVariable j) : ℚ[X]) : PowerSeries ℚ) *
    ((ZetaNine.CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹
def numeratorLocalCoefficient (m j s : ℕ) (A : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries m j A)
def numeratorLocalTruncation (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc 9 (ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries m j A)
def numeratorPartialBlock (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial m j ^ 9 *
    (ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation m j A).comp (X + C (j : ℚ))
def numeratorPartialNumerator (m : ℕ) (A : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
    C (ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient m j s A) *
      ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial m j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)
end NativeSourceByteAliases
theorem whole_function_rfl_numeratorClearedSeries : ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries = NativeSourceByteAliases.numeratorClearedSeries := by rfl
theorem whole_function_rfl_numeratorLocalCoefficient : ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient = NativeSourceByteAliases.numeratorLocalCoefficient := by rfl
theorem whole_function_rfl_numeratorLocalTruncation : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation = NativeSourceByteAliases.numeratorLocalTruncation := by rfl
theorem whole_function_rfl_numeratorPartialBlock : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock = NativeSourceByteAliases.numeratorPartialBlock := by rfl
theorem whole_function_rfl_numeratorPartialNumerator : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator = NativeSourceByteAliases.numeratorPartialNumerator := by rfl
theorem exact_forall_polynomial : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → A = numeratorPartialNumerator m A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions
theorem exact_forall_global : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → ∀ (t : ℚ), (∀ k ≤ m, t + (k : ℚ) ≠ 0) →
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.checked_actual_numerator_global_partial_fractions
theorem exact_forall_injective : ∀ (m : ℕ) (A B : ℚ[X]),
    A.natDegree < 9 * (m + 1) → B.natDegree < 9 * (m + 1) →
    (∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) → A = B :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective
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
  have h := checked_actual_numerator_global_partial_fractions 0 (X ^ 8) (by norm_num) t
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


open Lean Meta
set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def emitAuthorDefinition (name : Name) : MetaM Unit := do
  let .defnInfo d ← getConstInfo name | throwError "Expected actual definition: {name}"
  let axs ← Lean.collectAxioms name
  IO.println (Json.mkObj [("kind",Json.str "definition_full_expression"),
    ("declaration",Json.str name.toString),
    ("level_parameters",toJson (d.levelParams.map Name.toString)),
    ("type_expression_repr",Json.str (reprStr d.type)),
    ("full_value_expression_repr",Json.str (reprStr d.value)),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def emitAuthorProof (name : Name) (kind : String := "proof_full_type") : MetaM Unit := do
  let ci ← getConstInfo name
  unless ← isProp ci.type do throwError "Expected proof declaration: {name}"
  let axs ← Lean.collectAxioms name
  IO.println (Json.mkObj [("kind",Json.str kind),
    ("declaration",Json.str name.toString),
    ("full_type_expression_repr",Json.str (reprStr ci.type)),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def checkAuthorWholeDefinition (name aliasName : Name) : MetaM Unit := do
  let .defnInfo d ← getConstInfo name | throwError "Expected actual definition"
  let .defnInfo a ← getConstInfo aliasName | throwError "Expected native-source byte alias"
  let typeEq ← isDefEq d.type a.type
  let valueEq ← isDefEq d.value a.value
  let typeRaw := Expr.equal d.type a.type
  let valueRaw := Expr.equal d.value a.value
  unless typeEq && valueEq && typeRaw && valueRaw do
    throwError "Full definition equality failed: {name}"
  let axs ← Lean.collectAxioms aliasName
  IO.println (Json.mkObj [("kind",Json.str "definition_whole_kernel_and_expr_equal"),
    ("declaration",Json.str name.toString),("alias",Json.str aliasName.toString),
    ("type_kernel_equal",toJson typeEq),("full_value_kernel_equal",toJson valueEq),
    ("type_Expr_equal",toJson typeRaw),("full_value_Expr_equal",toJson valueRaw),
    ("original_type_expression_repr",Json.str (reprStr d.type)),
    ("alias_type_expression_repr",Json.str (reprStr a.type)),
    ("original_full_value_expression_repr",Json.str (reprStr d.value)),
    ("alias_full_value_expression_repr",Json.str (reprStr a.value)),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def checkAuthorExactType (name expected : Name) : MetaM Unit := do
  let a ← getConstInfo name
  let b ← getConstInfo expected
  let eq ← isDefEq a.type b.type
  unless eq do throwError "Exact forall endpoint mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "explicit_endpoint_type_kernel"),
    ("declaration",Json.str name.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson eq),
    ("actual_type_repr",Json.str (reprStr a.type)),
    ("explicit_type_repr",Json.str (reprStr b.type))]).compress

private def emitAuthorPrivateHelpers (modules : List String) : MetaM Unit := do
  let env ← getEnv
  let mut names : List Name := []
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[idx.toNat]? | continue
    if modules.contains moduleName.toString && (name.isInternal || (privateToUserName? name).isSome) then
        names := name :: names
  for name in names do
    let ci ← getConstInfo name
    if ← isProp ci.type then
      emitAuthorProof name "private_helper_full_type"
    else if let .defnInfo _ := ci then
      emitAuthorDefinition name
  IO.println (Json.mkObj [("kind",Json.str "private_helper_inventory"),
    ("modules",toJson modules),("names",toJson (names.map Name.toString))]).compress

run_meta do
  emitAuthorDefinition `ZetaNine.CoefficientMap.poleProduct
  emitAuthorDefinition `ZetaNine.CoefficientMap.clearedPoleProduct
  emitAuthorDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries
  emitAuthorDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
  emitAuthorDefinition `ZetaNine.CoefficientMapInjectivity.polePolynomial
  emitAuthorDefinition `ZetaNine.CoefficientMapJet.shiftedVariable
  emitAuthorDefinition `ZetaNine.CoefficientMapJet.shiftedClearedDenominator
  emitAuthorDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation
  emitAuthorDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock
  emitAuthorDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator
  emitAuthorDefinition `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial
  emitAuthorProof `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero
  emitAuthorProof `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime
  emitAuthorProof `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree
  emitAuthorProof `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree
  emitAuthorProof `ZetaNine.CoefficientMapJet.shiftedVariable_eval
  emitAuthorProof `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval
  emitAuthorProof `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant
  emitAuthorProof `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_denominator_identity
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_comp_eq_sum
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_eq_sum_blocks
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_comp_own_shift
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_own_block_matches_nine_jets
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_pole_divisibility
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_shift_X_pow_dvd
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_full_candidate_matches_nine_jets
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_denominator_divides_actual_candidate_difference
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_natDegree_le
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_natDegree_le
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_natDegree_le
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_partial_term_division
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.checked_actual_numerator_global_partial_fractions
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalCoefficient_sub
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_all_local_coefficients_zero_implies_zero
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective
  emitAuthorProof `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift
  emitAuthorProof `ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd
  emitAuthorProof `ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series
  emitAuthorProof `ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility
  emitAuthorProof `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree
  emitAuthorProof `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval
  emitAuthorProof `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero
  emitAuthorProof `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor
  emitAuthorProof `solution
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock.eq_1 "generated_helper_full_type"
  checkAuthorWholeDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries `NativeSourceByteAliases.numeratorClearedSeries
  checkAuthorWholeDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient `NativeSourceByteAliases.numeratorLocalCoefficient
  checkAuthorWholeDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation `NativeSourceByteAliases.numeratorLocalTruncation
  checkAuthorWholeDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock `NativeSourceByteAliases.numeratorPartialBlock
  checkAuthorWholeDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator `NativeSourceByteAliases.numeratorPartialNumerator
  emitAuthorProof `whole_function_rfl_numeratorClearedSeries "whole_function_rfl"
  emitAuthorProof `whole_function_rfl_numeratorLocalCoefficient "whole_function_rfl"
  emitAuthorProof `whole_function_rfl_numeratorLocalTruncation "whole_function_rfl"
  emitAuthorProof `whole_function_rfl_numeratorPartialBlock "whole_function_rfl"
  emitAuthorProof `whole_function_rfl_numeratorPartialNumerator "whole_function_rfl"
  emitAuthorProof `exact_forall_polynomial "exact_forall_endpoint_proof"
  emitAuthorProof `exact_forall_global "exact_forall_endpoint_proof"
  emitAuthorProof `exact_forall_injective "exact_forall_endpoint_proof"
  checkAuthorExactType `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions `exact_forall_polynomial
  checkAuthorExactType `ZetaNine.CoefficientMapNumeratorPartialFractions.checked_actual_numerator_global_partial_fractions `exact_forall_global
  checkAuthorExactType `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective `exact_forall_injective
  checkAuthorExactType `solution `exact_forall_global
  emitAuthorProof `checked_zero_actual_jet "closed_boundary_proof"
  emitAuthorProof `checked_zero_numerator_reconstruction "closed_boundary_proof"
  emitAuthorProof `checked_m0_Aone_reconstruction "closed_boundary_proof"
  emitAuthorProof `checked_m0_critical_X8_reconstruction "closed_boundary_proof"
  emitAuthorProof `checked_m0_X9_is_excluded "closed_boundary_proof"
  emitAuthorProof `checked_m0_highest_pole_of_one "closed_boundary_proof"
  emitAuthorProof `checked_m0_simple_pole_of_X8 "closed_boundary_proof"
  emitAuthorProof `checked_m0_simple_pole_regular_PF "closed_boundary_proof"
  emitAuthorProof `checked_two_pole_constant_reconstruction "closed_boundary_proof"
  emitAuthorProof `checked_actual_weighted_jets_agree "closed_boundary_proof"
  emitAuthorPrivateHelpers ["Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_global", "Definitions.Def_ZetaNine_CoefficientMapNumeratorPF"]
