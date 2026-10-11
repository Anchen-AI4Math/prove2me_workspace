import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import Lean
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
noncomputable section
open scoped BigOperators
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapNumeratorPartialFractions
namespace PFIndependentFormula
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
end PFIndependentFormula
theorem whole_rfl_numeratorClearedSeries : ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries = PFIndependentFormula.numeratorClearedSeries := by rfl
theorem whole_rfl_numeratorLocalCoefficient : ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient = PFIndependentFormula.numeratorLocalCoefficient := by rfl
theorem whole_rfl_numeratorLocalTruncation : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation = PFIndependentFormula.numeratorLocalTruncation := by rfl
theorem whole_rfl_numeratorPartialBlock : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock = PFIndependentFormula.numeratorPartialBlock := by rfl
theorem whole_rfl_numeratorPartialNumerator : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator = PFIndependentFormula.numeratorPartialNumerator := by rfl
namespace PFIndependentExpected
theorem polynomial : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → A = numeratorPartialNumerator m A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions
theorem global : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → ∀ (t : ℚ), (∀ k ≤ m, t + (k : ℚ) ≠ 0) →
      A.eval t / (polePolynomial m).eval t ^ 9 =
        ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
          numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions
theorem injective : ∀ (m : ℕ) (A B : ℚ[X]),
    A.natDegree < 9 * (m + 1) → B.natDegree < 9 * (m + 1) →
    (∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) → A = B :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective
end PFIndependentExpected
namespace PFIndependentBoundary
theorem zero_jet (m j s : ℕ) : numeratorLocalCoefficient m j s (0 : ℚ[X]) = 0 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries]
theorem zero_reconstruction (m : ℕ) : (0 : ℚ[X]) = numeratorPartialNumerator m 0 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions m 0 (by simp)
theorem m0_one : (1 : ℚ[X]) = numeratorPartialNumerator 0 1 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions 0 1 (by norm_num)
theorem m0_critical_X8 : (X ^ 8 : ℚ[X]) = numeratorPartialNumerator 0 (X ^ 8) :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions 0 (X ^ 8) (by norm_num)
theorem m0_X9_outside_proper : ¬ (X ^ 9 : ℚ[X]).natDegree < 9 * (0 + 1) := by norm_num
theorem m0_highest_pole_one : numeratorLocalCoefficient 0 0 9 (1 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator, ZetaNine.CoefficientMapJet.shiftedVariable]
theorem m0_simple_pole_X8 : numeratorLocalCoefficient 0 0 1 (X ^ 8 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator, ZetaNine.CoefficientMapJet.shiftedVariable]
theorem m0_regular_simple_PF (t : ℚ) (ht : t ≠ 0) :
    (1 : ℚ) / t = ∑ j ∈ range (0 + 1), ∑ s ∈ Icc 1 9,
      numeratorLocalCoefficient 0 j s (X ^ 8 : ℚ[X]) / (t + (j : ℚ)) ^ s := by
  have h := ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions 0 (X ^ 8) (by norm_num) t (by
    intro k hk
    have hk0 : k = 0 := by omega
    simpa only [hk0, Nat.cast_zero, add_zero] using ht)
  have eval_identity : (X ^ 8 : ℚ[X]).eval t / (polePolynomial 0).eval t ^ 9 = (1 : ℚ) / t := by
    have pole_identity : (polePolynomial 0).eval t = t := by simp [polePolynomial]
    rw [pole_identity]
    simp only [eval_pow, eval_X]
    field_simp [ht] <;> ring
  rw [eval_identity] at h
  exact h
theorem two_pole_one : (1 : ℚ[X]) = numeratorPartialNumerator 1 1 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions 1 1 (by norm_num)
end PFIndependentBoundary
open Lean Meta
private def requireStd3 (name : Name) : MetaM (Array Name) := do
  let axioms ← Lean.collectAxioms name
  unless axioms.toList.all (fun n => ([`propext, `Classical.choice, `Quot.sound] : List Name).contains n) do
    throwError "Nonstandard axiom in actual declaration: {name}"
  return axioms
private def requireClosed (name : Name) (ty : Expr) (value : Expr) : MetaM Unit := do
  unless !(ty.hasFVar || ty.hasMVar || value.hasFVar || value.hasMVar) do
    throwError "Actual declaration has unclosed type or value: {name}"
private def emitDefinition (name : Name) : MetaM Unit := do
  let .defnInfo info ← getConstInfo name | throwError "Expected actual definition {name}"
  requireClosed name info.type info.value
  let axioms ← requireStd3 name
  IO.println (Json.mkObj [("kind",Json.str "independent_full_definition"),
    ("declaration",Json.str name.toString),("closed",toJson true),
    ("level_parameters",toJson (info.levelParams.map Name.toString)),
    ("full_type_raw_Expr",Json.str (reprStr info.type)),
    ("full_value_raw_Expr",Json.str (reprStr info.value)),
    ("axioms",toJson (axioms.toList.map Name.toString))]).compress
private def emitProof (name : Name) (kind : String) : MetaM Unit := do
  let .thmInfo info ← getConstInfo name | throwError "Expected actual theorem {name}"
  requireClosed name info.type info.value
  let axioms ← requireStd3 name
  IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str name.toString),
    ("closed",toJson true),("full_type_raw_Expr",Json.str (reprStr info.type)),
    ("axioms",toJson (axioms.toList.map Name.toString))]).compress
private def compareWhole (name expected : Name) : MetaM Unit := do
  let .defnInfo actualInfo ← getConstInfo name | throwError "Expected actual definition"
  let .defnInfo expectedInfo ← getConstInfo expected | throwError "Expected independently written definition"
  let typeKernel ← isDefEq actualInfo.type expectedInfo.type
  let valueKernel ← isDefEq actualInfo.value expectedInfo.value
  let typeRaw := Expr.equal actualInfo.type expectedInfo.type
  let valueRaw := Expr.equal actualInfo.value expectedInfo.value
  unless typeKernel && valueKernel && typeRaw && valueRaw do
    throwError "Full-function Expr/kernel mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_whole_definition_comparison"),
    ("declaration",Json.str name.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson typeKernel),("value_kernel_equal",toJson valueKernel),
    ("type_Expr_equal",toJson typeRaw),("value_Expr_equal",toJson valueRaw),
    ("actual_full_type_raw_Expr",Json.str (reprStr actualInfo.type)),
    ("expected_full_type_raw_Expr",Json.str (reprStr expectedInfo.type)),
    ("actual_full_value_raw_Expr",Json.str (reprStr actualInfo.value)),
    ("expected_full_value_raw_Expr",Json.str (reprStr expectedInfo.value))]).compress
private def compareType (name expected : Name) : MetaM Unit := do
  let actualInfo ← getConstInfo name
  let expectedInfo ← getConstInfo expected
  let same ← isDefEq actualInfo.type expectedInfo.type
  unless same do throwError "Whole forall type mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_forall_kernel_comparison"),
    ("declaration",Json.str name.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson same),
    ("actual_full_type_raw_Expr",Json.str (reprStr actualInfo.type)),
    ("expected_full_type_raw_Expr",Json.str (reprStr expectedInfo.type))]).compress
private def compareDefinitionSnapshot (name : Name) (nativeType nativeValue : Expr) : MetaM Unit := do
  let .defnInfo actualInfo ← getConstInfo name | throwError "Expected actual definition"
  let typeKernel ← isDefEq actualInfo.type nativeType
  let valueKernel ← isDefEq actualInfo.value nativeValue
  let typeRaw := Expr.equal actualInfo.type nativeType
  let valueRaw := Expr.equal actualInfo.value nativeValue
  unless typeKernel && valueKernel && typeRaw && valueRaw do
    throwError "Fresh native/staged full definition mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_native_staged_definition_snapshot"),
    ("declaration",Json.str name.toString),("type_kernel_equal",toJson typeKernel),
    ("value_kernel_equal",toJson valueKernel),("type_Expr_equal",toJson typeRaw),
    ("value_Expr_equal",toJson valueRaw),
    ("native_full_type_raw_Expr",Json.str (reprStr nativeType)),
    ("native_full_value_raw_Expr",Json.str (reprStr nativeValue))]).compress
private def compareProofSnapshot (name : Name) (nativeType : Expr) : MetaM Unit := do
  let actualInfo ← getConstInfo name
  let same ← isDefEq actualInfo.type nativeType
  unless same do throwError "Fresh native/staged whole proof type mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str "independent_native_staged_proof_snapshot"),
    ("declaration",Json.str name.toString),("whole_type_kernel_equal",toJson same),
    ("native_full_type_raw_Expr",Json.str (reprStr nativeType)),
    ("actual_full_type_raw_Expr",Json.str (reprStr actualInfo.type))]).compress
private def emitInternalHelpers (modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut found : List Name := []
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[index.toNat]? | continue
    if modules.contains moduleName && (name.isInternal || (privateToUserName? name).isSome) then
      found := name :: found
      match info with
      | .thmInfo _ => emitProof name "independent_internal_helper_proof"
      | .defnInfo _ => emitDefinition name
      | _ =>
        let axioms ← requireStd3 name
        IO.println (Json.mkObj [("kind",Json.str "independent_internal_helper_other"),
          ("declaration",Json.str name.toString),("full_type_raw_Expr",Json.str (reprStr info.type)),
          ("axioms",toJson (axioms.toList.map Name.toString))]).compress
  IO.println (Json.mkObj [("kind",Json.str "independent_actual_internal_helper_inventory"),
    ("modules",toJson (modules.map Name.toString)),("names",toJson (found.map Name.toString))]).compress

run_meta do
  emitDefinition `ZetaNine.CoefficientMap.clearedPoleProduct
  emitDefinition `ZetaNine.CoefficientMap.poleProduct
  emitDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries
  emitDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
  emitDefinition `ZetaNine.CoefficientMapInjectivity.polePolynomial
  emitDefinition `ZetaNine.CoefficientMapJet.shiftedClearedDenominator
  emitDefinition `ZetaNine.CoefficientMapJet.shiftedVariable
  emitDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation
  emitDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock
  emitDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator
  emitDefinition `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial
  emitProof `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapJet.shiftedVariable_eval "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_all_local_coefficients_zero_implies_zero "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_denominator_identity "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalCoefficient_sub "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_comp_eq_sum "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_natDegree_le "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_comp_own_shift "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_natDegree_le "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_eq_sum_blocks "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_natDegree_le "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_denominator_divides_actual_candidate_difference "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_pole_divisibility "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_shift_X_pow_dvd "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_full_candidate_matches_nine_jets "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_own_block_matches_nine_jets "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_partial_term_division "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd "independent_named_native_proof"
  emitProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock.eq_1 "independent_generated_equation_helper"
  compareWhole `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries `PFIndependentFormula.numeratorClearedSeries
  emitProof `whole_rfl_numeratorClearedSeries "independent_whole_function_rfl"
  compareWhole `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient `PFIndependentFormula.numeratorLocalCoefficient
  emitProof `whole_rfl_numeratorLocalCoefficient "independent_whole_function_rfl"
  compareWhole `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation `PFIndependentFormula.numeratorLocalTruncation
  emitProof `whole_rfl_numeratorLocalTruncation "independent_whole_function_rfl"
  compareWhole `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock `PFIndependentFormula.numeratorPartialBlock
  emitProof `whole_rfl_numeratorPartialBlock "independent_whole_function_rfl"
  compareWhole `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator `PFIndependentFormula.numeratorPartialNumerator
  emitProof `whole_rfl_numeratorPartialNumerator "independent_whole_function_rfl"
  emitProof `PFIndependentExpected.polynomial "independent_expected_complete_forall"
  compareType `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions `PFIndependentExpected.polynomial
  emitProof `PFIndependentExpected.global "independent_expected_complete_forall"
  compareType `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions `PFIndependentExpected.global
  emitProof `PFIndependentExpected.injective "independent_expected_complete_forall"
  compareType `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective `PFIndependentExpected.injective
  emitProof `PFIndependentBoundary.zero_jet "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.zero_reconstruction "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_one "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_critical_X8 "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_X9_outside_proper "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_highest_pole_one "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_simple_pole_X8 "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.m0_regular_simple_PF "independent_actual_closed_boundary"
  emitProof `PFIndependentBoundary.two_pole_one "independent_actual_closed_boundary"
  emitInternalHelpers [`missions.zeta9.formalization.CoefficientMap, `missions.zeta9.formalization.CoefficientMapJet, `missions.zeta9.formalization.CoefficientMapInjectivity, `missions.zeta9.formalization.CoefficientMapPartialFractions, `missions.zeta9.formalization.CoefficientMapReflection, `Definitions.Def_ZetaNine_HarmonicStability, `missions.zeta9.formalization.CoefficientMapFiniteSum, `missions.zeta9.formalization.CoefficientMapSummation, `missions.zeta9.formalization.CoefficientMapAggregate, `missions.zeta9.formalization.CoefficientMapTelescoper, `missions.zeta9.formalization.CoefficientMapShiftDegree, `missions.zeta9.formalization.CoefficientMapKernelBridge, `missions.zeta9.formalization.CoefficientMapConnection, `missions.zeta9.formalization.CoefficientMapParameterShift, `missions.zeta9.formalization.CoefficientMapFormalTransportData, `missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions]
