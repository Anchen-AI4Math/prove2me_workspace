import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapNumeratorPartialFractions
namespace NumeratorPFIndependentBoundaries

theorem zero_jet (m j s : ℕ) : numeratorLocalCoefficient m j s (0 : ℚ[X]) = 0 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries]

theorem zero_candidate (m : ℕ) : numeratorPartialNumerator m (0 : ℚ[X]) = 0 := by
  exact (actual_numerator_polynomial_partial_fractions m 0 (by simp)).symm

theorem m0_highest_one : numeratorLocalCoefficient 0 0 9 (1 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.shiftedVariable]

theorem m0_simple_X8 : numeratorLocalCoefficient 0 0 1 (X ^ 8 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.shiftedVariable]

theorem m0_X9_all_jets_zero (s : ℕ) (hs : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient 0 0 s (X ^ 9 : ℚ[X]) = 0 := by
  have hk : 9 - s ≠ 9 := by omega
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.shiftedVariable, hk]

theorem m0_X9_nonzero : (X ^ 9 : ℚ[X]) ≠ 0 := by simp

theorem m0_X9_not_proper : ¬ (X ^ 9 : ℚ[X]).natDegree < 9 * ((0 : ℕ) + 1) := by
  norm_num

theorem m0_X9_candidate_zero : numeratorPartialNumerator 0 (X ^ 9 : ℚ[X]) = 0 := by
  unfold numeratorPartialNumerator
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j = 0 := by simpa using hj
  subst j
  apply Finset.sum_eq_zero
  intro s hs
  rw [m0_X9_all_jets_zero s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2]
  simp

theorem properness_required_counterexample :
    (∀ j ≤ (0 : ℕ), ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient 0 j s (X ^ 9 : ℚ[X]) = 0) ∧
    (X ^ 9 : ℚ[X]) ≠ 0 := by
  constructor
  · intro j hj s hs hs9
    have hj0 : j = 0 := by omega
    subst j
    exact m0_X9_all_jets_zero s hs hs9
  · exact m0_X9_nonzero

theorem m0_critical_proper : (X ^ 8 : ℚ[X]).natDegree < 9 * ((0 : ℕ) + 1) := by norm_num

theorem m0_critical_reconstruction : (X ^ 8 : ℚ[X]) = numeratorPartialNumerator 0 (X ^ 8) :=
  actual_numerator_polynomial_partial_fractions 0 (X ^ 8) m0_critical_proper

theorem m0_critical_rational_is_one_div_t (t : ℚ) (ht : t ≠ 0) :
    (X ^ 8 : ℚ[X]).eval t / (polePolynomial 0).eval t ^ 9 = 1 / t := by
  have hp : (polePolynomial 0).eval t = t := by simp [polePolynomial]
  rw [hp]
  simp only [eval_pow, eval_X]
  field_simp [ht] <;> ring

theorem m0_pole_not_regular : ¬ (∀ k ≤ (0 : ℕ), (0 : ℚ) + (k : ℚ) ≠ 0) := by
  intro h
  exact h 0 (by omega) (by norm_num)

theorem m1_second_pole_not_regular : ¬ (∀ k ≤ (1 : ℕ), (-1 : ℚ) + (k : ℚ) ≠ 0) := by
  intro h
  exact h 1 (by omega) (by norm_num)

theorem m1_regular_at_one : ∀ k ≤ (1 : ℕ), (1 : ℚ) + (k : ℚ) ≠ 0 := by
  intro k hk
  have hp : (0 : ℚ) < 1 + (k : ℚ) := by positivity
  exact ne_of_gt hp

theorem m1_constant_reconstruction : (1 : ℚ[X]) = numeratorPartialNumerator 1 1 :=
  actual_numerator_polynomial_partial_fractions 1 1 (by norm_num)

theorem m1_constant_regular_at_one :
    (1 : ℚ) / (polePolynomial 1).eval 1 ^ 9 =
      ∑ j ∈ range (1 + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient 1 j s (1 : ℚ[X]) / (1 + (j : ℚ)) ^ s := by
  simpa using actual_numerator_global_partial_fractions 1 (1 : ℚ[X])
    (by norm_num) 1 m1_regular_at_one

theorem coeff_k0 (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    PowerSeries.coeff 0 (numeratorCandidateClearedSeries m j A) =
      PowerSeries.coeff 0 (numeratorClearedSeries m j A) :=
  numerator_candidate_first_nine_coefficients m j A hj 0 (by omega)

theorem coeff_k8 (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    PowerSeries.coeff 8 (numeratorCandidateClearedSeries m j A) =
      PowerSeries.coeff 8 (numeratorClearedSeries m j A) :=
  numerator_candidate_first_nine_coefficients m j A hj 8 (by omega)

theorem endpoint_s1 (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    PowerSeries.coeff 8 (numeratorCandidateClearedSeries m j A) =
      numeratorLocalCoefficient m j 1 A :=
  numerator_candidate_local_coefficients m j 1 A hj (by omega) (by omega)

theorem endpoint_s9 (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    PowerSeries.coeff 0 (numeratorCandidateClearedSeries m j A) =
      numeratorLocalCoefficient m j 9 A :=
  numerator_candidate_local_coefficients m j 9 A hj (by omega) (by omega)

theorem candidate_degree_all_A (m : ℕ) (A : ℚ[X]) :
    (numeratorPartialNumerator m A).natDegree ≤ 9 * m + 8 :=
  numeratorPartialNumerator_natDegree_le m A

theorem divisibility_without_properness (m : ℕ) (A : ℚ[X]) :
    polePolynomial m ^ 9 ∣ A - numeratorPartialNumerator m A :=
  numerator_denominator_divides_actual_candidate_difference m A

theorem offrange_denominator_identity (m : ℕ) (A : ℚ[X]) :
    numeratorClearedSeries m (m + 1) A *
      (ZetaNine.CoefficientMapJet.shiftedClearedDenominator m (m + 1) : PowerSeries ℚ) ^ 9 =
        (A.comp (ZetaNine.CoefficientMapJet.shiftedVariable (m + 1)) : PowerSeries ℚ) :=
  numeratorClearedSeries_denominator_identity m (m + 1) A

theorem weighted_agreement_unrestricted (m j s : ℕ) (W : ℚ[X]) :
    numeratorLocalCoefficient m j s (weightedNumerator m W) =
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient m j s W :=
  numerator_local_coefficient_weighted_agreement m j s W

end NumeratorPFIndependentBoundaries

-- Source-only imported helper for this fresh independent runtime audit; helper source copied and hash-bound, no objects borrowed.
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
  emitIndependentProof `NumeratorPFIndependentBoundaries.zero_jet
  emitIndependentProof `NumeratorPFIndependentBoundaries.zero_candidate
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_highest_one
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_simple_X8
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_X9_all_jets_zero
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_X9_nonzero
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_X9_not_proper
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_X9_candidate_zero
  emitIndependentProof `NumeratorPFIndependentBoundaries.properness_required_counterexample
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_critical_proper
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_critical_reconstruction
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_critical_rational_is_one_div_t
  emitIndependentProof `NumeratorPFIndependentBoundaries.m0_pole_not_regular
  emitIndependentProof `NumeratorPFIndependentBoundaries.m1_second_pole_not_regular
  emitIndependentProof `NumeratorPFIndependentBoundaries.m1_regular_at_one
  emitIndependentProof `NumeratorPFIndependentBoundaries.m1_constant_reconstruction
  emitIndependentProof `NumeratorPFIndependentBoundaries.m1_constant_regular_at_one
  emitIndependentProof `NumeratorPFIndependentBoundaries.coeff_k0
  emitIndependentProof `NumeratorPFIndependentBoundaries.coeff_k8
  emitIndependentProof `NumeratorPFIndependentBoundaries.endpoint_s1
  emitIndependentProof `NumeratorPFIndependentBoundaries.endpoint_s9
  emitIndependentProof `NumeratorPFIndependentBoundaries.candidate_degree_all_A
  emitIndependentProof `NumeratorPFIndependentBoundaries.divisibility_without_properness
  emitIndependentProof `NumeratorPFIndependentBoundaries.offrange_denominator_identity
  emitIndependentProof `NumeratorPFIndependentBoundaries.weighted_agreement_unrestricted
