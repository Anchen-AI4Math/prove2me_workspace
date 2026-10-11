import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
-- Own author runtime full Expr audit; helper source copied and hash-bound, no objects borrowed.
-- The caller supplies imports and constant lists from frozen inputs plus actual
-- official graph/parser facts. PP is diagnostic, never the kernel equality gate.
import Lean
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
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.connectionPair
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.connectionP
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.connectionQ
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.connectionGamma
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.remainderNumerator
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient
  emitIndependentDefinition `ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient
  emitIndependentDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation
  emitIndependentDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock
  emitIndependentDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator
  emitIndependentDefinition `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorCandidateClearedSeries
  emitIndependentProof `ZetaNine.CoefficientMapFormalTransportData.connectionPair_spec
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_denominator_identity
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_unique
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_comp_eq_sum
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_eq_sum_blocks
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_comp_own_shift
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_own_block_matches_nine_jets
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_pole_divisibility
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_shift_X_pow_dvd
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_full_candidate_matches_nine_jets
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_denominator_divides_actual_candidate_difference
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorCandidateClearedSeries_denominator_identity
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_candidate_first_nine_coefficients
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_candidate_local_coefficients
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_natDegree_le
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_natDegree_le
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_natDegree_le
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_partial_term_division
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_local_coefficient_weighted_agreement
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalCoefficient_sub
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_all_local_coefficients_zero_implies_zero
  emitIndependentProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective
