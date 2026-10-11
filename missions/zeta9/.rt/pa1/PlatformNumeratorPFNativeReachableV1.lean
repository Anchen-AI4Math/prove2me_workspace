import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import Lean

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
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions
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
  emitAuthorProof `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock.eq_1 "generated_helper_full_type"
