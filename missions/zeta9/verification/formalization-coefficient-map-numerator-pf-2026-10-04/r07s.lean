import ValueAliases
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
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.connectionPair `ZetaNine.NPFDataValueAliases.connectionPair
  emitIndependentProof `value_Data_connectionPair
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.connectionP `ZetaNine.NPFDataValueAliases.connectionP
  emitIndependentProof `value_Data_connectionP
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.connectionQ `ZetaNine.NPFDataValueAliases.connectionQ
  emitIndependentProof `value_Data_connectionQ
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.connectionGamma `ZetaNine.NPFDataValueAliases.connectionGamma
  emitIndependentProof `value_Data_connectionGamma
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.remainderNumerator `ZetaNine.NPFDataValueAliases.remainderNumerator
  emitIndependentProof `value_Data_remainderNumerator
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator `ZetaNine.NPFDataValueAliases.shiftedRemainderNumerator
  emitIndependentProof `value_Data_shiftedRemainderNumerator
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries `ZetaNine.NPFDataValueAliases.numeratorClearedSeries
  emitIndependentProof `value_Data_numeratorClearedSeries
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient `ZetaNine.NPFDataValueAliases.numeratorLocalCoefficient
  emitIndependentProof `value_Data_numeratorLocalCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient `ZetaNine.NPFDataValueAliases.remainderCoefficient
  emitIndependentProof `value_Data_remainderCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient `ZetaNine.NPFDataValueAliases.extendedOldCoefficient
  emitIndependentProof `value_Data_extendedOldCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient `ZetaNine.NPFDataValueAliases.extendedRemainderCoefficient
  emitIndependentProof `value_Data_extendedRemainderCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient `ZetaNine.NPFDataValueAliases.previousRemainderCoefficient
  emitIndependentProof `value_Data_previousRemainderCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation `ZetaNine.NPFValueAliases.numeratorLocalTruncation
  emitIndependentProof `value_PF_numeratorLocalTruncation
  checkIndependentNativeAlias `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock `ZetaNine.NPFValueAliases.numeratorPartialBlock
  emitIndependentProof `value_PF_numeratorPartialBlock
  checkIndependentNativeAlias `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator `ZetaNine.NPFValueAliases.numeratorPartialNumerator
  emitIndependentProof `value_PF_numeratorPartialNumerator
  checkIndependentNativeAlias `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorCandidateClearedSeries `ZetaNine.NPFValueAliases.numeratorCandidateClearedSeries
  emitIndependentProof `value_PF_numeratorCandidateClearedSeries
