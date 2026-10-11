import IndependentValuesV2
import Lean
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

theorem independent_whole_value_01 : ZetaNine.CoefficientMapFormalTransportData.connectionPair = NumeratorPFIndependentDataValues.connectionPair := rfl
theorem independent_whole_value_02 : ZetaNine.CoefficientMapFormalTransportData.connectionP = NumeratorPFIndependentDataValues.connectionP := rfl
theorem independent_whole_value_03 : ZetaNine.CoefficientMapFormalTransportData.connectionQ = NumeratorPFIndependentDataValues.connectionQ := rfl
theorem independent_whole_value_04 : ZetaNine.CoefficientMapFormalTransportData.connectionGamma = NumeratorPFIndependentDataValues.connectionGamma := rfl
theorem independent_whole_value_05 : ZetaNine.CoefficientMapFormalTransportData.remainderNumerator = NumeratorPFIndependentDataValues.remainderNumerator := rfl
theorem independent_whole_value_06 : ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator = NumeratorPFIndependentDataValues.shiftedRemainderNumerator := rfl
theorem independent_whole_value_07 : ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries = NumeratorPFIndependentDataValues.numeratorClearedSeries := rfl
theorem independent_whole_value_08 : ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient = NumeratorPFIndependentDataValues.numeratorLocalCoefficient := rfl
theorem independent_whole_value_09 : ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient = NumeratorPFIndependentDataValues.remainderCoefficient := rfl
theorem independent_whole_value_10 : ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient = NumeratorPFIndependentDataValues.extendedOldCoefficient := rfl
theorem independent_whole_value_11 : ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient = NumeratorPFIndependentDataValues.extendedRemainderCoefficient := rfl
theorem independent_whole_value_12 : ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient = NumeratorPFIndependentDataValues.previousRemainderCoefficient := rfl
theorem independent_whole_value_13 : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation = NumeratorPFIndependentValues.numeratorLocalTruncation := rfl
theorem independent_whole_value_14 : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock = NumeratorPFIndependentValues.numeratorPartialBlock := rfl
theorem independent_whole_value_15 : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator = NumeratorPFIndependentValues.numeratorPartialNumerator := rfl
theorem independent_whole_value_16 : ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorCandidateClearedSeries = NumeratorPFIndependentValues.numeratorCandidateClearedSeries := rfl

run_meta do
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.connectionPair `NumeratorPFIndependentDataValues.connectionPair
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.connectionP `NumeratorPFIndependentDataValues.connectionP
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.connectionQ `NumeratorPFIndependentDataValues.connectionQ
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.connectionGamma `NumeratorPFIndependentDataValues.connectionGamma
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.remainderNumerator `NumeratorPFIndependentDataValues.remainderNumerator
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator `NumeratorPFIndependentDataValues.shiftedRemainderNumerator
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries `NumeratorPFIndependentDataValues.numeratorClearedSeries
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient `NumeratorPFIndependentDataValues.numeratorLocalCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient `NumeratorPFIndependentDataValues.remainderCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient `NumeratorPFIndependentDataValues.extendedOldCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient `NumeratorPFIndependentDataValues.extendedRemainderCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient `NumeratorPFIndependentDataValues.previousRemainderCoefficient
  checkIndependentNativeAlias `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation `NumeratorPFIndependentValues.numeratorLocalTruncation
  checkIndependentNativeAlias `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock `NumeratorPFIndependentValues.numeratorPartialBlock
  checkIndependentNativeAlias `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator `NumeratorPFIndependentValues.numeratorPartialNumerator
  checkIndependentNativeAlias `ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorCandidateClearedSeries `NumeratorPFIndependentValues.numeratorCandidateClearedSeries
  emitIndependentProof `independent_whole_value_01
  emitIndependentProof `independent_whole_value_02
  emitIndependentProof `independent_whole_value_03
  emitIndependentProof `independent_whole_value_04
  emitIndependentProof `independent_whole_value_05
  emitIndependentProof `independent_whole_value_06
  emitIndependentProof `independent_whole_value_07
  emitIndependentProof `independent_whole_value_08
  emitIndependentProof `independent_whole_value_09
  emitIndependentProof `independent_whole_value_10
  emitIndependentProof `independent_whole_value_11
  emitIndependentProof `independent_whole_value_12
  emitIndependentProof `independent_whole_value_13
  emitIndependentProof `independent_whole_value_14
  emitIndependentProof `independent_whole_value_15
  emitIndependentProof `independent_whole_value_16
