import IndependentDataValues
import Lean
open Lean Meta
run_meta do
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.connectionPair | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.connectionPair | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_connectionPair
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_connectionPair
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.connectionPair"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.connectionPair"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.connectionP | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.connectionP | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_connectionP
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_connectionP
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.connectionP"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.connectionP"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.connectionQ | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.connectionQ | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_connectionQ
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_connectionQ
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.connectionQ"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.connectionQ"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.connectionGamma | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.connectionGamma | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_connectionGamma
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_connectionGamma
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.connectionGamma"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.connectionGamma"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.remainderNumerator | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.remainderNumerator | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_remainderNumerator
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_remainderNumerator
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.remainderNumerator"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.remainderNumerator"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.shiftedRemainderNumerator | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_shiftedRemainderNumerator
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_shiftedRemainderNumerator
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.shiftedRemainderNumerator"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.numeratorClearedSeries | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_numeratorClearedSeries
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_numeratorClearedSeries
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.numeratorClearedSeries"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.numeratorLocalCoefficient | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_numeratorLocalCoefficient
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_numeratorLocalCoefficient
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.numeratorLocalCoefficient"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.remainderCoefficient | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_remainderCoefficient
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_remainderCoefficient
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.remainderCoefficient"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.extendedOldCoefficient | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_extendedOldCoefficient
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_extendedOldCoefficient
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.extendedOldCoefficient"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.extendedRemainderCoefficient | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_extendedRemainderCoefficient
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_extendedRemainderCoefficient
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.extendedRemainderCoefficient"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let .defnInfo original ← getConstInfo `ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient | throwError "Expected actual original definition"
    let .defnInfo aliasDef ← getConstInfo `ZetaNine.NumeratorsIndependentDataValues.previousRemainderCoefficient | throwError "Expected actual same-byte alias"
    unless ← isDefEq original.type aliasDef.type do throwError "Whole definition type differs"
    unless ← isDefEq original.value aliasDef.value do throwError "Whole actual definition value differs"
    let certificate ← getConstInfo `NumeratorsIndependentValueCertificates.value_previousRemainderCoefficient
    let axs ← collectAxioms `NumeratorsIndependentValueCertificates.value_previousRemainderCoefficient
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole-value certificate"
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_value_kernel"),
      ("declaration",Json.str "ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient"),("alias",Json.str "ZetaNine.NumeratorsIndependentDataValues.previousRemainderCoefficient"),
      ("type_kernel_equal",Json.bool true),("full_value_kernel_equal",Json.bool true),
      ("original_type_expr",Json.str (reprStr original.type)),("alias_type_expr",Json.str (reprStr aliasDef.type)),
      ("original_full_value_expr",Json.str (reprStr original.value)),("alias_full_value_expr",Json.str (reprStr aliasDef.value)),
      ("actual_kernel_rfl_certificate",Json.str (reprStr certificate.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
