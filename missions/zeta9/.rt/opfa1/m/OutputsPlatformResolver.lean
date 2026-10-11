import OutputsPlatformGenerated
import OutputsPlatformSemantic
import OutputsPlatformExprDagValidationV1
import Lean
open Lean Meta
set_option maxHeartbeats 0
run_meta do
  let env ← getEnv
  for name in env.header.moduleNames do
    let file ← findOLean name
    let real ← IO.FS.realPath file
    IO.println (Json.mkObj [("kind",Json.str "actual_import_origin"),("module",Json.str name.toString),("chosen",Json.str file.toString),("realPath",Json.str real.toString)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMap
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMap.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMap"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMap"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapJet
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapJet.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapJet"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapJet"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapInjectivity
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapInjectivity.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapInjectivity"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapInjectivity"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapPartialFractions
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapPartialFractions.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapPartialFractions"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapPartialFractions"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapReflection
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapReflection.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapReflection"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapReflection"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_HarmonicStability
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_HarmonicStability.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_HarmonicStability"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_HarmonicStability"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapFiniteSum
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapFiniteSum.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapFiniteSum"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapFiniteSum"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapSummation
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapSummation.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapSummation"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapSummation"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapAggregate
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapAggregate.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapAggregate"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapAggregate"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapTelescoper
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapTelescoper.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapTelescoper"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapTelescoper"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapShiftDegree
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapShiftDegree.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapShiftDegree"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapShiftDegree"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapKernelBridge
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapKernelBridge.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapKernelBridge"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapKernelBridge"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapMatrix
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapMatrix.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapMatrix"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapMatrix"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapConnection
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapConnection.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapConnection"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapConnection"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapNumeratorPF
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapNumeratorPF.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapNumeratorPF"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapNumeratorPF"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Definitions\\Def_ZetaNine_CoefficientMapFormalTransportOutputs.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMap
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMap.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMap"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMap"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapJet
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapJet.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapJet"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapJet"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapInjectivity
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapInjectivity.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapInjectivity"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapInjectivity"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapPartialFractions
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapPartialFractions.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapPartialFractions"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapPartialFractions"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapReflection
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapReflection.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapReflection"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapReflection"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.HarmonicStability
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\HarmonicStability.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.HarmonicStability"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.HarmonicStability"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapFiniteSum
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapFiniteSum.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapFiniteSum"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapFiniteSum"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapSummation
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapSummation.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapSummation"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapSummation"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapAggregate
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapAggregate.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapAggregate"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapAggregate"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapTelescoper
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapTelescoper.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapTelescoper"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapTelescoper"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapShiftDegree
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapShiftDegree.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapShiftDegree"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapShiftDegree"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapKernelBridge
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapKernelBridge.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapKernelBridge"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapKernelBridge"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapConnection
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapConnection.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapConnection"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapConnection"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapParameterShift
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapParameterShift.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapParameterShift"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapParameterShift"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapFormalTransportData
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapFormalTransportData.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapFormalTransportData"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapFormalTransportData"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapFormalTransportBounds
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapFormalTransportBounds.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapFormalTransportBounds"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapFormalTransportBounds"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapFormalTransportNumerators
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapFormalTransportNumerators.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapFormalTransportNumerators"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapFormalTransportNumerators"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapNumeratorPartialFractions
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapNumeratorPartialFractions.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapNumeratorPartialFractions"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapNumeratorPartialFractions"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapFormalTransportJets
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapFormalTransportJets.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapFormalTransportJets"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapFormalTransportJets"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapMatrix
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapMatrix.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapMatrix"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapMatrix"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Oracle.CoefficientMapFormalTransportOutputs
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Oracle\\CoefficientMapFormalTransportOutputs.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Oracle.CoefficientMapFormalTransportOutputs"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Oracle.CoefficientMapFormalTransportOutputs"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Solutions.Sol_ZetaNine_CoefficientMapFormalTransportOutputs_matrix
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\Solutions\\Sol_ZetaNine_CoefficientMapFormalTransportOutputs_matrix.olean")
  unless real == expected do throwError "Own actual object origin mismatch: Solutions.Sol_ZetaNine_CoefficientMapFormalTransportOutputs_matrix"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Solutions.Sol_ZetaNine_CoefficientMapFormalTransportOutputs_matrix"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `OutputsPlatformExprDagV1
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\OutputsPlatformExprDagV1.olean")
  unless real == expected do throwError "Own actual object origin mismatch: OutputsPlatformExprDagV1"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "OutputsPlatformExprDagV1"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `OutputsPlatformExprDagValidationV1
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\OutputsPlatformExprDagValidationV1.olean")
  unless real == expected do throwError "Own actual object origin mismatch: OutputsPlatformExprDagValidationV1"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "OutputsPlatformExprDagValidationV1"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `OutputsPlatformAssertions
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\OutputsPlatformAssertions.olean")
  unless real == expected do throwError "Own actual object origin mismatch: OutputsPlatformAssertions"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "OutputsPlatformAssertions"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `OutputsPlatformSemantic
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\OutputsPlatformSemantic.olean")
  unless real == expected do throwError "Own actual object origin mismatch: OutputsPlatformSemantic"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "OutputsPlatformSemantic"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `OutputsPlatformGenerated
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\opfa1\\m\\b\\lib\\lean\\OutputsPlatformGenerated.olean")
  unless real == expected do throwError "Own actual object origin mismatch: OutputsPlatformGenerated"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "OutputsPlatformGenerated"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
