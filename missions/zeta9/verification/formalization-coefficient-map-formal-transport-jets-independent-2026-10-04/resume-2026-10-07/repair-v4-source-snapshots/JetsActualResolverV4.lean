import missions.zeta9.formalization.CoefficientMapFormalTransportJets
import JetsIndependentTypesV2
import JetsIndependentBoundariesV3
import JetsIndependentSerializerControls
import AuthorBoundaryReplay
import Lean
open Lean
set_option autoImplicit false
set_option maxHeartbeats 0
run_meta do
  let requested : List (Name × String) := [
    (`missions.zeta9.formalization.CoefficientMap, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMap.olean"),
    (`missions.zeta9.formalization.CoefficientMapJet, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapJet.olean"),
    (`missions.zeta9.formalization.CoefficientMapInjectivity, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapInjectivity.olean"),
    (`missions.zeta9.formalization.CoefficientMapPartialFractions, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapPartialFractions.olean"),
    (`missions.zeta9.formalization.CoefficientMapReflection, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapReflection.olean"),
    (`Definitions.Def_ZetaNine_HarmonicStability, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\Definitions\\Def_ZetaNine_HarmonicStability.olean"),
    (`missions.zeta9.formalization.CoefficientMapFiniteSum, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapFiniteSum.olean"),
    (`missions.zeta9.formalization.CoefficientMapSummation, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapSummation.olean"),
    (`missions.zeta9.formalization.CoefficientMapAggregate, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapAggregate.olean"),
    (`missions.zeta9.formalization.CoefficientMapTelescoper, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapTelescoper.olean"),
    (`missions.zeta9.formalization.CoefficientMapShiftDegree, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapShiftDegree.olean"),
    (`missions.zeta9.formalization.CoefficientMapKernelBridge, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapKernelBridge.olean"),
    (`missions.zeta9.formalization.CoefficientMapConnection, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapConnection.olean"),
    (`missions.zeta9.formalization.CoefficientMapParameterShift, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapParameterShift.olean"),
    (`missions.zeta9.formalization.CoefficientMapFormalTransportData, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapFormalTransportData.olean"),
    (`missions.zeta9.formalization.CoefficientMapFormalTransportBounds, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapFormalTransportBounds.olean"),
    (`missions.zeta9.formalization.CoefficientMapFormalTransportNumerators, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapFormalTransportNumerators.olean"),
    (`missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapNumeratorPartialFractions.olean"),
    (`missions.zeta9.formalization.CoefficientMapFormalTransportJets, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\missions\\zeta9\\formalization\\CoefficientMapFormalTransportJets.olean"),
    (`IndependentExprDagV3, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\IndependentExprDagV3.olean"),
    (`IndependentExprDagValidationV3, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\IndependentExprDagValidationV3.olean"),
    (`JetsIndependentTypesV2, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\JetsIndependentTypesV2.olean"),
    (`JetsIndependentBoundariesV3, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\JetsIndependentBoundariesV3.olean"),
    (`JetsIndependentSerializerControls, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\JetsIndependentSerializerControls.olean"),
    (`AuthorBoundaryReplay, "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\tj1\\b\\lib\\lean\\AuthorBoundaryReplay.olean")
  ]
  let env ← getEnv
  for (module, wanted) in requested do
    let actual ← IO.FS.realPath (← findOLean module)
    let expected ← IO.FS.realPath (System.FilePath.mk wanted)
    unless actual == expected do throwError "Borrowed proof object: {module}: {actual}"
    -- The duplicate fixture serializer is intentionally compiled separately.
    let mustBeInHeader := module != `IndependentExprDagValidationV3
    let inHeader := env.header.moduleNames.contains module
    unless !mustBeInHeader || inHeader do throwError "Actual imported header missing {module}"
    IO.println (Json.mkObj [("kind",Json.str "actual_own_findOLean"),
      ("module",Json.str module.toString),("olean",Json.str actual.toString),
      ("expected",Json.str expected.toString),("exact_own_cache",toJson true),
      ("actual_header_contains",toJson inHeader),
      ("separate_fixture_environment",toJson (!mustBeInHeader))]).compress
  IO.println (Json.mkObj [("kind",Json.str "actual_environment_module_header"),
    ("modules",toJson (env.header.moduleNames.toList.map Name.toString))]).compress
