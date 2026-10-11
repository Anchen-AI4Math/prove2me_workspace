import PhasePlatformSemantic
import PhasePlatformExprDagValidationV1
import Lean
open Lean Meta
set_option maxHeartbeats 8000000
run_meta do
  let env ← getEnv
  for name in env.header.moduleNames do
    let file ← findOLean name
    let real ← IO.FS.realPath file
    IO.println (Json.mkObj [("kind",Json.str "actual_import_origin"),("module",Json.str name.toString),("chosen",Json.str file.toString),("realPath",Json.str real.toString)]).compress
  let file ← findOLean `Definitions.Def_ZetaNine_AnalyticPhase
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\apfa1\\global\\b\\lib\\lean\\Definitions\\Def_ZetaNine_AnalyticPhase.olean")
  unless real == expected do throwError "Own actual proof object mismatch: Definitions.Def_ZetaNine_AnalyticPhase"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Definitions.Def_ZetaNine_AnalyticPhase"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Native.AnalyticPhase
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\apfa1\\global\\b\\lib\\lean\\Native\\AnalyticPhase.olean")
  unless real == expected do throwError "Own actual proof object mismatch: Native.AnalyticPhase"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Native.AnalyticPhase"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Native.AnalyticPhaseUpperBound
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\apfa1\\global\\b\\lib\\lean\\Native\\AnalyticPhaseUpperBound.olean")
  unless real == expected do throwError "Own actual proof object mismatch: Native.AnalyticPhaseUpperBound"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Native.AnalyticPhaseUpperBound"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `Solutions.Sol_ZetaNine_AnalyticPhase_phase_global_upper_bound
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\apfa1\\global\\b\\lib\\lean\\Solutions\\Sol_ZetaNine_AnalyticPhase_phase_global_upper_bound.olean")
  unless real == expected do throwError "Own actual proof object mismatch: Solutions.Sol_ZetaNine_AnalyticPhase_phase_global_upper_bound"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "Solutions.Sol_ZetaNine_AnalyticPhase_phase_global_upper_bound"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `PhasePlatformExprDagV1
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\apfa1\\global\\b\\lib\\lean\\PhasePlatformExprDagV1.olean")
  unless real == expected do throwError "Own actual proof object mismatch: PhasePlatformExprDagV1"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "PhasePlatformExprDagV1"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `PhasePlatformExprDagValidationV1
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\apfa1\\global\\b\\lib\\lean\\PhasePlatformExprDagValidationV1.olean")
  unless real == expected do throwError "Own actual proof object mismatch: PhasePlatformExprDagValidationV1"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "PhasePlatformExprDagValidationV1"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `PhasePlatformAssertions
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\apfa1\\global\\b\\lib\\lean\\PhasePlatformAssertions.olean")
  unless real == expected do throwError "Own actual proof object mismatch: PhasePlatformAssertions"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "PhasePlatformAssertions"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
  let file ← findOLean `PhasePlatformSemantic
  let real ← IO.FS.realPath file
  let expected ← IO.FS.realPath (System.FilePath.mk "D:\\users\\self_projects\\prove2me_workspace\\missions\\zeta9\\.rt\\apfa1\\global\\b\\lib\\lean\\PhasePlatformSemantic.olean")
  unless real == expected do throwError "Own actual proof object mismatch: PhasePlatformSemantic"
  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "PhasePlatformSemantic"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress
