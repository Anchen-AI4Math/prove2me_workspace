import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import Lean
open Lean Meta
run_meta do
  let env ← getEnv
  let expected : List (Name × String × Bool) := [(`missions.zeta9.formalization.CoefficientMap, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMap.olean", true),
    (`missions.zeta9.formalization.CoefficientMapJet, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapJet.olean", true),
    (`missions.zeta9.formalization.CoefficientMapInjectivity, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapInjectivity.olean", true),
    (`missions.zeta9.formalization.CoefficientMapPartialFractions, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapPartialFractions.olean", true),
    (`missions.zeta9.formalization.CoefficientMapReflection, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapReflection.olean", true),
    (`Definitions.Def_ZetaNine_HarmonicStability, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Definitions/Def_ZetaNine_HarmonicStability.olean", true),
    (`missions.zeta9.formalization.CoefficientMapFiniteSum, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapFiniteSum.olean", true),
    (`missions.zeta9.formalization.CoefficientMapSummation, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapSummation.olean", true),
    (`missions.zeta9.formalization.CoefficientMapAggregate, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapAggregate.olean", true),
    (`missions.zeta9.formalization.CoefficientMapTelescoper, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapTelescoper.olean", true),
    (`missions.zeta9.formalization.CoefficientMapShiftDegree, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapShiftDegree.olean", true),
    (`missions.zeta9.formalization.CoefficientMapKernelBridge, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapKernelBridge.olean", true),
    (`missions.zeta9.formalization.CoefficientMapConnection, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapConnection.olean", true),
    (`missions.zeta9.formalization.CoefficientMapParameterShift, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapParameterShift.olean", true),
    (`missions.zeta9.formalization.CoefficientMapFormalTransportData, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapFormalTransportData.olean", true),
    (`missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/missions/zeta9/formalization/CoefficientMapNumeratorPartialFractions.olean", true),
    (`Definitions.Def_ZetaNine_CoefficientMap, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Definitions/Def_ZetaNine_CoefficientMap.olean", false),
    (`Definitions.Def_ZetaNine_CoefficientMapJet, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Definitions/Def_ZetaNine_CoefficientMapJet.olean", false),
    (`Definitions.Def_ZetaNine_CoefficientMapInjectivity, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Definitions/Def_ZetaNine_CoefficientMapInjectivity.olean", false),
    (`Definitions.Def_ZetaNine_CoefficientMapPartialFractions, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Definitions/Def_ZetaNine_CoefficientMapPartialFractions.olean", false),
    (`Definitions.Def_ZetaNine_CoefficientMapNumeratorPF, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Definitions/Def_ZetaNine_CoefficientMapNumeratorPF.olean", false),
    (`Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_polynomial, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_polynomial.olean", false),
    (`Theorems.Thm_ZetaNine_CoefficientMapNumeratorPF_polynomial, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_polynomial.olean", false),
    (`Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_global, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_global.olean", false),
    (`Theorems.Thm_ZetaNine_CoefficientMapNumeratorPF_global, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_global.olean", false),
    (`Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_injective, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_injective.olean", false),
    (`Theorems.Thm_ZetaNine_CoefficientMapNumeratorPF_injective, "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/pfi1/b/lib/lean/Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_injective.olean", false)]
  for (module, path, shouldBeImported) in expected do
    let actual ← findOLean module
    let actualReal ← realPathNormalized actual
    let expectedReal ← realPathNormalized (System.FilePath.mk path)
    unless actualReal == expectedReal do throwError "Actual findOLean did not use independently compiled SOURCE: {module}"
    let imported := env.header.moduleNames.contains module
    unless imported == shouldBeImported do throwError "Actual module-header membership differs: {module}"
    IO.println (Json.mkObj [("kind",Json.str "independent_actual_findOLean"),
      ("context",Json.str "native"),("module",Json.str module.toString),
      ("actual_path",Json.str actual.toString),("actual_real_path",Json.str actualReal.toString),
      ("expected_real_path",Json.str expectedReal.toString),("path_equal",toJson true),
      ("module_header_imported",toJson imported),("expected_header_imported",toJson shouldBeImported)]).compress
  IO.println (Json.mkObj [("kind",Json.str "independent_full_actual_module_header"),
    ("context",Json.str "native"),("modules",toJson (env.header.moduleNames.toList.map Name.toString))]).compress
