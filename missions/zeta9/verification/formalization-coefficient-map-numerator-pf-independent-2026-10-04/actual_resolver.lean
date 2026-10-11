import Lean
open Lean
run_meta do
  let ep ← IO.getEnv "LEAN_PATH"
  IO.println (Json.mkObj [("kind",Json.str "actual_environment"),
    ("LEAN_PATH",Json.str (ep.getD "")),("Lean_version",Json.str Lean.versionString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_HarmonicStability
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_HarmonicStability"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMap
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMap"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapJet
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapJet"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapInjectivity
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapInjectivity"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapPartialFractions
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapPartialFractions"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapReflection
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapReflection"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapFiniteSum
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapFiniteSum"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapSummation
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapSummation"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapAggregate
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapAggregate"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapShiftDegree
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapShiftDegree"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapTelescoper
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapTelescoper"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapKernelBridge
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapKernelBridge"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapConnection
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapConnection"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapParameterShift
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapParameterShift"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapFormalTransportData
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapFormalTransportData"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions"),("object",Json.str p.toString)]).compress
  let p ← findOLean `IndependentValues
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "IndependentValues"),("object",Json.str p.toString)]).compress
  let p ← findOLean `ValueAliases
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "ValueAliases"),("object",Json.str p.toString)]).compress
