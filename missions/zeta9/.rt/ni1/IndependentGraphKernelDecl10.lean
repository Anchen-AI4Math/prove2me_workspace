import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let stdout ← IO.getStdout
  let specs : List (String × String) := [("ZetaNine.CoefficientMapKernelBridge.actual_R_shift_A_equals_R_B", "theorem")]
  let env ← getEnv
  let constants := env.constants.toList
  for (wanted, sourceKind) in specs do
    stdout.putStrLn ("PHASE start " ++ wanted)
    stdout.flush
    let found := constants.filter fun (name, _) =>
      name.toString == wanted || name.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Exact source declaration resolution failed {wanted}"
    let (name, ci) := found.head!
    let actualKind := match ci with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "proof"
      | _ => "other"
    let expectedKind := if sourceKind == "def" || sourceKind == "abbrev" then "definition" else "proof"
    unless actualKind == expectedKind do throwError "Source declaration kind mismatch {name}"
    let axioms ← collectAxioms name
    unless axioms.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard source axiom {name}"
    stdout.putStrLn "PHASE standard_axioms_complete"
    stdout.flush
    let typePP ← ppExpr ci.type
    let value := ci.value? (allowOpaque := true)
    let fullType := reprStr ci.type
    stdout.putStrLn "PHASE full_type_complete"
    stdout.flush
    let fullValue := reprStr value
    stdout.putStrLn ("PHASE full_value_complete_bytes " ++ toString fullValue.utf8ByteSize)
    stdout.flush
    IO.println (Json.mkObj [("kind",Json.str "actual_source_declaration"),
      ("source_kind",Json.str sourceKind),("source_name",Json.str wanted),
      ("actual_name",Json.str name.toString),("full_type_expr",Json.str fullType),
      ("full_value_expr",Json.str fullValue),("full_type_pp_diagnostic",Json.str typePP.pretty),
      ("axioms",toJson (axioms.toList.map Name.toString))]).compress
