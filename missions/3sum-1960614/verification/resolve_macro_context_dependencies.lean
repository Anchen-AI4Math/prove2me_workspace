import Submission.ThreeSum.CompleteCostBridge
import Submission.ThreeSum.ModelWitnessBounds
import Lean
open Lean
set_option maxHeartbeats 0

private def stringField (item : Json) (name : String) : MetaM String :=
  match item.getObjValAs? String name with
  | .ok value => pure value
  | .error message => throwError message

private def arrayField (item : Json) (name : String) : MetaM (Array Json) :=
  match item.getObjValAs? (Array Json) name with
  | .ok value => pure value
  | .error message => throwError message

run_meta do
  let env ← getEnv
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-macro-resolution-inputs.json"
  let items ← match Json.parse raw >>= Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  let mut output : Array Json := #[]
  for item in items do
    let module ← stringField item "module"
    let namespaceName := ( ← stringField item "namespace").toName
    let mut opened : List OpenDecl := []
    for entry in ← arrayField item "opens" do
      let name := ( ← stringField entry "namespace").toName
      let current := ( ← stringField entry "context").toName
      let namespaces ← withTheReader Core.Context (fun c => {c with currNamespace := current}) <| resolveNamespace (mkIdent name)
      for ns in namespaces do
        match entry.getObjValAs? String "member" with
        | .ok member => opened := .explicit member.toName (ns ++ member.toName) :: opened
        | .error _ => opened := .simple ns [] :: opened
    let mut deps : Array String := #[]
    for value in ← arrayField item "identifiers" do
      let .ok text := value.getStr? | throwError "Invalid macro identifier"
      let names ← withTheReader Core.Context (fun c => {c with currNamespace := namespaceName, openDecls := opened}) <| resolveGlobalName text.toName
      for (name,_) in names do
        if let some index := env.getModuleIdxFor? name then
          if let some owner := env.header.moduleNames[index.toNat]? then
            if owner.toString.startsWith "Submission." || owner.toString.startsWith "Closed3Sum." then
              deps := deps.push name.toString
    output := output.push <| Json.mkObj [("module",toJson module),("namespace",toJson namespaceName.toString),
      ("offset",(item.getObjVal? "offset").toOption.getD Json.null),("dependencies",toJson deps)]
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-macro-context-dependencies.json" (Json.arr output).pretty
  logInfo s!"resolved project names for {output.size} source macro commands"
