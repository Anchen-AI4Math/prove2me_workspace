import Lean
open Lean

private partial def imports (stx : Syntax) : Array String :=
  if stx.isOfKind ``Parser.Module.import then
    stx.getArgs.foldl (fun acc child => if child.isIdent then acc.push child.getId.toString else acc) #[]
  else stx.getArgs.foldl (fun acc child => acc ++ imports child) #[]

run_meta do
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/public-stub-mirror-inputs.json"
  let items ← match Json.parse raw >>= Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  let mut output : Array Json := #[]
  for item in items do
    let name ← match item.getObjValAs? String "theorem_name" with
      | .ok value => pure value
      | .error message => throwError message
    let preamble ← match item.getObjValAs? String "preamble" with
      | .ok value => pure value
      | .error message => throwError message
    let input := Parser.mkInputContext preamble name
    let (header,_,messages) ← Parser.parseHeader input
    if messages.hasErrors then throwError "Invalid published import header: {name}"
    output := output.push <| Json.mkObj [("name",toJson name),("imports",toJson (imports header.raw))]
  IO.FS.writeFile "missions/3sum-1960614/verification/public-stub-mirror-headers.json" (Json.arr output).compress
  logInfo s!"parsed {output.size} exact public theorem headers"
