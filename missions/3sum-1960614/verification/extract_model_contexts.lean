import Submission.ThreeSum.ModelWitnessBounds

open Lean

private partial def identifiers (stx : Syntax) : Array String :=
  if stx.isIdent then #[stx.getId.toString]
  else stx.getArgs.foldl (fun acc child => acc ++ identifiers child) #[]

/- Supplementary scope context only. It never infers declaration spans or
   proof boundaries. All declarations have already been blanked at the byte
   ranges emitted by the official Stage 2 oracle. -/
run_meta do
  let env ← getEnv
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/model-context-inputs.json"
  let inputs ← match Json.parse raw >>= Json.getArr? with
    | .ok values => pure values
    | .error message => throwError message
  let mut output : Array Json := #[]
  for item in inputs do
    let module ← match item.getObjValAs? String "module" with
      | .ok value => pure value
      | .error message => throwError message
    let path ← match item.getObjValAs? String "path" with
      | .ok value => pure value
      | .error message => throwError message
    let text ← IO.FS.readFile path
    let input := Parser.mkInputContext text path
    let (_, initial, initialMessages) ← Parser.parseHeader input
    let mut state := initial
    let mut messages := initialMessages
    let mut commands : Array Json := #[]
    repeat
      let (cmd, next, nextMessages) := Parser.parseCommand input { env, options := {} } state messages
      state := next
      messages := nextMessages
      if cmd.isOfKind ``Parser.Command.eoi then break
      let some first := cmd.getPos? | continue
      let some last := cmd.getTailPos? | continue
      commands := commands.push <| Json.mkObj [
        ("syntaxKind", toJson cmd.getKind.toString),
        ("startOffset", toJson first.byteIdx),
        ("endOffset", toJson last.byteIdx),
        ("identifiers", toJson (identifiers cmd))]
    if messages.hasErrors then
      for message in messages.toList do
        IO.eprintln (← message.toString)
      throwError "Context parse failed for {module}"
    output := output.push <| Json.mkObj [("module", toJson module),
      ("headerEndOffset", toJson initial.pos.byteIdx), ("commands", toJson commands)]
  IO.FS.writeFile "missions/3sum-1960614/verification/model-scope-contexts.json"
    (Json.arr output).pretty
  logInfo s!"parsed scope contexts for {output.size} modules"
