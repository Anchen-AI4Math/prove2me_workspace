import Lean
import Definitions.Def_ThreeSum1962Source_Bundle18
import Definitions.Def_ThreeSum1960614_Analysis

open Lean Elab
set_option maxHeartbeats 0
set_option maxRecDepth 20000

private partial def alphaPublicInterface (expr : Expr) : Expr :=
  match expr with
  | .app f a => .app (alphaPublicInterface f) (alphaPublicInterface a)
  | .lam _ t b i => .lam .anonymous (alphaPublicInterface t) (alphaPublicInterface b) i
  | .forallE _ t b i => .forallE .anonymous (alphaPublicInterface t) (alphaPublicInterface b) i
  | .letE _ t v b d => .letE .anonymous (alphaPublicInterface t) (alphaPublicInterface v) (alphaPublicInterface b) d
  | .mdata _ e => alphaPublicInterface e
  | .proj n i e => .proj n i (alphaPublicInterface e)
  | e => e

run_meta do
  let env ← getEnv
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/public-theorem-probe-inputs.json"
  let items ← match Json.parse raw >>= Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  let mut text := "set_option autoImplicit false\nset_option relaxedAutoImplicit false\nset_option Elab.async false\n"
  let mut publicEnv := env
  let mut errors : Array Json := #[]
  let mut output : Array Json := #[]
  for item in items do
    let name ← match item.getObjValAs? String "theorem_name" with
      | .ok value => pure value
      | .error message => throwError message
    let preamble ← match item.getObjValAs? String "preamble" with
      | .ok value => pure value
      | .error message => throwError message
    let statement ← match item.getObjValAs? String "formal_statement" with
      | .ok value => pure value
      | .error message => throwError message
    let context := Parser.mkInputContext preamble "public-interface-preamble"
    let (_,initial,initialMessages) ← Parser.parseHeader context
    let mut state := initial
    let mut messages := initialMessages
    let mut scope := ""
    repeat
      let (command,next,nextMessages) := Parser.parseCommand context {env,options := {}} state messages
      state := next
      messages := nextMessages
      if command.isOfKind ``Parser.Command.eoi then break
      if [``Parser.Command.universe, ``Parser.Command.variable, ``Parser.Command.open,
          ``Parser.Command.include, ``Parser.Command.omit].contains command.getKind then
        let some first := command.getPos? | continue
        let some last := command.getTailPos? | continue
        scope := scope ++ (preamble.toUTF8.extract first.byteIdx last.byteIdx |> String.fromUTF8!) ++ "\n"
    let code := "set_option autoImplicit false\nset_option relaxedAutoImplicit false\nset_option Elab.async false\nsection\n" ++ scope ++ statement ++ "\nend\n"
    text := text ++ "\n-- " ++ name ++ "\n" ++ code
    let input := Parser.mkInputContext code ("public-interface:" ++ name)
    let (_,parserState,initialMessages) ← Parser.parseHeader input
    let commands := Command.mkState publicEnv initialMessages {}
    let result ← IO.processCommands input parserState commands
    let mut itemErrors : Array String := #[]
    for message in result.commandState.messages.toList do
      if message.severity == .error then itemErrors := itemErrors.push (← message.toString)
    if !itemErrors.isEmpty then
      errors := errors.push <| Json.mkObj [("name",toJson name),("errors",toJson itemErrors)]
      continue
    publicEnv := result.commandState.env
    if let some ci := publicEnv.find? name.toName then
      if ci.type.hasMVar then throwError "Unresolved metavariable in public interface {name}"
      let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
      let normalized := alphaPublicInterface (ci.type.instantiateLevelParams ci.levelParams levels)
      output := output.push <| Json.mkObj [("name",toJson name),
        ("levelParams",toJson (ci.levelParams.map Name.toString)),("rawType",toJson (reprStr ci.type)),
        ("universeCount",toJson ci.levelParams.length),("type",toJson (reprStr normalized))]
  IO.FS.writeFile "missions/3sum-1960614/verification/public-theorem-probe-source.lean.txt" text
  IO.FS.writeFile "missions/3sum-1960614/verification/public-theorem-probe-errors.json" (toJson errors).pretty
  IO.FS.writeFile "missions/3sum-1960614/verification/public-theorem-probe-types.json" (Json.arr output).pretty
  logInfo s!"elaborated {output.size}/{items.size} existing public theorem types; errors {errors.size}"
