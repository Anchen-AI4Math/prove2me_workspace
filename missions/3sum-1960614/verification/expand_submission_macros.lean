import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Lean
open Lean Elab

set_option maxRecDepth 30000
set_option maxHeartbeats 0

private def customKind (env : Environment) (kind : Name) : Bool :=
  (macroAttribute.getEntries env kind).any fun entry =>
    !entry.isBuiltin && match env.getModuleIdxFor? entry.declName with
      | none => true
      | some idx =>
        let module := env.header.moduleNames[idx.toNat]!.toString
        module.startsWith "Definitions.Def_ThreeSum1960614_Machine_" ||
          module.startsWith "Definitions.Def_ThreeSum1962Source_" ||
          module.startsWith "Definitions.Def_APSPSource_"

private partial def expandCustom (env : Environment) (stx : Syntax) : MacroM Syntax := do
  if customKind env stx.getKind then
    let some result ← expandMacro? stx | Macro.throwError "Unsupported project macro"
    expandCustom env result
  else match stx with
    | .node info kind args => return .node info kind (← args.mapM (expandCustom env))
    | other => return other

private partial def qualifyResolved : Syntax → Syntax
  | original@(.ident _ _ name pre) =>
    let candidates := pre.filterMap fun
      | .decl resolved fields => some (fields.foldl Name.str resolved.eraseMacroScopes)
      | _ => none
    let candidates := candidates.eraseDups
    let preferred := candidates.find? fun n => n.toString.startsWith "ThreeSum1960614.Machine."
    match preferred.orElse (fun _ => candidates.head?) with
    | some resolved => mkIdentFrom original (Name.str .anonymous "_root_" ++ resolved)
    | none =>
      match pre.head? with
      | some (.namespace ns) => mkIdentFrom original (Name.str .anonymous "_root_" ++ ns.eraseMacroScopes)
      | _ =>
        if name.hasMacroScopes then
          mkIdentFrom original (Name.mkSimple ("p2m_macro_" ++ toString (hash name)))
        else original
  | .node info kind args => .node info kind (args.map qualifyResolved)
  | other => other

private partial def macroEdits (input : Parser.InputContext) (stx : Syntax) : Command.CommandElabM (Array Json) := do
  let env ← getEnv
  if customKind env stx.getKind then
    let some first := stx.getPos? | throwError "Macro has no source start"
    let some last := stx.getTailPos? | throwError "Macro has no source end"
    let kind := stx.getKind
    let category := if (Parser.getParserCategory? env `tactic).any (fun c => c.kinds.contains kind) then `tactic else `term
    let expanded ← liftMacroM (expandCustom env stx)
    let formatted ← Command.liftCoreM (PrettyPrinter.ppCategory category (qualifyResolved expanded))
    let replacement := "(" ++ formatted.pretty 1000000 ++ ")"
    let column := (input.fileMap.toPosition first).column
    let padding := String.ofList (List.replicate column ' ')
    let replacement := replacement.replace "\n" ("\n" ++ padding)
    return #[Json.mkObj [("start",toJson first.byteIdx),("end",toJson last.byteIdx),
      ("replacement",toJson replacement),("kind",toJson kind.toString)]]
  else
    stx.getArgs.foldlM (fun result child => return result ++ (← macroEdits input child)) #[]

private def convert (env : Environment) (path : String) : IO Json := do
  let text ← IO.FS.readFile ("missions/3sum-1960614/verification/server-macro-originals/" ++ path)
  let input := Parser.mkInputContext text path
  let (_,parserState,messages) ← Parser.parseHeader input
  let action : Frontend.FrontendM (Array Json) := do
    let mut edits := #[]
    repeat
      Frontend.updateCmdPos
      let state ← Frontend.getCommandState
      let scope := state.scopes.head!
      let (cmd,next,messages) := Parser.parseCommand input
        {env := state.env,options := scope.opts,currNamespace := scope.currNamespace,openDecls := scope.openDecls}
        (← Frontend.getParserState) state.messages
      Frontend.setParserState next
      Frontend.setMessages messages
      if cmd.isOfKind ``Parser.Command.eoi then break
      let some first := cmd.getPos? | continue
      let some last := cmd.getTailPos? | continue
      if cmd.isOfKind ``Parser.Command.macro || cmd.isOfKind ``Parser.Command.mixfix then
        -- Only generated local aliases need replaying: their definitions are
        -- pure source-translation helpers, never mathematical declarations.
        if cmd.isOfKind ``Parser.Command.macro && (cmd[2].reprint.getD "").trimAscii.toString == "local" then
          Frontend.elabCommandAtFrontend cmd
        edits := edits.push <| Json.mkObj [("start",toJson first.byteIdx),("end",toJson last.byteIdx),
          ("replacement",toJson ""),("kind",toJson cmd.getKind.toString)]
      else if cmd.isOfKind ``Parser.Command.namespace || cmd.isOfKind ``Parser.Command.section || cmd.isOfKind ``Parser.Command.end then
        Frontend.elabCommandAtFrontend cmd
      else
        edits := edits ++ (← Frontend.runCommandElabM (macroEdits input cmd))
    let finalState ← Frontend.getCommandState
    if finalState.messages.hasErrors then
      let mut texts := #[]
      for message in finalState.messages.toList do texts := texts.push (← message.toString)
      throw (IO.userError (String.intercalate "\n" texts.toList))
    return edits
  let commandState := Command.mkState env messages (({} : Options).set `maxRecDepth (30000 : Nat) |>.set `maxHeartbeats (0 : Nat))
  let (edits,_) ← (action {inputCtx := input}).run {commandState,parserState,cmdPos := parserState.pos}
  return Json.mkObj [("path",toJson path),("edits",Json.arr edits)]

run_meta do
  let env ← getEnv
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/server-macro-inputs.json"
  let paths ← ofExcept (Json.parse raw >>= Json.getArr?)
  let handle ← IO.FS.Handle.mk "missions/3sum-1960614/verification/server-macro-edits-v2.jsonl" .write
  for item in paths do
    let path ← ofExcept item.getStr?
    let result ← convert env path
    handle.putStrLn result.compress
    handle.flush
  logInfo s!"Translated macros in {paths.size} files without elaborating mathematical declarations"
