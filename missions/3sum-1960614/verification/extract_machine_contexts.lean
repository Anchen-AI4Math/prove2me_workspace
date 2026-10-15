import Submission.ThreeSum.CompleteCostBridge
import Submission.ThreeSum.ModelWitnessBounds

open Lean
open Finset
open scoped BigOperators Topology

private partial def nodesOfKind (stx : Syntax) (kind : SyntaxNodeKind) : Array Syntax :=
  if stx.getKind == kind then #[stx]
  else stx.getArgs.foldl (fun acc child => acc ++ nodesOfKind child kind) #[]

private partial def nestedNodesOfKind (stx : Syntax) (kind : SyntaxNodeKind) : Array Syntax :=
  (if stx.getKind == kind then #[stx] else #[]) ++
    stx.getArgs.foldl (fun acc child => acc ++ nestedNodesOfKind child kind) #[]

private partial def identifiers (stx : Syntax) : Array Json :=
  if stx.isIdent then
    match stx.getPos?,stx.getTailPos? with
    | some first,some last => #[Json.mkObj [
        ("name",toJson stx.getId.toString),("startOffset",toJson first.byteIdx),
        ("endOffset",toJson last.byteIdx)]]
    | _,_ => #[]
  else stx.getArgs.foldl (fun acc child => acc ++ identifiers child) #[]

private def range (stx : Syntax) : Json :=
  match stx.getPos?,stx.getTailPos? with
  | some first,some last => Json.mkObj [
      ("startOffset",toJson first.byteIdx),("endOffset",toJson last.byteIdx)]
  | _,_ => Json.null

private partial def headerKeywords (stx : Syntax) : Array Json :=
  if stx.isAtom && (stx.getAtomVal == "module" || stx.getAtomVal == "prelude") then
    #[range stx]
  else stx.getArgs.foldl (fun acc child => acc ++ headerKeywords child) #[]

/- Only the non-declaration scope commands preceding `in` are supplied here.
   Declaration/proof cuts and resolved constant references remain exclusively
   the official Stage 2 oracle's responsibility. -/
private def identifierJson (stx : Syntax) : Json :=
  Json.mkObj [("name",toJson stx.getId.toString),("range",range stx)]

private def describeOpenDecl (stx : TSyntax ``Parser.Command.openDecl) : Json := Id.run do
  match stx with
  | `(Parser.Command.openDecl| scoped $nss*) =>
      return Json.mkObj [("variant",toJson "scoped"),("namespaces",Json.arr (nss.map identifierJson))]
  | `(Parser.Command.openDecl| $ns ($ids*)) =>
      return Json.mkObj [("variant",toJson "explicit"),("namespace",identifierJson ns),
        ("members",Json.arr (ids.map identifierJson))]
  | `(Parser.Command.openDecl| $ns hiding $ids*) =>
      return Json.mkObj [("variant",toJson "hiding"),("namespace",identifierJson ns),
        ("members",Json.arr (ids.map identifierJson))]
  | `(Parser.Command.openDecl| $ns renaming $[$froms -> $tos],*) =>
      return Json.mkObj [("variant",toJson "renaming"),("namespace",identifierJson ns),
        ("members",Json.arr (froms.map identifierJson)),("aliases",Json.arr (tos.map identifierJson))]
  | `(Parser.Command.openDecl| $nss*) =>
      return Json.mkObj [("variant",toJson "simple"),("namespaces",Json.arr (nss.map identifierJson))]
  | _ => return Json.mkObj [("variant",toJson "unsupported")]

private def opensJson (stx : Syntax) : Json :=
  -- `openDecl` is a pseudo syntax kind: its concrete alternatives are
  -- openSimple/openOnly/openHiding/etc. The command's second argument is
  -- the parser-provided declaration, so never search for the pseudo kind.
  if stx.isOfKind ``Parser.Command.open then
    Json.arr #[describeOpenDecl ⟨stx[1]⟩]
  else Json.arr #[]

private partial def scopeWrappers (stx : Syntax) : Array Json :=
  if stx.isOfKind ``Parser.Command.in then
    let context := stx[0]
    let inToken := stx[1]
    match context.getPos?,context.getTailPos?,inToken.getTailPos? with
    | some first,some last,some afterIn =>
        #[Json.mkObj [
          ("syntaxKind",toJson context.getKind.toString),
          ("startOffset",toJson first.byteIdx),("endOffset",toJson last.byteIdx),
          ("afterInOffset",toJson afterIn.byteIdx),("opens",opensJson context),
          ("identifiers",Json.arr (identifiers context))]] ++ scopeWrappers stx[2]
    | _,_,_ => #[]
  else #[]

/- Parse supplementary context in one already-built environment. This neither
   elaborates source declarations again nor supplies declaration dependency,
   proof-cut or resolved-reference facts. Those always come from the official
   two-stage scripts, and command envelopes are cross-checked before use. -/
run_meta do
  let env ← getEnv
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-context-inputs.json"
  let inputs ← match Json.parse raw >>= Json.getArr? with
    | .ok values => pure values
    | .error message => throwError message
  let mut output : Array Json := #[]
  let mut failures : Array String := #[]
  for item in inputs do
    let module ← match item.getObjValAs? String "module" with
      | .ok value => pure value
      | .error message => throwError message
    let path ← match item.getObjValAs? String "path" with
      | .ok value => pure value
      | .error message => throwError message
    let text ← IO.FS.readFile path
    let input := Parser.mkInputContext text path
    let (header,initial,initialMessages) ← Parser.parseHeader input
    let mut state := initial
    let mut messages := initialMessages
    let mut commands : Array Json := #[]
    repeat
      let (cmd,next,nextMessages) := Parser.parseCommand input {env,options := {}} state messages
      state := next
      messages := nextMessages
      if cmd.isOfKind ``Parser.Command.eoi then break
      let some first := cmd.getPos? | continue
      let some last := cmd.getTailPos? | continue
      let hasDeclaration := !(nodesOfKind cmd ``Parser.Command.declaration).isEmpty ||
        !(nodesOfKind cmd ``Parser.Command.declId).isEmpty
      let attrs := nodesOfKind cmd ``Parser.Term.attributes
      commands := commands.push <| Json.mkObj [
        ("syntaxKind",toJson cmd.getKind.toString),
        ("startOffset",toJson first.byteIdx),("endOffset",toJson last.byteIdx),
        ("hasDeclaration",toJson hasDeclaration),
        ("identifiers",Json.arr (if hasDeclaration then #[] else identifiers cmd)),
        -- Lexical shape only: resolved constants and every edit range still
        -- come from the unmodified official Stage 2 reference facts.
        ("lexicalIdentifiers",Json.arr (identifiers cmd)),
        ("dotSelectors",Json.arr (
          (nestedNodesOfKind cmd ``Parser.Term.proj).foldl (fun acc stx => acc ++ identifiers stx[2]) #[] ++
          (nestedNodesOfKind cmd ``Parser.Term.dotIdent).foldl (fun acc stx => acc ++ identifiers stx[1]) #[])),
        ("caseLabels",Json.arr ((nodesOfKind cmd ``Parser.Tactic.inductionAltLHS).foldl
          (fun acc stx => acc ++ identifiers stx[1]) #[])),
        ("opens",if hasDeclaration then Json.arr #[] else opensJson cmd),
        ("scopeWrappers",Json.arr (scopeWrappers cmd)),
        ("attributes",Json.arr (attrs.map range))]
    let mut errorTexts : Array String := #[]
    if messages.hasErrors then
      failures := failures.push module
      for message in messages.toList do
        errorTexts := errorTexts.push (← message.toString)
      IO.eprintln s!"context parse failed: {module}"
    output := output.push <| Json.mkObj [
      ("module",toJson module),("headerEndOffset",toJson initial.pos.byteIdx),
      ("headerKeywordRanges",Json.arr (headerKeywords header.raw)),
      ("imports",Json.arr ((nodesOfKind header.raw ``Parser.Module.import).map fun stx =>
        Json.mkObj [("range",range stx),("identifiers",Json.arr (identifiers stx))])),
      ("commands",Json.arr commands),("parsePassed",toJson (!messages.hasErrors)),
      ("errors",Json.arr (errorTexts.map Json.str))]
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-scope-contexts.json"
    (Json.arr output).pretty
  -- This cache is specific to this task's frozen native imports/toolchain.
  -- Source fingerprints are checked by validate_machine_contexts.py.
  let namespaceCache : System.FilePath := "missions/3sum-1960614/verification/machine-external-namespaces.json"
  unless (← namespaceCache.pathExists) do
    let mut externalNamespaces : Std.HashSet Name := {}
    for (name,_) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      let some module := env.header.moduleNames[index.toNat]? | continue
      if module.toString.startsWith "Submission." || module.toString.startsWith "Closed3Sum." then continue
      let mut namespaceName := name.getPrefix
      while !namespaceName.isAnonymous do
        externalNamespaces := externalNamespaces.insert namespaceName
        namespaceName := namespaceName.getPrefix
    IO.FS.writeFile namespaceCache (toJson (externalNamespaces.toArray.map Name.toString)).compress
  logInfo s!"parsed {output.size} module contexts; failures: {failures.size}"
  unless failures.isEmpty do
    throwError "Supplementary context parsing failed in {failures.size} modules; inspect saved diagnostics"
