"""Probe existing public theorem interfaces without rewriting their statements.

Only native types whose data dependencies pass the conservative compatibility
preview are considered. The exact API statements are elaborated in the public
definition environment; source-universe commands are obtained with Lean's
parser, and no proof-side preamble helpers are executed.
"""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
VER=HERE/'verification'
rows={r['name']:r for r in map(json.loads,(VER/'machine-decl-graph.jsonl').read_text(encoding='utf-8').splitlines())}
catalog=json.loads((VER/'machine-public-1962-catalog.json').read_text(encoding='utf-8'))['records']
compatible=set(json.loads((VER/'extended-reuse-compatibility-preview.json').read_text(encoding='utf-8'))['compatible_names'])
records={r['theorem_name']:r for r in catalog if r['status']!='Definition' and r['theorem_name'] in rows}
eligible=set(records)
while True:
    removed={name for name in eligible if any(dep in rows and dep not in compatible and dep not in eligible
                                            for dep in rows[name]['typeDeps'])}
    if not removed:break
    eligible-=removed
remaining={n:set(rows[n]['typeDeps']) & eligible for n in eligible};order=[]
while remaining:
    ready=sorted(n for n,deps in remaining.items() if not deps)
    assert ready,'Unexpected theorem type dependency cycle'
    order+=ready
    for name in ready:del remaining[name]
    for deps in remaining.values():deps.difference_update(ready)
selected=[records[n] for n in order if n not in compatible]
(VER/'public-theorem-probe-inputs.json').write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
code='''import Lean
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
  let mut text := "set_option autoImplicit false\\nset_option relaxedAutoImplicit false\\nset_option Elab.async false\\n"
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
        scope := scope ++ (preamble.toUTF8.extract first.byteIdx last.byteIdx |> String.fromUTF8!) ++ "\\n"
    let code := "set_option autoImplicit false\\nset_option relaxedAutoImplicit false\\nset_option Elab.async false\\nsection\\n" ++ scope ++ statement ++ "\\nend\\n"
    text := text ++ "\\n-- " ++ name ++ "\\n" ++ code
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
'''
(VER/'probe_public_theorem_types.lean').write_text(code,encoding='utf-8',newline='\n')
print('Prepared exact public-interface probes:',len(selected),'native-compatible candidates; omitted',len(records)-len(eligible),'with changed data dependencies.')
