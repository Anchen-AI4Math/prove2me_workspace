"""Prepare compiler name-resolution requests for source macro identifiers."""
import json
from machine_skeleton import Renderer, VER, COMMAND

plan = json.loads((VER / 'machine-node-classification.json').read_text(encoding='utf-8'))
renderer = Renderer(plan)
items = []
for module in renderer.sources:
    for command in renderer.contexts[module]['commands']:
        if command['syntaxKind'] not in (COMMAND + 'macro', COMMAND + 'mixfix'):
            continue
        frames = renderer.scope_stack(module, command['startOffset'])
        opened = []
        for frame in frames:
            for context in frame['commands']:
                if context['syntaxKind'] != COMMAND + 'open':
                    continue
                for declaration in context['opens']:
                    if declaration['variant'] == 'simple':
                        for ns in declaration['namespaces']:
                            opened.append({'namespace': ns['name'], 'context': frame['namespace']})
                    elif declaration['variant'] == 'explicit':
                        for member in declaration['members']:
                            opened.append({'namespace': declaration['namespace']['name'],
                                           'context': frame['namespace'], 'member': member['name']})
        items.append({'module': module, 'namespace': frames[-1]['namespace'],
                      'offset': command['startOffset'], 'opens': opened,
                      'identifiers': sorted({i['name'] for i in command['lexicalIdentifiers']})})
(VER / 'machine-macro-resolution-inputs.json').write_text(json.dumps(items) + '\n', encoding='utf-8')
code = '''import Submission.ThreeSum.CompleteCostBridge
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
'''
(VER / 'resolve_macro_context_dependencies.lean').write_text(code, encoding='utf-8', newline='\n')
print('Prepared macro context name resolution:', len(items), 'source commands.')
