from run_author import *
import re
declarations=[]
for short in ['Data','Bounds']:
 source=TASK/'formalization'/('CoefficientMapFormalTransport'+short+'.lean')
 declarations += ['ZetaNine.CoefficientMapFormalTransport'+short+'.'+n for n in re.findall(r'^(?:def|theorem) (\w+)',source.read_text(encoding='utf-8-sig'),re.M)]
assert len(declarations)==33
program='''import missions.zeta9.formalization.CoefficientMapFormalTransportBounds
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  for name in ['''+','.join('`'+n for n in declarations)+'''] do
    let ci ← getConstInfo name
    let axioms ← collectAxioms name
    let value := match ci with | .defnInfo d => some d.value | _ => none
    let kind := match ci with | .defnInfo _ => "def" | .thmInfo _ => "theorem" | _ => "other"
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("kind",Json.str kind),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("full_definition_value_expression_repr",value.map (fun x => Json.str (reprStr x)) |>.getD Json.null),
      ("axioms",toJson (axioms.toList.map Name.toString))]).compress
'''
write(OUT/'source-full-audit.lean',program)
modules=load(OUT/'preparation-state.json')['parent_modules']+['missions.zeta9.formalization.CoefficientMapFormalTransportData','missions.zeta9.formalization.CoefficientMapFormalTransportBounds']
write(OUT/'resolver.lean','''import Lean
open Lean
def main : IO Unit := do
  let path ← IO.getEnv "LEAN_PATH"
  IO.println ((Json.mkObj [("kind",Json.str "actual_search_path"),("LEAN_PATH",Json.str (path.getD ""))]).compress)
  for m in ('''+json.dumps(modules)+''' : List String) do
    let p ← Lean.findOLean ((m.splitOn ".").foldl Name.str Name.anonymous)
    IO.println ((Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str m),("resolved_olean",Json.str p.toString)]).compress)
''')
print('Pure prepared33 full source declarations and16 resolver probes; no Lean invocation')
