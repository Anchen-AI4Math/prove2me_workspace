"""Actual source-span endpoint full kernel types plus independent native/staged controls."""
import review_driver as d
import argparse,json
p=argparse.ArgumentParser();p.add_argument('--lane-granted',action='store_true',required=True);p.parse_args()
c=d.context();plan=d.load(d.OUT/'target-plan.json');source=c['source']
assert all((d.OUT/'staged'/f['root_relative_destination']).read_bytes()==(d.OUT.parent/'staged'/f['root_relative_destination']).read_bytes() for f in d.load(d.OUT.parent/'root-copy-plan.json')['files'])
for i,context in enumerate(['native','stage0','stage1','stage2']):
 selected=list(range(3)) if context=='native' else [i-1]
 module=d.NATIVE if context=='native' else plan['targets'][i-1]['local_solution'].removesuffix('.lean').replace('/','.')
 text='import '+module+'\nimport Lean\nset_option autoImplicit false\nnoncomputable section\nopen Polynomial '+d.NS+'\nnamespace IndependentConnectionExpected\n'
 pairs=[]
 for j in selected:
  name=d.TARGETS[j];full=d.NS+'.'+name;decl=c['declaration'](full);a,v=decl['declStart']['offset'],decl['valStart']['offset']
  refs=[r for r in c['refs'] if r['const']==full and a<=r['start']['offset']<v];assert len(refs)==1
  sig=source[refs[0]['end']['offset']:v].decode()
  callee=full if context=='native' else d.NS+'.checked_'+name
  actual=full if context=='native' else 'solution'
  expected='IndependentConnectionExpected.expected_'+name
  text+='theorem expected_'+name+sig+':= '+callee+' '+d.ARGS[j]+'\n\n';pairs.append((actual,expected))
 text+='end IndependentConnectionExpected\nopen Lean Meta\nrun_meta do\n'
 for actual,expected in pairs:
  text+='''  do
    let a ← getConstInfo `'''+actual+'''
    let e ← getConstInfo `'''+expected+'''
    let equal ← isDefEq a.type e.type
    unless equal do throwError "Complete original source type differs"
    let ax ← collectAxioms `'''+expected+'''
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_endpoint_kernel_type"),
      ("source",Json.str "'''+actual+'''"),("expected",Json.str "'''+expected+'''"),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr e.type)),
      ("axioms",toJson (ax.toList.map Name.toString))]).compress
'''
 filename='own-kernel-'+context+'.lean';d.write(d.OUT/filename,text);d.write(d.PROJECT/filename,text);d.run('own-kernel-'+context,['lean',filename])
native=(d.OUT/'own-boundary-native.lean').read_bytes()
solution=plan['targets'][2]['local_solution'].removesuffix('.lean').replace('/','.')
staged=native.replace(('import '+d.NATIVE).encode(),('import '+solution).encode()).replace(b'  connection_five_systems_unique ',b'  checked_connection_five_systems_unique ')
for label,text in [('own-boundary-native',native),('own-boundary-staged',staged)]:
 filename=label+'.lean';d.write(d.OUT/filename,text);d.write(d.PROJECT/filename,text);d.run(label,['lean',filename])
modules=[d.NATIVE,d.DEF_PATH.removesuffix('.lean').replace('/','.')]+[t['local_'+kind].removesuffix('.lean').replace('/','.') for t in plan['targets'] for kind in ['solution','reference']]+['NativeValueComparisonDefinition','StagedValueComparisonDefinition']
probe='''import Lean
open Lean
run_meta do
  let path ← IO.getEnv "LEAN_PATH"
  IO.println (Json.mkObj [("kind",Json.str "actual_search_path"),("LEAN_PATH",Json.str (path.getD ""))]).compress
  for m in ['''+','.join('`'+m for m in modules)+'''] do
    let p ← findOLean m
    IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str m.toString),("olean",Json.str p.toString)]).compress
'''
d.write(d.OUT/'own-all-resolver.lean',probe);d.write(d.PROJECT/'own-all-resolver.lean',probe);d.run('own-all-resolver',['lean','own-all-resolver.lean'])
print('Six actual endpoint kernel-type comparisons and own8 controls in native/staged environments finished',flush=True)
