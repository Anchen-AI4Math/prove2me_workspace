import inspect_prepare as p
from prepare_controls import save
plan=p.load(p.OUT/'control-preparation-v3.json')
prep=p.load(p.OUT/'source-preparation.json')
modules=[r['module'] for r in prep['native_sources']]+[r['module'] for r in prep['serializer_sources']]+[plan['assertions']['module'],plan['semantic']['module']]
assert len(modules)==25 and len(set(modules))==25
text='import OutputsIndependentSemanticV3\nimport Lean\nopen Lean Meta\nset_option maxHeartbeats 8000000\nrun_meta do\n'
for name in modules:
 expected=str((p.PROJECT/'b/lib/lean'/(name.replace('.','/')+'.olean')).resolve())
 text+='  let chosen ← findOLean `'+name+'\n'
 text+='  let resolved ← IO.FS.realPath chosen\n'
 text+='  let expected ← IO.FS.realPath (System.FilePath.mk '+__import__('json').dumps(expected)+')\n'
 text+='  unless resolved == expected do throwError "Actual own olean resolution failed: '+name+'"\n'
 text+='  IO.println (Json.mkObj [("kind",Json.str "independent_actual_own_findOLean"),("module",Json.str "'+name+'"),("chosen",Json.str chosen.toString),("realPath",Json.str resolved.toString),("expected",Json.str expected.toString),("actual_expected_own_path_equal",toJson true)]).compress\n'
row=save('OutputsIndependentResolutionV1',text)
p.dump(p.OUT/'resolution-preparation.json',dict(modules=modules,source=row,actual_source_count=21,actual_control_count=4,independent_PASS_claimed=False))
print('25 own module path checks SOURCE prepared; no Lean call yet.')
