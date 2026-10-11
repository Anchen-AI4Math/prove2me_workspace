import json,sys
import inspect_prepare as p
from prepare_controls import save
prep=p.load(p.OUT/'source-preparation.json');plan=p.load(p.OUT/'control-preparation.json')
modules=[x['module'] for x in prep['native_sources']]+[x['module'] for x in prep['serializer_sources']]+[plan[k]['module'] for k in ['assertions','semantic','generated']]
assert len(modules)==27 and len(set(modules))==27
text='import ParameterSummationIndependentGeneratedV1\nimport ParameterSummationIndependentSemanticV1\nimport Lean\nopen Lean Meta\nset_option maxHeartbeats 8000000\nrun_meta do\n'
for name in modules:
 expected=str((p.PROJECT/'b/lib/lean'/(name.replace('.','/')+'.olean')).resolve())
 text+='  let chosen ← findOLean `'+name+'\n'
 text+='  let resolved ← IO.FS.realPath chosen\n'
 text+='  let expected ← IO.FS.realPath (System.FilePath.mk '+json.dumps(expected)+')\n'
 text+='  unless resolved == expected do throwError "Actual own source object lookup mismatch: '+name+'"\n'
 text+='  IO.println (Json.mkObj [("kind",Json.str "independent_actual_own_findOLean"),("module",Json.str "'+name+'"),("chosen",Json.str chosen.toString),("realPath",Json.str resolved.toString),("expected",Json.str expected.toString),("actual_expected_own_path_equal",toJson true)]).compress\n'
row=save('ParameterSummationIndependentResolutionV1',text)
p.dump(p.OUT/'resolution-preparation.json',dict(modules=modules,source=row,actual_native_modules=22,control_modules=5,own_actual_findOLean_checks=27,independent_PASS_claimed=False))
print('27 own module path resolutions prepared; all target outputs must first exist from own actual compiler calls.')
