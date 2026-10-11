import inspect_prepare as p
from prepare_controls import save
old=p.load(p.OUT/'resolution-preparation.json')
text=(p.PROJECT/old['source']['project_relative']).read_text(encoding='utf-8')
name='OutputsIndependentGeneratedClosureV1'
expected=str((p.PROJECT/'b/lib/lean'/ (name+'.olean')).resolve())
text+='  let chosen ← findOLean `'+name+'\n'
text+='  let resolved ← IO.FS.realPath chosen\n'
text+='  let expected ← IO.FS.realPath (System.FilePath.mk '+__import__('json').dumps(expected)+')\n'
text+='  unless resolved == expected do throwError "Actual own olean resolution failed: '+name+'"\n'
text+='  IO.println (Json.mkObj [("kind",Json.str "independent_actual_own_findOLean"),("module",Json.str "'+name+'"),("chosen",Json.str chosen.toString),("realPath",Json.str resolved.toString),("expected",Json.str expected.toString),("actual_expected_own_path_equal",toJson true)]).compress\n'
row=save('OutputsIndependentResolutionV2',text)
p.dump(p.OUT/'resolution-preparation-v2.json',dict(modules=old['modules']+[name],source=row,actual_source_count=21,actual_control_count=5,unattempted_resolver_V1_preserved=old['source'],independent_PASS_claimed=False))
print('Own resolver V2 covers26 actual own compiled modules.')
