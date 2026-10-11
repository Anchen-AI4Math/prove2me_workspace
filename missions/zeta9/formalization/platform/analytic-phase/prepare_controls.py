from pathlib import Path
import importlib.util,json,re,sys
import inspect_prepare as p
# Pure recording functions only, no mathematics/object reuse from former package.
origin=p.TASK/'verification/formalization-coefficient-map-parameter-summation-independent-2026-10-07/prepare_controls.py'
spec=importlib.util.spec_from_file_location('generic_param_controls_source',origin);template=importlib.util.module_from_spec(spec);spec.loader.exec_module(template)
META=template.META.replace('import ParameterSummationIndependentAssertionsV1\n','import PhasePlatformAssertions\n').replace('import IndependentExprDagV3\n','import PhasePlatformExprDagV1\n')
GENERATED=template.GENERATED
prep=p.load(p.OUT/'source-preparation.json');defs=prep['native_definitions'];thms=prep['native_theorems']
contract=p.TASK/'.rt/aph1/APBoundary.lean'
body=contract.read_text(encoding='utf-8').split('namespace APBoundary\n',1)[1].split('end APBoundary',1)[0]
boundaries=re.findall(r'^theorem\s+(\w+)',body,re.M);assert len(boundaries)==15
controls=[]
for context in prep['contexts']:
 tag=context['tag']
 if tag not in ['definition','right','certified','global']:continue
 ctx=p.PROJECT/tag;isproof=tag!='definition'
 imports='import Definitions.Def_ZetaNine_AnalyticPhase\nimport Native.AnalyticPhaseUpperBound\n'
 if isproof:imports+='import '+next(x['module'] for x in context['math_sources'] if x['label']=='complete-solution')+'\n'
 assertions=imports+'set_option autoImplicit false\nset_option maxHeartbeats 8000000\nset_option maxRecDepth 20000\nnoncomputable section\nopen Set\nopen ZetaNine.AnalyticPhase\nnamespace PhasePlatformWhole\n'
 for row in defs:assertions+='theorem whole_'+row['name']+' : ZetaNine.AnalyticPhase.'+row['name']+' = PhasePlatformNativeOracle.'+row['name']+' := by rfl\n'
 assertions+='end PhasePlatformWhole\n'
 if isproof:assertions+='namespace PhasePlatformBoundary\n'+body+'end PhasePlatformBoundary\n'
 p.write(ctx/'PhasePlatformAssertions.lean',assertions)
 semantic=META+'run_meta do\n'
 if isproof:
  for row in thms:
   a='ZetaNine.AnalyticPhase.'+row['name'];e='PhasePlatformNativeOracle.'+row['name']
   semantic+='  full `'+a+' "actual_original_forall"\n  full `'+e+' "oracle_original_forall"\n  wholeType `'+a+' `'+e+'\n'
  target=['phase_strictAntiOn_right','phase_global_lt_certified','phase_global_upper_bound'][['right','certified','global'].index(tag)]
  semantic+='  full `solution "actual_complete_solution"\n  wholeType `solution `ZetaNine.AnalyticPhase.'+target+'\n'
 for row in defs:
  a='ZetaNine.AnalyticPhase.'+row['name'];e='PhasePlatformNativeOracle.'+row['name']
  semantic+='  full `'+a+' "actual_full_definition"\n  full `'+e+' "oracle_full_definition"\n  definitionKernel `'+a+' `'+e+'\n  full `PhasePlatformWhole.whole_'+row['name']+' "actual_whole_function_rfl"\n'
 if isproof:
  for name in boundaries:semantic+='  full `PhasePlatformBoundary.'+name+' "actual_typed_boundary"\n'
 modules=['Definitions.Def_ZetaNine_AnalyticPhase','Native.AnalyticPhase','Native.AnalyticPhaseUpperBound','PhasePlatformAssertions']
 if isproof:modules.append(next(x['module'] for x in context['math_sources'] if x['label']=='complete-solution'))
 semantic=semantic.replace('run_meta do\n',GENERATED+'run_meta do\n',1)
 semantic+='  completeActualModuleInventory ['+', '.join('`'+x for x in modules)+']\n'
 p.write(ctx/'PhasePlatformSemantic.lean',semantic)
 resolver='import PhasePlatformSemantic\nimport PhasePlatformExprDagValidationV1\nimport Lean\nopen Lean Meta\nset_option maxHeartbeats 8000000\nrun_meta do\n'
 # Inspect every actual imported module, not guessed paths.
 resolver+='  let env ← getEnv\n  for name in env.header.moduleNames do\n    let file ← findOLean name\n    let real ← IO.FS.realPath file\n    IO.println (Json.mkObj [("kind",Json.str "actual_import_origin"),("module",Json.str name.toString),("chosen",Json.str file.toString),("realPath",Json.str real.toString)]).compress\n'
 own=[x['module'] for x in context['math_sources']]+['PhasePlatformAssertions','PhasePlatformSemantic']
 for module in own:
  expected=str((ctx/'b/lib/lean'/(module.replace('.','/')+'.olean')).resolve())
  resolver+='  let file ← findOLean `'+module+'\n  let real ← IO.FS.realPath file\n  let expected ← IO.FS.realPath (System.FilePath.mk '+json.dumps(expected)+')\n  unless real == expected do throwError "Own actual proof object mismatch: '+module+'"\n  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "'+module+'"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress\n'
 p.write(ctx/'PhasePlatformResolver.lean',resolver)
 rows=[dict(label='control-'+x,module='PhasePlatform'+x.title(),path='PhasePlatform'+x.title()+'.lean',binding=p.bind(ctx/('PhasePlatform'+x.title()+'.lean'))) for x in ['assertions','semantic','resolver']]
 controls.append(dict(tag=tag,proof_context=isproof,rows=rows,own_mathematical_modules=modules,own_resolver_expected=own,exact_forall_count=34 if isproof else 0,whole_definition_count=7,whole_function_rfl=7,typed_boundaries=15 if isproof else 0))
p.dump(p.OUT/'control-preparation.json',dict(contexts=controls,boundary_names=boundaries,native_boundary_SOURCE_reuse=dict(binding=p.bind(contract),only_verified_mathematical_Source_body_copied=True,namespace_changed_to='PhasePlatformBoundary',native_Meta_code_not_reused=True,foreign_boundary_objects_borrowed=False),generic_Meta_recorder_SOURCE_reuse=p.bind(origin),original_headers34_preserved=True,raw_alias_namespace_differences_must_be_retained=True,platform_AUTHOR_PASS_claimed=False))
print('4 own-context controls prepared: each7whole definitions/rfl; each3proof contexts34allforalls and15typedbounds plus full helpers and actual import origins.')
