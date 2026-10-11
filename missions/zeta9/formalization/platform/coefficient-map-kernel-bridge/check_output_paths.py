"""Offline guard for every planned compiler/output path and a 64-char temp suffix."""
from pathlib import Path
import hashlib,json,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2]
plan=json.loads((OUT/'preparation-state.json').read_text(encoding='utf-8-sig'))
PROJECT=(TASK/plan['source_project_task_relative']).resolve();BUILD=(TASK/plan['fresh_build_task_relative']).resolve()
assert PROJECT.is_relative_to(OUT.resolve()) and BUILD.is_relative_to((TASK/'.rt').resolve())
assert str(BUILD).count('..')==0
kernel=OUT.name=='coefficient-map-kernel-bridge'
module='CoefficientMapKernelBridge' if kernel else 'CoefficientMapTelescoper'
names=[t['name'].split('.')[-1] for t in plan['selected_actual_endpoints']] if kernel else plan['selected_actual_endpoints']
controls=plan['native_controls'] if kernel else plan['fixed_control_sources']
pure='Def_ZetaNine_HarmonicStability'
defs=['Def_ZetaNine_'+n for n in list(plan['sources_sha256']) if n!=module]+[pure]
rows=[]
def compiler_paths(m):
 rel=Path(*m.split('.'))
 paths=[BUILD/'lib/lean'/rel.with_suffix(e) for e in ['.olean','.olean.server','.olean.private','.ilean','.trace']]
 paths +=[BUILD/'ir'/rel.with_suffix(e) for e in ['.c','.c.o','.setup.json']]
 return [dict(absolute_path=str(p),kind='compiler_artifact',temporary_suffix_budget=64) for p in paths]
def execution(label,modules=(),extra=()):
 paths=[dict(absolute_path=str(OUT/(label+s)),kind='captured_output',temporary_suffix_budget=64) for s in ['.log','-exit.txt']]
 for m in modules:paths.extend(compiler_paths(m))
 for p in extra:paths.append(dict(absolute_path=str(p),kind='oracle_snapshot',temporary_suffix_budget=64))
 rows.append({'label':label,'outputs':paths})
execution('toolchain')
execution('build-native',['missions.zeta9.formalization.'+n for n in plan['sources_sha256']]+['Definitions.'+pure])
for c in controls:execution('native-control-'+c['module'],[c['module']])
execution('stage1-extract',extra=[OUT/'decl_graph.jsonl'])
for n in list(plan['sources_sha256'])+[pure]:
 snapshot='oracle-input.lean' if n.endswith('PartialFractions') else n+'-oracle-input.lean'
 facts='sketch_info.jsonl' if n.endswith('PartialFractions') else n+'-sketch_info.jsonl'
 execution('stage2-'+n,extra=[OUT/snapshot,OUT/facts,OUT/('stage2-'+n+'-stderr.log')])
execution('stage2-header',extra=[OUT/'header_info.jsonl',OUT/'stage2-header-stderr.log'])
for d in defs:execution('build-'+d.split('Def_ZetaNine_')[1],['Definitions.'+d])
execution('build-definition',['Definitions.Def_ZetaNine_'+module])
for i,n in enumerate(names):
 for kind,prefix in [('solution','Solutions.Sol_'),('reference','Theorems.Thm_')]:
  execution(f'build-{i}-{kind}',[prefix+'ZetaNine_'+module+'_'+n])
for label in ['types_original','types_definition']+[f'types_{i}_{k}' for i in range(3) for k in ['solution','reference']]+[f'helpers_{i}' for i in range(3)]:
 execution(label)
main_count=len(rows)
execution('aggregate-native-alias',['NativeValueComparisonDefinition'])
execution('aggregate-native-value-details')
execution('aggregate-staged-alias',['StagedValueComparisonDefinition'])
execution('aggregate-staged-value-details')
if kernel:
 execution('kernel-native-alias',['NativeKernelValueComparisonDefinition'])
 execution('kernel-native-value-details')
 execution('kernel-staged-alias',['StagedKernelValueComparisonDefinition'])
 execution('kernel-staged-value-details')
for label in ['stage-native-author-audit','stage-independent-boundary-audit']:execution(label)
assert (main_count,len(rows))==((47,57) if kernel else (43,49))
allpaths=[]
for r in rows:
 for p in r['outputs']:
  p['characters']=len(p['absolute_path']);p['with_temporary_suffix']=p['characters']+p['temporary_suffix_budget']
  p['below_260']=p['with_temporary_suffix']<=259
  allpaths.append(p)
# Lake's configuration cache stays inside the source project, not the compiler cache.
config_paths=[PROJECT/'.lake/lakefile.olean',PROJECT/'.lake/config/00000000000000000000/lakefile.olean']
for p in config_paths:
 n=len(str(p));allpaths.append({'absolute_path':str(p),'kind':'Lake_configuration_cache','temporary_suffix_budget':64,'characters':n,'with_temporary_suffix':n+64,'below_260':n+64<=259})
source_inputs=[PROJECT/'missions/zeta9/formalization'/(n+'.lean') for n in plan['sources_sha256']]
source_inputs +=[PROJECT/'Definitions'/(d+'.lean') for d in defs+['Def_ZetaNine_'+module]]
source_inputs +=[PROJECT/k/(prefix+'ZetaNine_'+module+'_'+n+'.lean') for n in names for k,prefix in [('Solutions','Sol_'),('Theorems','Thm_')]]
source_rows=[{'absolute_path':str(p),'characters':len(str(p)),'below_260':len(str(p))<=259} for p in source_inputs]
cache_files=list(BUILD.rglob('*')) if BUILD.exists() else []
safe=all(p['below_260'] for p in allpaths) and all(p['below_260'] for p in source_rows)
longest=max(allpaths,key=lambda p:p['with_temporary_suffix'])
report={'source_project_task_relative':PROJECT.relative_to(TASK).as_posix(),'fresh_build_task_relative':BUILD.relative_to(TASK).as_posix(),
 'compiler_cache_external_to_source_project':True,'compiler_cache_inside_current_task':True,
 'canonical_module_and_file_names_preserved':True,'proof_or_data_source_bytes_changed_by_path_shortening':False,
 'temporary_suffix_budget':64,'Windows_limit_including_NUL':260,'largest_allowed_without_NUL':259,
 'planned_main_execution_count':main_count,'planned_total_execution_count':len(rows),'execution_output_paths':rows,
 'Lake_configuration_cache_paths':allpaths[-len(config_paths):],'source_inputs':source_rows,
 'longest_guarded_output_path':longest,'cache_absent_or_empty_before_first_Lean':not cache_files,
 'existing_compiler_cache_files':len(cache_files),'all_absolute_output_paths_with_64_chars_below_260':safe,
 'proof_build_objects_copied_or_reused':False,'Lean_executed':False,'mathematical_PASS_claimed':False}
(OUT/'output-path-preflight.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
assert safe,'Windows output path or temporary suffix budget exceeded'
assert not cache_files,'Fresh compiler/cache path unexpectedly populated before first Lean'
print(json.dumps({'all_paths_safe':safe,'total_planned_executions':len(rows),'maximum_output_characters':longest['characters'],'maximum_with_64_characters':longest['with_temporary_suffix'],'source_project':str(PROJECT),'fresh_build_cache':str(BUILD),'Lean_executed':False},ensure_ascii=False))
