"""Offline independent Telescoper enrollment and Windows path guard. Runs no Lean."""
from pathlib import Path
import json,hashlib,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;BATCH=OUT.parent;TASK=OUT.parents[3];ROOT=TASK.parents[1]
PROJECT=OUT/'p';BUILD=TASK/'.rt/ti1/b';N=BUILD/'n/lib/lean';P=BUILD/'p/lib/lean'
MATH=TASK/'verification/formalization-coefficient-map-telescoper-independent-2026-10-04/independent-review.json'
MATH_SHA='cac46e0ea0674bcd4b2dca543326ab2d9bdd3cd8a409cba8988bfea0130a556a'
AGG=TASK/'formalization/platform/coefficient-map-aggregate';AGGI=AGG/'independent'
AGG_REVIEW_SHA='ff464d565f54cdcb8efd6445864fb278ed8ed0525c2b0fbab6fe158c96d5c24d'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def dump(p,d):p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
def write(p,b):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b if isinstance(b,bytes) else b.encode())
assert sha(MATH)==MATH_SHA
math=load(MATH);assert math['verdict']=='PASS' and len(math['checks'])==16 and len(math['stable_files'])==150
for r in math['stable_files']:
 f=ROOT/r['root_relative'];assert sha(f)==r['sha256'] and f.stat().st_size==r['bytes']
assert sha(AGGI/'independent-integration-review.json')==AGG_REVIEW_SHA
for r in load(AGGI/'independent-integration-review.json')['stable_files']:
 f=ROOT/r['root_relative'];assert sha(f)==r['sha256'] and f.stat().st_size==r['bytes']
state=load(BATCH/'preparation-state.json');sources=state['sources_sha256']
assert len(sources)==9 and sources['CoefficientMapTelescoper']=='8792e8ba5c6abcbdbe83b0aa4ffa1ab716fd05fac10da7275b86ab2f780fd121'
assert not BUILD.exists(), 'Independent compiler cache must not exist before first actual run'
assert PROJECT.resolve().is_relative_to(OUT.resolve()) and BUILD.resolve().is_relative_to((TASK/'.rt').resolve())
bindings=[]
def enroll(original,destination,kind,expected=None):
 if expected:assert sha(original)==expected
 write(destination,original.read_bytes());assert destination.read_bytes()==original.read_bytes()
 bindings.append({'kind':kind,'original_root_relative':original.relative_to(ROOT).as_posix(),'project_relative':destination.relative_to(PROJECT).as_posix(),'bytes':destination.stat().st_size,'sha256':sha(destination)})
for m,h in sources.items():enroll(TASK/'formalization'/(m+'.lean'),PROJECT/'missions/zeta9/formalization'/(m+'.lean'),'actual_native_source',h)
defs=load(AGG/'root-copy-plan.json')['required_existing_Definitions']+[{'root_relative':'Definitions/Def_ZetaNine_CoefficientMapAggregate.lean','task_relative':'formalization/platform/coefficient-map-aggregate/staged/Definitions/Def_ZetaNine_CoefficientMapAggregate.lean','sha256':'ef491f5136c5a98d976ff9faf73df3b65393bb2caf50772dccafd213c8302079'}]
assert len(defs)==9
for r in defs:
 original=TASK/r['task_relative'];assert original.read_bytes()==(ROOT/r['root_relative']).read_bytes();enroll(original,PROJECT/r['root_relative'],'pure_Def_dependency',r['sha256'])
controls=state['fixed_control_sources'];assert len(controls)==2
for r in controls:enroll(TASK/r['task_relative'],PROJECT/(r['module']+'.lean'),'actual_native_control',r['sha256'])
alias=AGG/'native-value-comparison-definition.lean';assert sha(alias)=='4187ed313d634e9a85f284f67835d63f4543487eee01e359dbc3f68adeda0fc8'
enroll(alias,PROJECT/'NativeValueComparisonDefinition.lean','source_only_frozen_Aggregate_native_alias')
original=b'import missions.zeta9.formalization.CoefficientMapAggregate';staged=b'import Definitions.Def_ZetaNine_CoefficientMapAggregate'
b=alias.read_bytes();assert b.count(original)==1 and b.splitlines()[0]==original
write(PROJECT/'StagedValueComparisonDefinition.lean',b.replace(original,staged))
native_audit=(AGGI/'independent-native-value-comparison.lean').read_bytes();assert native_audit.splitlines()[0]==b'import NativeValueComparisonDefinition'
write(OUT/'agg-native-values.lean',native_audit)
write(OUT/'agg-staged-values.lean',native_audit.replace(b'import NativeValueComparisonDefinition',b'import StagedValueComparisonDefinition',1))
# A Lake config is supplied as a readable specification. The future driver will use
# ROOT's pinned lake env and our explicit, first-position N/P cache paths.
write(PROJECT/'lakefile.lean','import Lake\nopen Lake DSL\npackage zeta9TelescoperIndependent where\n  buildDir := "'+BUILD.as_posix()+'"\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"\nlean_lib Definitions\nlean_lib Solutions\nlean_lib Theorems\n')
for n in ['lake-manifest.json','lean-toolchain']:write(PROJECT/n,(ROOT/n).read_bytes())
targets=state['selected_actual_endpoints'];assert targets==['actual_weightedR_is_difference','telescoper_actual_rational_representation','actual_polynomial_quotient_degree_bound']
compiler_modules_n=['Definitions.Def_ZetaNine_HarmonicStability']+['missions.zeta9.formalization.'+m for m in sources]+[r['module'] for r in controls]+['NativeValueComparisonDefinition']
compiler_modules_p=[r['root_relative'].removesuffix('.lean').replace('/','.') for r in defs]+['Definitions.Def_ZetaNine_CoefficientMapTelescoper']+[k+'.'+prefix+'ZetaNine_CoefficientMapTelescoper_'+n for n in targets for k,prefix in [('Solutions','Sol_'),('Theorems','Thm_')]]+['StagedValueComparisonDefinition']
paths=[]
def guard(p,kind,suffix=64):
 p=p.resolve();assert p.is_relative_to(TASK.resolve())
 paths.append({'absolute_path':str(p),'kind':kind,'characters':len(str(p)),'temporary_suffix_budget':suffix,'with_temporary_suffix':len(str(p))+suffix,'below_260':len(str(p))+suffix<=259})
for cache,modules in [(N,compiler_modules_n),(P,compiler_modules_p)]:
 for m in modules:
  rel=Path(*m.split('.'))
  for ext in ['.olean','.olean.server','.olean.private','.ilean','.trace']:guard(cache/rel.with_suffix(ext),'compiler_artifact')
  for ext in ['.c','.c.o','.setup.json']:guard(cache.parent.parent/'ir'/rel.with_suffix(ext),'possible_compiler_IR_artifact')
for name in ['s01','s30','x01','x14','a01','a26','cx0','cx6','bd-native','bd-stage','run-version']:
 for ext in ['.log','-exit.txt','.ps1']:guard(OUT/(name+ext),'short_capture_or_wrapper')
for p in [PROJECT/'.lake/lakefile.olean',PROJECT/'.lake/config/00000000000000000000/lakefile.olean']:guard(p,'Lake_config_cache')
for r in bindings:guard(PROJECT/r['project_relative'],'source_input',0)
for m in compiler_modules_p:
 if m.startswith(('Solutions.','Theorems.')):guard(PROJECT/Path(*m.split('.')).with_suffix('.lean'),'future_staged_source_input',0)
assert all(r['below_260'] for r in paths)
guarded=max(paths,key=lambda r:r['with_temporary_suffix'])
dump(OUT/'output-path-preflight.json',{'status':'OFFLINE_PREPARATION_ONLY','source_project_task_relative':PROJECT.relative_to(TASK).as_posix(),'fresh_cache_task_relative':BUILD.relative_to(TASK).as_posix(),'native_cache_task_relative':N.relative_to(TASK).as_posix(),'platform_cache_task_relative':P.relative_to(TASK).as_posix(),'native_and_platform_cache_separate':True,'cache_absent_before_first_Lean':not BUILD.exists(),'all_paths_with_64_char_suffix_below_260':True,'longest_guarded_output':guarded,'path_rows':paths,'Lean_executed':False,'mathematical_PASS_claimed':False})
dump(OUT/'preparation-enrollment.json',{'status':'PREFREEZE_PREPARATION_ONLY','native_math_review_sha256':MATH_SHA,'native_math_checks':16,'native_math_stable_bindings_rehashed':150,'Aggregate_independent_review_sha256':AGG_REVIEW_SHA,'Aggregate_independent_bindings_rehashed':771,'original_source_hashes':sources,'source_bindings':bindings,'pure_Def_dependencies':defs,'fixed_native_controls':controls,'targets':targets,'new_Defs':state['new_genuine_Definitions'],'aggregate_native_alias_sha256':sha(alias),'source_only_alias_replay':True,'only_staged_alias_change':'single import of canonical staged Aggregate Def','source_copies_byte_identical':True,'objects_copied_or_reused':False,'Lean_executed':False,'author_Telescoper_controls_not_frozen':True,'Root_Telescoper_not_verified':True,'future_fresh_Lean_requires_parent_lane':True,'independent_PASS_claimed':False,'root_scope_API_credentials_writes':False})
print(json.dumps({'preparation_only':True,'native_source_copies':9,'pure_Def_copies':9,'native_control_copies':2,'path_rows':len(paths),'longest_with_64_char_suffix':guarded['with_temporary_suffix'],'Lean_executed':False},ensure_ascii=False))
