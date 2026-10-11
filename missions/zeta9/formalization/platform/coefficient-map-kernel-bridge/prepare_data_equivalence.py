"""Fresh native/staged whole-value kernel replay of frozen Aggregate source."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];PROJECT=OUT/'p';BUILD=TASK/'.rt/k1/b'
AGG=TASK/'formalization/platform/coefficient-map-aggregate'
DEF_SHA='ef491f5136c5a98d976ff9faf73df3b65393bb2caf50772dccafd213c8302079'
DETAILS_SHA='8593fe0fb35a0eacc4195a0693eab2c9118916e51e548e51bf7d47b8bcb585c6'
NS='ZetaNine.CoefficientMapAggregate'
NAMES=['aggregate','coordinatePolynomial','polynomialCoordinates','aggregateLinearMap','coordinateLinearMap','quarticAggregateLinearMap']
PROOFS=['native_value_'+n+'_eq' for n in NAMES]+['native_data_'+n for n in NAMES[3:]]
STD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def dump(p,d):p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def write(p,data):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
ap=argparse.ArgumentParser()
ap.add_argument('--alias-source-task-relative',required=True);ap.add_argument('--alias-source-sha256',required=True)
ap.add_argument('--alias-namespace',required=True);ap.add_argument('--aggregate-author-audit-sha256',required=True)
ap.add_argument('--aggregate-SHA256SUMS-sha256',required=True);ap.add_argument('--prepare-only',action='store_true')
opts=ap.parse_args()
assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*',opts.alias_namespace)
assert opts.alias_namespace=='ZetaNine.CoefficientMapAggregateValueComparison'
alias=(TASK/opts.alias_source_task_relative).resolve()
details=AGG/'native-value-details.lean'
assert alias.is_relative_to(AGG.resolve()) and alias.suffix=='.lean' and sha(alias)==opts.alias_source_sha256
assert sha(details)==DETAILS_SHA
assert sha(AGG/'staged/Definitions/Def_ZetaNine_CoefficientMapAggregate.lean')==DEF_SHA==sha(PROJECT/'Definitions/Def_ZetaNine_CoefficientMapAggregate.lean')
assert sha(AGG/'author-audit.json')==opts.aggregate_author_audit_sha256
assert sha(AGG/'SHA256SUMS.txt')==opts.aggregate_SHA256SUMS_sha256
parent=load(AGG/'author-audit.json');assert parent['verdict']=='PASS' and all(c['pass'] for c in parent['checks'])
parent_bindings=[]
for line in (AGG/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
 h,rel=line.split('  ',1);assert sha(AGG/rel)==h
 parent_bindings.append({'task_relative':(AGG/rel).relative_to(TASK).as_posix(),'sha256':h})
for p in [alias,details]:
 assert any(r['task_relative']==p.relative_to(TASK).as_posix() and r['sha256']==sha(p) for r in parent_bindings)

# Replay true native imports and a staged program differing by exactly one import.
# Neither process imports both environments or borrows any previous mission object.
native_import=b'import missions.zeta9.formalization.CoefficientMapAggregate'
staged_import=b'import Definitions.Def_ZetaNine_CoefficientMapAggregate'
native_alias=alias.read_bytes();assert native_alias.count(native_import)==1
assert native_alias.splitlines()[0]==native_import
staged_alias=native_alias.replace(native_import,staged_import)
assert not any(l.startswith((b'import missions.',b'import Solutions.',b'import Theorems.')) for l in staged_alias.splitlines())
native_details=details.read_bytes();detail_import=b'import NativeValueComparisonDefinition'
assert native_details.count(detail_import)==1 and native_details.splitlines()[0]==detail_import
staged_details=native_details.replace(detail_import,b'import StagedValueComparisonDefinition')
variants=[('NativeValueComparisonDefinition.lean',native_alias),('StagedValueComparisonDefinition.lean',staged_alias),
 ('aggregate-native-value-details.lean',native_details),('aggregate-staged-value-details.lean',staged_details)]
for name,data in variants:
 write(OUT/'dependencies'/name,data);write(PROJECT/name,data)
program_bindings=[{'file':name,'sha256':sha(PROJECT/name),'dependency_snapshot':(OUT/'dependencies'/name).relative_to(TASK).as_posix()} for name,_ in variants]
provenance={'actual_parent_definition_sha256':DEF_SHA,'alias_native_source':alias.relative_to(TASK).as_posix(),
 'alias_source_sha256':opts.alias_source_sha256,'alias_namespace':opts.alias_namespace,
 'native_full_value_details_source':details.relative_to(TASK).as_posix(),'native_full_value_details_source_sha256':DETAILS_SHA,
 'alias_and_original_definition_names':NAMES,'closed_kernel_data_equality_proofs':PROOFS,
 'aggregate_author_audit_sha256':opts.aggregate_author_audit_sha256,
 'aggregate_SHA256SUMS_sha256':opts.aggregate_SHA256SUMS_sha256,'parent_frozen_bindings':parent_bindings,
 'fresh_program_bindings':program_bindings,
 'alias_single_import_substitution':{'original':native_import.decode(),'staged':staged_import.decode(),'only_change':True},
 'details_single_import_substitution':{'original':detail_import.decode(),'staged':'import StagedValueComparisonDefinition','only_change':True},
 'pretty_value_exception_names':[NS+'.'+n for n in NAMES[3:]],
 'native_direct_full_value_kernel_comparisons':6,'staged_direct_full_value_kernel_comparisons':6,
 'closed_rfl_and_data_equalities_per_environment':9,'seven_context_map_checks_are_canonical_propagation':True,
 'actual_native_alias_kernel_definitional_equality_not_F_kernel_triviality':True,
 'extra_hypotheses':[],'borrowed_objects':False,'root_scope_API_credential_writes':False}
dump(OUT/'aggregate-data-equivalence-provenance.json',provenance)
if opts.prepare_only:
 print('Frozen Aggregate native/staged full-value replay prepared; no Lean executed.');sys.exit(0)
env=os.environ.copy();env.pop('LEAN_PATH',None)
objdir=BUILD/'lib/lean';objdir.mkdir(parents=True,exist_ok=True)
runs=[]
steps=[('aggregate-native-alias',['lake','env','lean','-o',(objdir/'NativeValueComparisonDefinition.olean').as_posix(),'NativeValueComparisonDefinition.lean']),
 ('aggregate-native-value-details',['lake','env','lean','aggregate-native-value-details.lean']),
 ('aggregate-staged-alias',['lake','env','lean','-o',(objdir/'StagedValueComparisonDefinition.olean').as_posix(),'StagedValueComparisonDefinition.lean']),
 ('aggregate-staged-value-details',['lake','env','lean','aggregate-staged-value-details.lean'])]
for label,args in steps:
 p=subprocess.run(args,cwd=PROJECT,env=env,capture_output=True)
 log=OUT/(label+'.log');log.write_bytes(p.stdout+p.stderr)
 (OUT/(label+'-exit.txt')).write_text(str(p.returncode)+'\n',encoding='utf-8')
 runs.append({'label':label,'command':args,'working_directory':str(PROJECT),'exit_code':p.returncode,'log_sha256':sha(log)})
 dump(OUT/'aggregate-data-equivalence-receipt.json',{'runs':runs,'complete':False,'borrowed_objects':False})
 print(label+': exit '+str(p.returncode),flush=True)
 if p.returncode:print((p.stdout+p.stderr).decode('utf-8-sig'),flush=True)
 assert p.returncode==0
environments=[]
for context in ['native','staged']:
 rs=[json.loads(l) for l in (OUT/('aggregate-'+context+'-value-details.log')).read_text(encoding='utf-8-sig').splitlines() if l.startswith('{')]
 assert len(rs)==15 and all(set(r['axioms'])<=STD for r in rs)
 assert [r['declaration'] for r in rs[:6]]==[NS+'.'+n for n in NAMES]
 assert all(r['kind']=='kernel_definition_value' and r['alias_declaration']==opts.alias_namespace+'.'+n and r['type_kernel_equal'] and r['full_value_kernel_equal'] and r['pp_proofs_enabled'] and r['original_expression_repr'] and r['comparison_expression_repr'] for n,r in zip(NAMES,rs[:6]))
 assert [r['declaration'] for r in rs[6:]]==PROOFS
 assert all(r['kind']=='rfl_or_data_equality' for r in rs[6:])
 objectfile=objdir/('NativeValueComparisonDefinition.olean' if context=='native' else 'StagedValueComparisonDefinition.olean')
 environments.append({'context':context,'records':rs,'actual_whole_value_kernel_comparisons':6,'actual_closed_rfl_and_data_equalities':9,'all_standard_axioms':True,'object_task_relative':objectfile.relative_to(TASK).as_posix(),'object_sha256':sha(objectfile)})
dump(OUT/'aggregate-data-equivalence-report.json',{'runs':runs,'environments':environments,
 'exact_shared_alias_program_except_single_import':True,'exact_shared_full_details_except_single_import':True,
 'native_direct_full_value_comparisons':6,'staged_direct_full_value_comparisons':6,
 'closed_rfl_and_data_equalities':18,'all_standard_axioms':True,'no_extra_hypotheses':True})
dump(OUT/'aggregate-data-equivalence-receipt.json',{'runs':runs,'complete':True,'borrowed_objects':False})
