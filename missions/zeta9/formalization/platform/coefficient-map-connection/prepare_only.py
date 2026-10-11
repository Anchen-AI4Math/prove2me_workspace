"""Offline Connection platform preparation. Never invokes Lean, Lake or an API."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/ca1';NATIVE='missions.zeta9.formalization.CoefficientMapConnection'
NS='ZetaNine.CoefficientMapConnection';ALIAS_NS=NS+'ValueComparison'
SOURCE_SHA='098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8'
REV='0df444a360eaa60ab8c11dca51a86af692955474'
AUTHOR=TASK/'verification/formalization-coefficient-map-connection-2026-10-04'
INDEPENDENT=TASK/'verification/formalization-coefficient-map-connection-independent-2026-10-04/independent-review.json'
INDEPENDENT_SHA='92940f9b02161210e55af39c625e0cd233eaf7a5bf9d5c1aa2238f0506e28d82'
FIXED={'compile-receipt.json':'d6dec3cc709eba34d307ed85d521906e13129a0453a22cb32ebf6d77b011c9f0',
 'type-audit-receipt.json':'6a134c567b23f3319eeb5f3bdf28e3fa099ea715cf5894d99accd8e12329be8a',
 'author-audit.json':'306fb4fc9b838c50c2928317994107f20605e4f8c9acd610d22d962492b75972',
 'source-manifest.json':'dec02f5213b8e92cd2575225b55ade114aff7af6561bbd2b296bf2ebfe3a9190',
 'SHA256SUMS.txt':'6fc61bb0625ad243a09df436c919955be60686d2ea9dc2ba4288f15448ba7a99'}
TARGETS=['connection_homogeneous_kernel_zero','connectionLinearMap_bijective','connection_five_systems_unique']
ARGS=['n hn P q hqdeg heq','n hn','n hn r']
DEFS=['connectionU','connectionV','connectionD','connectionH','connectionReflection',
 'coefficientPolynomial','inputP','inputQ','connectionOperator','connectionLinearMap','connectionZ','connectionTarget']
HELPERS=['coefficientPolynomial_add','coefficientPolynomial_smul','connectionOperator_add','connectionOperator_smul']
IMPORTS=['Mathlib.Algebra.Polynomial.RingDivision','Mathlib.Algebra.Polynomial.Degree.Lemmas',
 'Mathlib.Algebra.Polynomial.BigOperators','Mathlib.LinearAlgebra.FiniteDimensional.Basic','Mathlib.Tactic']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
SOURCE=TASK/'formalization/CoefficientMapConnection.lean'
assert sha(SOURCE)==SOURCE_SHA
for n,h in FIXED.items():assert sha(AUTHOR/n)==h
manifest=json.loads((AUTHOR/'source-manifest.json').read_text(encoding='utf-8'))
assert len(manifest['files'])==53
for x in manifest['files']:assert sha(ROOT/x['root_relative'])==x['sha256']
assert sha(INDEPENDENT)==INDEPENDENT_SHA
independent=json.loads(INDEPENDENT.read_text(encoding='utf-8'))
assert independent['verdict']=='PASS' and independent['source_sha256']==SOURCE_SHA
assert len(independent['checks'])==28 and all(x['pass'] for x in independent['checks'])
NATIVE_INDEPENDENT={'task_relative':INDEPENDENT.relative_to(TASK).as_posix(),'sha256':INDEPENDENT_SHA,
 'verdict':'PASS','checks':28,'scope':'native Connection mathematics only, not a platform transplant verdict'}
native=json.loads((AUTHOR/'type-audit.json').read_text(encoding='utf-8'))
assert len(native['records'])==39
assert [r['declaration'].rsplit('.',1)[1] for r in native['records'] if r['kind']=='def']==DEFS
assert sum(r['kind']=='theorem' for r in native['records'])==27
assert all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in native['records'])
assert not (PROJECT/'b').exists() and not (PROJECT/'.lake/build').exists(), 'Fresh-empty cache required.'
definition='Definitions/Def_ZetaNine_CoefficientMapConnection.lean'
targets=[{'theorem_name':NS+'.'+n,'wrapper_arguments':a,
          'local_solution':'Solutions/Sol_ZetaNine_CoefficientMapConnection_'+n+'.lean',
          'local_reference':'Theorems/Thm_ZetaNine_CoefficientMapConnection_'+n+'.lean'} for n,a in zip(TARGETS,ARGS)]
modules=([NATIVE,definition.removesuffix('.lean').replace('/','.')]+
 [t[k].removesuffix('.lean').replace('/','.') for t in targets for k in ['local_solution','local_reference']])
paths=[str(PROJECT/'b/lib/lean'/(m.replace('.','/')+'.olean')) for m in modules]
path_checks=[{'absolute_object_path':p,'characters':len(p),'temporary_suffix_margin':64,'path_plus_64':len(p)+64,'pass':len(p)+64<=259} for p in paths]
assert all(x['pass'] for x in path_checks)
write(PROJECT/'lakefile.lean',f'''import Lake
open Lake DSL
package zeta9ConnectionOfflineAuthor where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib Native where
  roots := #[`{NATIVE}]
  globs := #[.one `{NATIVE}]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
''')
for n in ['lean-toolchain','lake-manifest.json']:write(PROJECT/n,(ROOT/n).read_bytes())
write(PROJECT/(NATIVE.replace('.','/')+'.lean'),SOURCE.read_bytes())
(PROJECT/'.lake').mkdir(exist_ok=True)
if not (PROJECT/'.lake/packages').exists():
 r=subprocess.run(['cmd','/c','mklink','/J',str(PROJECT/'.lake/packages'),str(ROOT/'.lake/packages')],capture_output=True)
 write(OUT/'package-junction-preparation.log',r.stdout+r.stderr)
 assert r.returncode==0
KIT=TASK/'formalization/platform/coefficient-map-jet'
graph=(KIT/'extract_decl_graph.lean').read_text(encoding='utf-8-sig')
graph=graph.replace('import missions.zeta9.formalization.CoefficientMapJet','import '+NATIVE)
graph=graph.replace('missions/zeta9/formalization/platform/coefficient-map-jet/decl_graph.jsonl',
                    (OUT/'decl_graph.jsonl').as_posix())
parser=(KIT/'extract_sketch_info.lean').read_text(encoding='utf-8-sig')
old='missions/zeta9/formalization/platform/coefficient-map-jet/oracle-input.lean';assert parser.count(old)==1
for name,snapshot in [('source','CoefficientMapConnection-oracle-input.lean'),
                      ('native-author','native-author-oracle-input.lean'),('native-boundary','native-boundary-oracle-input.lean')]:
 code=parser.replace(old,(OUT/snapshot).as_posix())
 write(OUT/('parse-'+name+'.lean'),code);write(PROJECT/('parse-'+name+'.lean'),code)
for name,data in [('extract_decl_graph.lean',graph),('extract_header.lean',(KIT/'extract_header.lean').read_bytes())]:
 write(OUT/name,data);write(PROJECT/name,data)
for name in ['type-audit.lean','boundary-audit.lean']:write(OUT/('native-'+name), (AUTHOR/name).read_bytes())
dump(OUT/'target-plan.preparation.json',{'status':'PREPARATION_ONLY','source_sha256':SOURCE_SHA,
 'namespace':NS,'native_module':NATIVE,'definition_name':'ZetaNine_CoefficientMapConnection','local_definition':definition,
 'targets':targets,'expected_actual_definitions':DEFS,'expected_native_source_types':39,'expected_native_source_proofs':27,
 'expected_proof_records_per_Solution':28,'expected_Solution_proof_records':84,'required_existing_Definitions':[],
 'external_Theorems':[],'wrapper_signatures_pending_actual_parser':True,
 'no_original_mission_proof_import_in_staged':True,'no_regex_position_authority':True})
dump(OUT/'definition-closure.preparation.json',{'status':'PREPARATION_ONLY','actual_spans_pending':True,
 'proof_bearing_definition':'connectionLinearMap','constructor_fields':['map_add\x27','map_smul\x27'],
 'expected_actual_helper_callees':HELPERS,'local_have_closure_required':True,
 'embedding_policy':'Only actual resolved helper reference tokens are replaced. Original helper theorem prefix becomes local have; proof bodies come byte-for-byte from actual parser spans.',
 'no_new_global_helper_theorems':True,'no_Bijective_constructor_definition':True,'no_kernel_or_bijective_assumption':True,
 'native_alias_namespace':ALIAS_NS,'full_kernel_equality_required_for_all_twelve_Definitions':True,
 'comparison_policy':'12 direct native-alias full kernel comparisons plus twelve rfl and one actual data equality; seven staged contexts separately bound. PP with proofs enabled is diagnostic, not full-value equality evidence.'})
future=[['lake','env','lean','--version'],['lake','--no-cache','build',NATIVE],
 ['lake','env','lean','extract_decl_graph.lean'],
 ['lake','env','lean','--run','parse-source.lean',NATIVE.replace('.','/')+'.lean','ZetaNine'],
 ['lake','env','lean','--run','extract_header.lean',NATIVE.replace('.','/')+'.lean']]
dump(OUT/'execution-plan.preparation.json',{'status':'NOT_EXECUTED','working_directory':str(PROJECT),
 'first_future_commands':future,'remaining_future_phases':['actual graph/parser checks','actual constructor helper closures and type-remap oracle',
 '7 staged modules','12-definition native-alias full kernel comparison','12 types/values in 7 contexts',
 '3 original/Solution/reference exact target types','84 complete staged proof records standard3',
 'native39 author audit and native12 boundary replay through actual parser facts','staged39 source-type comparison and staged12 boundary types',
 'author gate and 7-file copyplan','independent platform review by a non-author','parent root install and supported scoped build'],
 'Lean_executed':False,'independent_native_review_pending':False,'independent_native_review':NATIVE_INDEPENDENT,'platform_review_pending':True})
copyfiles=[{'root_relative_destination':rel,'staged_task_relative':(OUT/'staged'/rel).relative_to(TASK).as_posix(),
 'sha256':None,'bytes':None,'pin_required_before_install':True}
 for rel in [definition]+[t[k] for t in targets for k in ['local_solution','local_reference']]]
dump(OUT/'root-copy-plan.preparation.json',{'status':'NOT_INSTALLABLE','source_sha256':SOURCE_SHA,'files':copyfiles,
 'required_existing_Definitions':[],'ready_to_install':False,'overwrite_allowed':False,
 'reason':'No staged bytes or author freeze until actual Lean graph/parser and native/staged audits succeed.'})
dump(OUT/'preparation-state.json',{'status':'PREPARATION_ONLY','source_sha256':SOURCE_SHA,
 'native_author_controls_verified':FIXED,'native_author_role_is_this_agent':True,
 'native_author_PASS_is_not_independent_or_platform_PASS':True,'independent_native_review_pending':False,'independent_native_review':NATIVE_INDEPENDENT,
 'Lean_Lake_executed':False,'native_or_stage_objects_borrowed':False,'only_Mathlib_package_cache_shared':True,
 'fresh_project':str(PROJECT),'build_cache_absent':True,'path_checks':path_checks,
 'API_root_scope_credential_writes':False,'no_regex_source_position_evidence':True})
print(json.dumps({'status':'PREPARATION_ONLY','Lean_executed':False,'source_sha256':SOURCE_SHA,
 'fresh_project':str(PROJECT),'max_object_path_characters':max(map(len,paths)),
 'max_object_path_plus_64':max(map(len,paths))+64,'expected_source_declarations':39,
 'expected_original_proofs':27,'expected_pure_Definitions':12,'targets':TARGETS},ensure_ascii=False,indent=2))
