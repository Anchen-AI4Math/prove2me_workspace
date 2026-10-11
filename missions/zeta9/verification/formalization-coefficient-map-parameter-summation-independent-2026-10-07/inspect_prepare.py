from pathlib import Path
import json,hashlib,re,sys,concurrent.futures
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parent.parent;PROJECT=TASK/'.rt/psi1'
AUTHOR=TASK/'verification/formalization-coefficient-map-parameter-summation-author-2026-10-07'
PREP=TASK/'verification/formalization-coefficient-map-parameter-summation-preparation-2026-10-07'
PREVIOUS=TASK/'verification/formalization-coefficient-map-formal-transport-outputs-independent-2026-10-07'
AUTHOR_SHA='aea3ede6a6f240450fe0ce1fb59aa7a1f8e93d21ff26bf1694e190407cc11d8d'
SOURCE_SHA='bf21501e51b31a9e9e754f8c7f22dcd734aa1435d5770838d2118bb40b662446'
def load(path):return json.loads(path.read_text(encoding='utf-8-sig'))
def sha(path):
 with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def resolve(r):return TASK/r['task_relative'] if r.get('task_relative') is not None else ROOT/r['root_relative']
def check(rows):
 for r in rows:
  rel=r.get('task_relative',r.get('root_relative'));assert rel and not Path(rel).is_absolute() and '..' not in Path(rel).parts
  path=resolve(r);assert path.stat().st_size==r['bytes'] and sha(path)==r['sha256'],str(path)
def bind(path):return dict(task_relative=path.resolve().relative_to(TASK.resolve()).as_posix(),bytes=path.stat().st_size,sha256=sha(path))
def dump(path,x):path.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def copy(origin,target):target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists();target.write_bytes(origin.read_bytes())
def main():
 sys.stdout.reconfigure(encoding='utf-8');assert not PROJECT.exists(),'psi1 must be fresh; never erase/reset prior objects'
 assert sha(AUTHOR/'author-audit.json')==AUTHOR_SHA
 author=load(AUTHOR/'author-audit.json');assert author['verdict']=='PASS' and len(author['stable_files'])==755 and all(x['passed'] for x in author['checks'])
 def check_one(row):
  p=resolve(row);return p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:assert all(pool.map(check_one,author['stable_files']))
 sources=load(PREP/'source-inputs.json')['sources'];assert len(sources)==22
 PROJECT.mkdir(parents=True);rows=[]
 for row in sources:
  origin=Path(row['origin_absolute']);assert origin.stat().st_size==row['bytes'] and sha(origin)==row['sha256']
  target=PROJECT/row['project_relative'];snapshot=OUT/'immutable-sources'/row['project_relative'];copy(origin,target);copy(origin,snapshot)
  rows.append(dict(module=row['module'],project_relative=row['project_relative'],origin=dict(absolute_path=str(origin),bytes=row['bytes'],sha256=row['sha256']),project_copy=bind(target),snapshot=bind(snapshot)))
 modules={x['module'] for x in rows}
 for row in rows:
  for line in re.findall(r'^import\s+([^\n]+)',(PROJECT/row['project_relative']).read_text(encoding='utf-8-sig'),re.M):
   for dep in line.split():assert not dep.startswith(('missions.','Definitions.')) or dep in modules
 for name in ['lakefile.toml','lean-toolchain','lake-manifest.json']:copy(PREP/'project-config'/name,PROJECT/name)
 wrapper=(TASK/'.rt/oi7/lean_call.py').read_text(encoding='utf-8').replace('OUTPUTS_INDEPENDENT_PATH_RECEIPT','PARAMETER_SUMMATION_INDEPENDENT_PATH_RECEIPT')
 (PROJECT/'lean_call.py').write_text(wrapper,encoding='utf-8')
 engine=(PREVIOUS/'run_sources.py').read_text(encoding='utf-8')
 engine=engine.replace("'.rt/oi7'","'.rt/psi1'").replace("'lakefile.lean'","'lakefile.toml'")
 engine=engine.replace('Independent Outputs native reviewer; no Outputs source authorship','Independent Parameter-Summation native reviewer; no Parameter-Summation source authorship')
 engine=engine.replace('OUTPUTS_INDEPENDENT_PATH_RECEIPT','PARAMETER_SUMMATION_INDEPENDENT_PATH_RECEIPT').replace('FRESH_21_NATIVE_SOURCE_AND_SERIALIZER_ACTUAL0','FRESH_22_NATIVE_SOURCE_AND_SERIALIZER_ACTUAL0').replace('actual_SOURCE_modules=21','actual_SOURCE_modules=22')
 (OUT/'run_sources.py').write_text(engine,encoding='utf-8')
 serializers=[]
 for name in ['IndependentExprDagV3','IndependentExprDagValidationV3']:
  original=PREVIOUS/(name+'.lean');target=PROJECT/(name+'.lean');snapshot=OUT/(name+'.lean');copy(original,target);copy(original,snapshot)
  serializers.append(dict(module=name,project_relative=target.name,source=bind(target),snapshot=bind(snapshot),original_SOURCE=bind(original)))
 assert sha(TASK/'formalization/CoefficientMapParameterSummationTransport.lean')==SOURCE_SHA
 stable=[bind(path) for path in PROJECT.rglob('*') if path.is_file()]+[bind(OUT/'run_sources.py'),bind(OUT/'inspect_prepare.py')]
 sourceprep=dict(status='PURE_FRESH_PARAMETER_SUMMATION_SOURCE_PREPARATION',role='Independent Parameter-Summation reviewer did not author17 proof',project_initially_absent=True,cache_initially_absent=True,own_project='.rt/psi1',native_sources=rows,serializer_sources=serializers,stable_files=stable,author_report=bind(AUTHOR/'author-audit.json'),author755bindings_personally_rehashed=True,author_actual_calls=dict(total=34,success=31,failed=3,all_failed_runs_excluded=True),original_complete_headers=author['original_complete_headers'],compiled_author_SOURCE=author['compiled_private_source'],verified_author_export=author['verified_export'],original_candidate=author['original_candidate'],generic_SOURCE_only_reuse=dict(recorder=bind(PREVIOUS/'run_sources.py'),wrapper=bind(TASK/'.rt/oi7/lean_call.py'),serializer_sources=[bind(PREVIOUS/(x+'.lean')) for x in ['IndependentExprDagV3','IndependentExprDagValidationV3']],previous_independent_proof_objects_borrowed=False),foreign_proof_objects_allowed=False,independent_PASS_claimed=False,Lean_invocations_in_preparation=0)
 dump(OUT/'source-preparation.json',sourceprep)
 root=load(OUT/'Root-independent-lane2-grant.json');assert root['Root_explicit_grant'] and root['lane']==2
 dump(OUT/'lane2-grant.json',dict(explicit_parent_lane2_granted=True,maximum_global_Lean_lanes=2,single_serial_Lean_j1=True,foreign_proof_objects_allowed=False,source_preparation_sha256=sha(OUT/'source-preparation.json'),original_parent_grant=bind(OUT/'Root-independent-lane2-grant.json')))
 print(json.dumps(dict(status=sourceprep['status'],author_rehash=755,SOURCE=22,project='.rt/psi1',sourceprep_SHA=sha(OUT/'source-preparation.json')),indent=2))
if __name__=='__main__':main()
