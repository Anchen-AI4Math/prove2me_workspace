"""Serial independent native Matrix audit; no inherited native objects or paths."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parents[1];PROJECT=TASK/'.rt/mi1'
AUTHOR=TASK/'verification/formalization-coefficient-map-matrix-2026-10-04'
AUTHOR_SHA='767b25d5db8a371308a875b023d58f050eb1969650e62917207157c6c8bbc010'
SOURCE_SHA='a4bf1766c8bbcc1f2f83af27594ba10b3dfcd4e55058f10ccc4d4b25cb9c6d99'
ORDER=['Definitions.Def_ZetaNine_HarmonicStability']+['missions.zeta9.formalization.'+n for n in [
 'CoefficientMap','CoefficientMapJet','CoefficientMapInjectivity','CoefficientMapPartialFractions',
 'CoefficientMapReflection','CoefficientMapFiniteSum','CoefficientMapSummation','CoefficientMapAggregate',
 'CoefficientMapShiftDegree','CoefficientMapTelescoper','CoefficientMapKernelBridge','CoefficientMapMatrix']]
PROGRAMS=['source-full-audit.lean','expected-types.lean','independent-boundary.lean','author-type-audit.lean','author-endpoint-audit.lean','kernel-types.lean','resolver.lean']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def verify_bindings(records):
 for r in records:
  p=ROOT/r['root_relative'];assert p.resolve().is_relative_to(ROOT.resolve()) and sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
def verify():
 h=load(OUT/'frozen-handoff.json');assert h['status']=='AUTHOR_FREEZE_VERIFIED_AND_LANE1_AUTHORIZED' and h['parent_serial_lane_authorized']
 assert sha(AUTHOR/'author-audit.json')==AUTHOR_SHA and h['author_report_sha256']==AUTHOR_SHA
 a=load(AUTHOR/'author-audit.json');assert a['verdict']=='PASS' and a['source_sha256']==SOURCE_SHA and len(a['stable_files'])==44
 verify_bindings(a['stable_files'])
 assert sha(OUT/'preparation-state.json')==h['source_preparation_state_sha256']
 prep=load(OUT/'preparation-state.json');assert prep['observed_candidate_sha256']==SOURCE_SHA and len(prep['source_bindings'])==13
 verify_bindings(prep['source_bindings'])
 for r in prep['source_bindings']:
  p=ROOT/r['root_relative'];q=PROJECT/r['root_relative'];assert p.read_bytes()==q.read_bytes() and sha(q)==r['sha256']
 dependency=prep['dependency_review'];verify_bindings([dependency]);d=load(ROOT/dependency['root_relative'])
 assert d['verdict']=='PASS' and len(d['stable_files'])==296;verify_bindings(d['stable_files'])
 for name in ['lean-toolchain','lake-manifest.json']:assert (PROJECT/name).read_bytes()==(ROOT/name).read_bytes()
 for name in ['type-audit.lean','endpoint-audit.lean']:assert (PROJECT/('author-'+name)).read_bytes()==(AUTHOR/name).read_bytes()
 for name in ['source-full-audit.lean','expected-types.lean','independent-boundary.lean','kernel-types.lean','resolver.lean']:assert (PROJECT/name).read_bytes()==(OUT/name).read_bytes()
 packages=PROJECT/'.lake/packages';assert packages.is_junction() and packages.resolve()==(ROOT/'.lake/packages').resolve()
 return prep
def run(logical,cmd,source=None,object_path=None,resume=False):
 verify();p=OUT/'actual-execution-receipt.json';r=load(p)
 found=[x for x in r['rows'] if x['logical_step']==logical]
 if found:
  assert resume and len(found)==1;row=found[0];assert row['actual_exit']==0
  for k in ['log','exit_file']:assert sha(OUT/row[k])==row[k+'_sha256']
  if source:assert sha(source)==row['source_sha256']
  if object_path:assert sha(object_path)==row['object_sha256']
  print(logical+': identical own successful cache reused',flush=True);return row
 index=len(r['rows'])+1;label='e'+str(index).zfill(2);log=OUT/(label+'.log');exitfile=OUT/(label+'-exit.txt')
 assert len(str(log))+64<=259 and len(str(exitfile))+64<=259
 env=dict(os.environ)
 for name in ['LEAN_PATH','LEAN_SRC_PATH']:env.pop(name,None)
 env['LEAN_NUM_THREADS']='1';env['LAKE_JOBS']='1'
 start=time.monotonic()
 with log.open('wb') as output:result=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=output,stderr=subprocess.STDOUT)
 write(exitfile,str(result.returncode)+'\n')
 row={'label':label,'logical_step':logical,'command':cmd,'cwd':str(PROJECT),'actual_exit':result.returncode,
  'inherited_Lean_search_paths_removed':True,'serial_lane':1,'Lean_num_threads':1,
  'elapsed_seconds':round(time.monotonic()-start,3),'log':log.name,'log_sha256':sha(log),'exit_file':exitfile.name,'exit_file_sha256':sha(exitfile),
  'source_root_relative':source.relative_to(ROOT).as_posix() if source else None,'source_sha256':sha(source) if source else None,
  'object_task_relative':object_path.relative_to(TASK).as_posix() if object_path and object_path.exists() else None,
  'object_sha256':sha(object_path) if object_path and object_path.exists() else None}
 r['rows'].append(row);dump(p,r);print(logical+': actual exit '+str(result.returncode),flush=True)
 verify()
 if result.returncode:raise SystemExit(result.returncode)
 return row
def main():
 parser=argparse.ArgumentParser();parser.add_argument('mode',choices=['source','controls']);parser.add_argument('--parent-lane-authorized',action='store_true',required=True);parser.add_argument('--resume',action='store_true');args=parser.parse_args()
 verify();receipt=OUT/'actual-execution-receipt.json'
 if not receipt.exists():
  assert not args.resume and not(PROJECT/'b').exists() and not(PROJECT/'.lake/build').exists()
  dump(receipt,{'status':'IN_PROGRESS','empty_independent_cache_verified_before_first_run':True,'author_native_objects_borrowed':False,'rows':[],
   'original_control_programs':[{ 'name':name,'sha256':sha(PROJECT/name)} for name in PROGRAMS]})
 if args.mode=='source':
  for m in ORDER:
   src=PROJECT/(m.replace('.','/')+'.lean');obj=PROJECT/'b/lib/lean'/(m.replace('.','/')+'.olean');assert len(str(obj))+64<=259
   run('fresh source '+m,['lake','--no-cache','build',m],src,obj,args.resume)
  r=load(receipt);r['source_phase_complete']=True;dump(receipt,r)
  print('All13 real sources compiled in the initially empty independent cache',flush=True)
 else:
  r=load(receipt);assert r['source_phase_complete'] and all(x['actual_exit']==0 for x in r['rows'])
  run('actual pinned runtime',['lake','env','lean','--version'],resume=args.resume)
  for name in PROGRAMS[:-1]:run('actual own '+name,['lake','env','lean',str(PROJECT/name)],PROJECT/name,resume=args.resume)
  run('actual own thirteen module resolver',['lake','env','lean','--run',str(PROJECT/'resolver.lean')],PROJECT/'resolver.lean',resume=args.resume)
  r=load(receipt);r['controls_phase_complete']=True;r['status']='ALL_REQUESTED_EXECUTIONS_FINISHED';dump(receipt,r)
if __name__=='__main__':main()
