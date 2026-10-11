"""One native author lane. Direct Lean compilation writes only the new objects."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/ft1';PARENT=TASK/'.rt/ps1'
AUTHOR=TASK/'verification/formalization-coefficient-map-parameter-shift-2026-10-04'
AUTHOR_SHA='4a8dbe4ff74047e223054a4b14ca034ca73c900513ed205dcdd8ff91bd670642'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def bind(p):return {'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def gate():
 assert sha(AUTHOR/'author-audit.json')==AUTHOR_SHA
 a=load(AUTHOR/'author-audit.json');assert a['verdict']=='PASS' and len(a['stable_files'])==59
 s=load(OUT/'preparation-state.json')
 for r in a['stable_files']+s['parent_source_and_objects']+s['new_project_copies']+s['pinned_runtime']+[s['design_freeze']]:
  p=ROOT/r['root_relative'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
 assert sha(TASK/'formalization/CoefficientMapFormalTransportData.lean')==s['frozen_data_sha256']=='ae9f4eab8efecd88aaae5d4b13da7ba4bed7db89bbf257d3b0645e1b8584fb27'
 assert (PROJECT/'.lake/packages').is_junction() and (PROJECT/'.lake/packages').resolve()==(ROOT/'.lake/packages').resolve()
 return s
def run(mode,name):
 gate();source=TASK/'formalization'/(name+'.lean') if mode=='compile' else (PROJECT/'lean-toolchain' if mode=='runtime' else OUT/name)
 assert source.is_file();destination=PROJECT/'missions/zeta9/formalization'/source.name if mode=='compile' else PROJECT/source.name
 if mode!='runtime':write(destination,source.read_bytes())
 receipt=OUT/'actual-execution-receipt.json';r=load(receipt) if receipt.exists() else {'parent_cache_reused':True,'fresh_parent_build_claimed':False,'independent_objects_borrowed':False,'rows':[]}
 index=len(r['rows'])+1;label='e'+str(index).zfill(2);folder=OUT/label;folder.mkdir()
 write(folder/source.name,source.read_bytes());object_path=None
 if mode=='compile':
  object_path=PROJECT/'b/lib/lean/missions/zeta9/formalization'/(name+'.olean');object_path.parent.mkdir(parents=True,exist_ok=True)
  assert len(str(object_path))+64<=259
  command=['lake','env','lean','-o',str(object_path),str(destination)]
 elif mode=='runtime':command=['lake','env','lean','--version']
 else:command=['lake','env','lean']+(['--run'] if mode=='resolver' else [])+[str(destination)]
 log=folder/'run.log';exitfile=folder/'exit.txt';assert len(str(log))+64<=259
 env=dict(os.environ)
 for n in ['LEAN_PATH','LEAN_SRC_PATH']:env.pop(n,None)
 env['LEAN_NUM_THREADS']='1';env['LAKE_JOBS']='1'
 start=time.monotonic()
 with log.open('wb') as f:res=subprocess.run(command,cwd=PROJECT,env=env,stdout=f,stderr=subprocess.STDOUT)
 write(exitfile,str(res.returncode)+'\n')
 row={'label':label,'mode':mode,'name':name,'command':command,'cwd':str(PROJECT),'actual_exit':res.returncode,'elapsed_seconds':round(time.monotonic()-start,3),
  'source':bind(source),'actual_input':bind(folder/source.name),'log':bind(log),'exit_file':bind(exitfile),
  'inherited_Lean_search_paths_removed':True,'serial_lane':1,'same_author_parent_cache_reused':True,'fresh_parent_build_claimed':False,
  'independent_objects_borrowed':False,'object':bind(object_path) if object_path and object_path.exists() else None}
 if object_path and res.returncode==0:write(folder/'compiled.olean',object_path.read_bytes());row['retained_object']=bind(folder/'compiled.olean')
 r['rows'].append(row);dump(receipt,r);gate();print(name,mode,'actual exit',res.returncode,flush=True)
 return res.returncode
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['compile','audit','resolver','runtime']);p.add_argument('name');p.add_argument('--parent-lane-authorized',action='store_true',required=True);args=p.parse_args()
 raise SystemExit(run(args.mode,args.name))
