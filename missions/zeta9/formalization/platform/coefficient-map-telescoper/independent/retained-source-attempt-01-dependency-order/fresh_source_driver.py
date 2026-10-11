"""First fresh phase, disabled until frozen handoff and explicit parent lane grant."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
from verify_handoff import verify
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[3];ROOT=TASK.parents[1];PROJECT=OUT/'p';BUILD=TASK/'.rt/ti1/b'
N=BUILD/'n/lib/lean';P=BUILD/'p/lib/lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def dump(p,d):p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
parser=argparse.ArgumentParser();parser.add_argument('--parent-lane-authorized',action='store_true');args=parser.parse_args()
assert args.parent_lane_authorized,'Await parent single Lean lane allocation; never start a third lane'
handoff=verify();enroll=load(OUT/'preparation-enrollment.json');assert not BUILD.exists(),'Fresh cache required; failed attempts must be preserved and explicitly hash-bound before any resume'
preflight=load(OUT/'output-path-preflight.json');assert preflight['all_paths_with_64_char_suffix_below_260'] and preflight['native_and_platform_cache_separate']
rs=[]
def run(logical,source,cache,output=None):
 label='s'+str(len(rs)+1).zfill(2);wrapper=OUT/(label+'.ps1')
 script=f'$env:LEAN_NUM_THREADS = "1"\n$env:LEAN_PATH = "{cache.as_posix()};" + $env:LEAN_PATH + ";{PROJECT.as_posix()}"\nSet-Location -LiteralPath "{PROJECT.as_posix()}"\n& lean '
 if output:output.parent.mkdir(parents=True,exist_ok=True);script+='-o "'+output.as_posix()+'" '
 script+='"'+source.as_posix()+'"\nexit $LASTEXITCODE\n';wrapper.write_bytes(script.encode())
 invocation=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
 p=subprocess.run(invocation,cwd=ROOT,capture_output=True);log=OUT/(label+'.log');log.write_bytes(p.stdout+p.stderr);ex=OUT/(label+'-exit.txt');ex.write_bytes((str(p.returncode)+'\n').encode())
 rs.append({'label':label,'logical_step':logical,'command':invocation,'exit_code':p.returncode,'lake_env_working_directory':str(ROOT),'lean_working_directory':str(PROJECT),
  'source_root_relative':source.relative_to(ROOT).as_posix(),'source_sha256':sha(source),'log':log.name,'log_sha256':sha(log),'exit_file':ex.name,'exit_file_sha256':sha(ex),
  'wrapper':wrapper.name,'wrapper_sha256':sha(wrapper),'cache_task_relative':cache.relative_to(TASK).as_posix(),'output_task_relative':output.relative_to(TASK).as_posix() if output else None,'output_sha256':sha(output) if output and output.exists() else None})
 dump(OUT/'fresh-source-compile-receipt.json',{'complete':False,'rows':rs,'native_and_staged_objects_borrowed':False,'root_scope_API_credentials_writes':False});print(logical+': actual exit '+str(p.returncode),flush=True)
 verify()
 if p.returncode:print(log.read_text(encoding='utf-8-sig'),flush=True)
 assert p.returncode==0,'Keep actual failed source/log/exit/object evidence separately; no automatic rerun'
run('native pure Harmonic Def',PROJECT/'Definitions/Def_ZetaNine_HarmonicStability.lean',N,N/'Definitions/Def_ZetaNine_HarmonicStability.olean')
for m in enroll['original_source_hashes']:run('native '+m,PROJECT/'missions/zeta9/formalization'/(m+'.lean'),N,N/'missions/zeta9/formalization'/(m+'.olean'))
for r in enroll['fixed_native_controls']:run('native control '+r['module'],PROJECT/(r['module']+'.lean'),N,N/(r['module']+'.olean'))
for r in enroll['pure_Def_dependencies']:run('pure Def '+r['root_relative'],PROJECT/r['root_relative'],P,P/(r['root_relative'].removesuffix('.lean')+'.olean'))
run('native Aggregate alias',PROJECT/'NativeValueComparisonDefinition.lean',N,N/'NativeValueComparisonDefinition.olean')
run('native Aggregate actual six kernel plus nine rfl',OUT/'agg-native-values.lean',N)
run('staged Aggregate alias',PROJECT/'StagedValueComparisonDefinition.lean',P,P/'StagedValueComparisonDefinition.olean')
run('staged Aggregate actual six kernel plus nine rfl',OUT/'agg-staged-values.lean',P)
dump(OUT/'fresh-source-compile-receipt.json',{'complete':True,'rows':rs,'native_and_staged_objects_borrowed':False,'root_scope_API_credentials_writes':False})
assert len(rs)==25 and all(r['exit_code']==0 for r in rs)
