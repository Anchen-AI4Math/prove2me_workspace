from pathlib import Path
import argparse, hashlib, json, subprocess, sys
from prepare import verify,OUT,TASK,ROOT,PROJECT,BUILD,MODULE,sha,dump,bind
sys.stdout.reconfigure(encoding='utf-8')
parser=argparse.ArgumentParser();parser.add_argument('--parent-lane-authorized',action='store_true');args=parser.parse_args()
assert args.parent_lane_authorized,'Explicit parent lane allocation required'
verify();enroll=json.loads((OUT/'enrollment.json').read_text(encoding='utf-8'))
assert not BUILD.exists(),'Fresh cache only; explicitly bound resume is separate'
for row in enroll['stable_files']:
 p=TASK/row['task_relative'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
rows=[]
def run(logical,src,output=None):
 label='s'+str(len(rows)+1).zfill(2);wrapper=OUT/(label+'.ps1')
 script='$env:LEAN_NUM_THREADS = "1"\n$env:LEAN_PATH = "'+BUILD.as_posix()+';" + $env:LEAN_PATH + ";'+PROJECT.as_posix()+'"\nSet-Location -LiteralPath "'+PROJECT.as_posix()+'"\n& lean '
 if output:output.parent.mkdir(parents=True,exist_ok=True);script+='-o "'+output.as_posix()+'" '
 script+='"'+src.as_posix()+'"\nexit $LASTEXITCODE\n';wrapper.write_bytes(script.encode())
 invocation=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
 p=subprocess.run(invocation,cwd=ROOT,capture_output=True);log=OUT/(label+'.log');log.write_bytes(p.stdout+p.stderr)
 ex=OUT/(label+'-exit.txt');ex.write_bytes((str(p.returncode)+'\n').encode())
 row={'label':label,'logical_step':logical,'command':invocation,'exit_code':p.returncode,'source':bind(src),'log':bind(log),'exit_file':bind(ex),'wrapper':bind(wrapper),
  'output':bind(output) if output and output.exists() else None,'lean_working_directory':str(PROJECT),'only_Mathlib_cache_shared':True,'native_object_borrowed':False}
 rows.append(row);dump(OUT/'fresh-compile-receipt.json',{'complete':False,'rows':rows,'source_sha256':enroll['source_sha256']})
 print(logical+': actual exit '+str(p.returncode),flush=True);verify()
 if p.returncode:print(log.read_text(encoding='utf-8',errors='replace'),flush=True)
 assert p.returncode==0,'Failed source/log/exit retained; no automatic retry'
run('fresh actual Connection native source',PROJECT/(MODULE.replace('.','/')+'.lean'),BUILD/(MODULE.replace('.','/')+'.olean'))
run('fresh own actual module graph/types/full values',OUT/'t.lean')
run('fresh original author exact type audit',PROJECT/'a.lean')
run('fresh original author boundary audit',PROJECT/'ab.lean')
run('fresh independent own boundaries',OUT/'b.lean')
dump(OUT/'fresh-compile-receipt.json',{'complete':True,'rows':rows,'source_sha256':enroll['source_sha256']})
assert len(rows)==5 and all(r['exit_code']==0 for r in rows)
