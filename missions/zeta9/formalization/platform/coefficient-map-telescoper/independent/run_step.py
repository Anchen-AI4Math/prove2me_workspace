from pathlib import Path
import hashlib,json,subprocess,sys
from verify_handoff import verify,OUT,TASK,ROOT,BATCH,sha,load
PROJECT=OUT/'p';BUILD=TASK/'.rt/ti1/b';N=BUILD/'n/lib/lean';P=BUILD/'p/lib/lean'
sys.stdout.reconfigure(encoding='utf-8')
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s.encode() if isinstance(s,str) else s)
def dump(p,d):write(p,json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def rows(p):return [json.loads(s) for s in p.read_text(encoding='utf-8-sig').splitlines() if s.startswith('{')]
def run(logical,src,cache,output=None,args=None,copy=None):
 verify();rp=OUT/'review-compile-receipt.json';receipt=load(rp) if rp.exists() else {'complete':False,'rows':[],'native_and_staged_objects_borrowed':False}
 prior=[r for r in receipt['rows'] if r['logical_step']==logical]
 if prior:
  assert len(prior)==1
  r=prior[0];assert r['exit_code']==0 and r['source_sha256']==sha(src) and r['cache_task_relative']==cache.relative_to(TASK).as_posix()
  for key in ['log','exit_file','wrapper','stdout_copy']:
   if r.get(key):assert sha(OUT/r[key])==r[key+'_sha256']
  if output:assert sha(output)==r['output_sha256']
  print(logical+': own identical cache hash-bound success reused',flush=True);return
 label='r'+str(len(receipt['rows'])+1).zfill(2);wrapper=OUT/(label+'.ps1')
 blocked=(ROOT/'.lake/build/lib/lean').as_posix().casefold()
 script='$env:LEAN_NUM_THREADS = "1"\n$blockedRootProofCache = "'+blocked+'"\n$packagePathEntries = @($env:LEAN_PATH -split ";" | Where-Object { $_ -and ([System.IO.Path]::GetFullPath($_).Replace("\\", "/").TrimEnd("/").ToLowerInvariant() -ne $blockedRootProofCache) })\n$env:LEAN_PATH = "'+cache.as_posix()+';" + ($packagePathEntries -join ";") + ";'+PROJECT.as_posix()+'"\nSet-Location -LiteralPath "'+PROJECT.as_posix()+'"\n& lean '
 if output:output.parent.mkdir(parents=True,exist_ok=True);script+='-o "'+output.as_posix()+'" '
 if args is not None:script+='--run '
 script+='"'+src.as_posix()+'"'+''.join(' "'+a+'"' for a in args or [])+'\nexit $LASTEXITCODE\n';write(wrapper,script)
 assert len(str(src))<=259,(src,len(str(src)))
 for p in [wrapper,OUT/(label+'.log'),OUT/(label+'-exit.txt')]+([output] if output else [])+([copy] if copy else []):assert len(str(p))+64<=259,(p,len(str(p))+64)
 cmd=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
 p=subprocess.run(cmd,cwd=ROOT,capture_output=True);log=OUT/(label+'.log');write(log,p.stdout+p.stderr);ex=OUT/(label+'-exit.txt');write(ex,str(p.returncode)+'\n')
 if copy:write(copy,p.stdout)
 receipt['rows'].append({'label':label,'logical_step':logical,'command':cmd,'exit_code':p.returncode,'source_root_relative':src.relative_to(ROOT).as_posix(),'source_sha256':sha(src),
  'log':log.name,'log_sha256':sha(log),'exit_file':ex.name,'exit_file_sha256':sha(ex),'wrapper':wrapper.name,'wrapper_sha256':sha(wrapper),
  'cache_task_relative':cache.relative_to(TASK).as_posix(),'output_task_relative':output.relative_to(TASK).as_posix() if output else None,'output_sha256':sha(output) if output and output.exists() else None,
  'stdout_copy':copy.name if copy else None,'stdout_copy_sha256':sha(copy) if copy else None,'lean_working_directory':str(PROJECT)})
 dump(rp,receipt);print(logical+': actual exit '+str(p.returncode),flush=True);verify()
 if p.returncode:print('\n'.join(x for x in log.read_text(encoding='utf-8',errors='replace').splitlines() if not x.startswith('{')),flush=True)
 assert p.returncode==0,'Failed actual source/log/exit preserved; explicit new retry required'
