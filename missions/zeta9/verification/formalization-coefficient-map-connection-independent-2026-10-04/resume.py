"""Explicit guarded retry of independent controls; never relabel previous steps fresh."""
from prepare import OUT,TASK,ROOT,PROJECT,BUILD,MODULE,sha,dump,bind,verify,SOURCE_HASH
import json,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
verify()
old=json.loads((OUT/'failed-own-boundary-01/fresh-compile-receipt.json').read_text(encoding='utf-8'))
assert len(old['rows'])==5 and [r['exit_code'] for r in old['rows']]==[0,0,0,0,1]
for row in old['rows'][:4]:
 for key in ['source','log','exit_file','wrapper','output']:
  b=row.get(key)
  if b: assert sha(TASK/b['task_relative'])==b['sha256']
assert sha(PROJECT/(MODULE.replace('.','/')+'.lean'))==SOURCE_HASH
src=OUT/'b.lean';label='s06';wrapper=OUT/(label+'.ps1')
script='$env:LEAN_NUM_THREADS = "1"\n$env:LEAN_PATH = "'+BUILD.as_posix()+';" + $env:LEAN_PATH + ";'+PROJECT.as_posix()+'"\nSet-Location -LiteralPath "'+PROJECT.as_posix()+'"\n& lean "'+src.as_posix()+'"\nexit $LASTEXITCODE\n';wrapper.write_bytes(script.encode())
cmd=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
p=subprocess.run(cmd,cwd=ROOT,capture_output=True);log=OUT/(label+'.log');log.write_bytes(p.stdout+p.stderr);ex=OUT/(label+'-exit.txt');ex.write_bytes((str(p.returncode)+'\n').encode())
row={'label':label,'logical_step':'corrected own boundary same guarded fresh-source cache','command':cmd,'exit_code':p.returncode,'source':bind(src),'log':bind(log),'exit_file':bind(ex),'wrapper':bind(wrapper),'output':None,
 'fresh_native_object_from_step':old['rows'][0]['label'],'native_object_borrowed':False,'successful_prior_steps_reused_only_same_project':True}
old['rows'].append(row);old['complete']=p.returncode==0;old['retained_failed_step_labels']=['s05'];old['native_object_borrowed']=False;dump(OUT/'fresh-compile-receipt.json',old)
print('corrected own boundaries: actual exit '+str(p.returncode),flush=True)
if p.returncode:print('\n'.join(x for x in log.read_text(encoding='utf-8',errors='replace').splitlines() if not x.startswith('{')),flush=True)
verify();assert p.returncode==0
