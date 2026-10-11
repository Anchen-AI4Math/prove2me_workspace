from prepare import OUT,TASK,ROOT,PROJECT,BUILD,MODULE,sha,dump,bind,verify,SOURCE_HASH
import json,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8');verify()
r=json.loads((OUT/'fresh-compile-receipt.json').read_text(encoding='utf-8'))
assert r['complete'] and r['rows'][-1]['exit_code']==0
assert sha(TASK/r['rows'][0]['output']['task_relative'])==r['rows'][0]['output']['sha256']
src=OUT/'e.lean';label='s07';wrapper=OUT/(label+'.ps1')
wrapper.write_bytes(('$env:LEAN_NUM_THREADS = "1"\n$env:LEAN_PATH = "'+BUILD.as_posix()+';" + $env:LEAN_PATH + ";'+PROJECT.as_posix()+'"\nSet-Location -LiteralPath "'+PROJECT.as_posix()+'"\n& lean "'+src.as_posix()+'"\nexit $LASTEXITCODE\n').encode())
cmd=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
p=subprocess.run(cmd,cwd=ROOT,capture_output=True);log=OUT/(label+'.log');log.write_bytes(p.stdout+p.stderr);ex=OUT/(label+'-exit.txt');ex.write_bytes((str(p.returncode)+'\n').encode())
r['rows'].append({'label':label,'logical_step':'five independently encoded universal endpoint types by actual kernel comparison','command':cmd,'exit_code':p.returncode,'source':bind(src),'log':bind(log),'exit_file':bind(ex),'wrapper':bind(wrapper),'output':None,
 'fresh_native_object_from_step':'s01','native_object_borrowed':False});r['complete']=p.returncode==0;dump(OUT/'fresh-compile-receipt.json',r)
print('five endpoint exact type controls: actual exit '+str(p.returncode),flush=True)
if p.returncode:print('\n'.join(x for x in log.read_text(encoding='utf-8',errors='replace').splitlines() if not x.startswith('{')),flush=True)
verify();assert p.returncode==0
