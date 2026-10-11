from pathlib import Path
import json,os,re,subprocess,sys,time
import inspect_prepare as p
PY=r'C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe'
def gate():
 grant=p.load(p.OUT/'Root-platform-author-lane2-grant.json');assert grant['Root_explicit_grant'] and grant['lane']==2 and not grant['API_calls_permitted']
 prep=p.load(p.OUT/'source-preparation.json');p.check(prep['stable_files']);assert p.sha(p.INDEP/'independent-audit.json')==p.INDEP_SHA
 return prep
def configure(ctx):
 link=ctx/'.lake/packages';expected=p.ROOT/'.lake/packages'
 if not link.exists():
  link.parent.mkdir(parents=True,exist_ok=True)
  result=subprocess.run(['pwsh','-NoProfile','-Command','New-Item -ItemType Junction -Path "'+str(link)+'" -Target "'+str(expected)+'" | Out-Null'],capture_output=True)
  (p.OUT/('junction-'+ctx.name+'.log')).write_bytes(result.stdout+result.stderr)
  assert result.returncode==0
 assert link.is_junction() and link.resolve()==expected.resolve()
def run(tag,label,module=None,source=None):
 prep=gate();ctx=p.PROJECT/tag;configure(ctx)
 rp=p.OUT/'execution-receipt.json';r=p.load(rp) if rp.exists() else dict(role='Phase platform AUTHOR',rows=[])
 inputs=[p.bind(ctx/x) for x in ['lakefile.toml','lean-toolchain','lake-manifest.json','lean_call.py']]
 if source:inputs.append(p.bind(ctx/source))
 # Actual prior outputs can be reused only within this same exact context after rehash.
 previous=next((x for x in reversed(r['rows']) if x['tag']==tag and x['label']==label and x['exit_code']==0 and x['input_bindings']==inputs),None)
 if previous:p.check(previous['input_bindings']+previous['output_bindings']+previous['evidence_bindings']);print(tag+'/'+label+': own exact prior actual0 retained',flush=True);return
 occupied=[int(x.name[1:4]) for x in (p.OUT/'actual-runs').glob('c[0-9][0-9][0-9]-*')] if (p.OUT/'actual-runs').exists() else []
 num=max([len(r['rows'])]+occupied)+1;folder=p.OUT/'actual-runs'/('c'+str(num).zfill(3)+'-'+tag+'-'+label);folder.mkdir(parents=True,exist_ok=False)
 snapshots=[]
 for i,b in enumerate(inputs):
  target=folder/('i'+str(i).zfill(2));target.write_bytes(p.resolve(b).read_bytes());snapshots.append(dict(original=b,retained=p.bind(target)))
 obj=ctx/'b/lib/lean'/(module.replace('.','/')+'.olean') if module else None
 if obj:obj.parent.mkdir(parents=True,exist_ok=True)
 args=['lean','-j1']+(['-o',str(obj.relative_to(ctx)),source] if module else ['--version'])
 command=['lake','env',PY,'lean_call.py']+args
 env=dict(os.environ);env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None);env['LEAN_NUM_THREADS']='1';env['LAKE_JOBS']='1';env['PHASE_PLATFORM_PATH_RECEIPT']=str(folder/'selected-paths.json')
 start=time.monotonic()
 with (folder/'stdout.log').open('wb') as out,(folder/'stderr.log').open('wb') as err:result=subprocess.run(command,cwd=ctx,env=env,stdout=out,stderr=err)
 with (folder/'combined.log').open('wb') as out:
  for name in ['stdout.log','stderr.log']:
   with (folder/name).open('rb') as f:
    while block:=f.read(1024*1024):out.write(block)
 (folder/'exit.txt').write_text(str(result.returncode)+'\n',encoding='ascii')
 outputs=[]
 if obj and obj.exists():
  for actual in sorted(obj.parent.glob(obj.name+'*')):
   b=p.bind(actual);outputs.append(b);snap=folder/('o'+str(len(outputs)).zfill(2));snap.write_bytes(actual.read_bytes());snapshots.append(dict(original=b,retained=p.bind(snap)))
 evidence=[p.bind(folder/x) for x in ['stdout.log','stderr.log','combined.log','exit.txt','selected-paths.json'] if (folder/x).exists()]
 row=dict(tag=tag,label=label,module=module,source=source,command=command,execution_CWD=str(ctx),exit_code=result.returncode,elapsed_seconds=round(time.monotonic()-start,3),input_bindings=inputs,output_bindings=outputs,evidence_bindings=evidence,immutable_snapshots=snapshots,folder_task_relative=folder.relative_to(p.TASK).as_posix(),all_actual_handles_terminal=True,whole_failed_run_excluded=result.returncode!=0,actual_environment=dict(LEAN_NUM_THREADS='1',LAKE_JOBS='1'))
 r['rows'].append(row);p.dump(rp,r);print(tag+'/'+label+': actual '+str(result.returncode)+' ('+str(row['elapsed_seconds'])+'s)',flush=True)
 if result.returncode:
  with (folder/'combined.log').open('rb') as f:f.seek(max(0,f.seek(0,2)-7000));print(f.read().decode('utf-8',errors='replace'),flush=True)
 assert result.returncode==0,'Whole actual failed run preserved; no repair of original/staged bytes'
 gate()
def main():
 sys.stdout.reconfigure(encoding='utf-8');prep=gate();run('native','runtime')
 for context in prep['contexts']:
  for row in context['math_sources']:run(context['tag'],row['label'],row['module'],row['path'])
 p.dump(p.OUT/'source-terminal.json',dict(status='ALL_FRESH_ISOLATED_CONTEXT_SOURCE_COMPILATIONS_ACTUAL0',all_actual_handles_terminal=True,author_PASS_claimed=False,API_calls=0))
if __name__=='__main__':main()
