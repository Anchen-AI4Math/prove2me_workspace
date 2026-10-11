from pathlib import Path
import argparse,hashlib,json,subprocess,sys,shutil
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent; TASK=OUT.parents[1]; ROOT=TASK.parents[1]; CACHE=OUT/'build'
AUTHOR=TASK/'verification/formalization-coefficient-map-kernel-2026-10-04'
TELE=TASK/'verification/formalization-coefficient-map-telescoper-independent-2026-10-04'
EXPECTED={'source':'1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb',
 'receipt':'07ed208d0eef9d16632320ee1710c4c62919cc948f5fe770eba5dcc315656aa7',
 'manifest':'5e6481b76038db693c73f3bc13f582019ff5ce06c3f5361dadf88d218f69a498',
 'telescoper_review':'cac46e0ea0674bcd4b2dca543326ab2d9bdd3cd8a409cba8988bfea0130a556a',
 'shift_source':'96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,v): p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def gates():
 assert sha(TASK/'formalization/CoefficientMapKernelBridge.lean')==EXPECTED['source']
 assert sha(TASK/'formalization/CoefficientMapShiftDegree.lean')==EXPECTED['shift_source']
 assert sha(AUTHOR/'compile-receipt.json')==EXPECTED['receipt']
 assert sha(AUTHOR/'SHA256SUMS.txt')==EXPECTED['manifest']
 assert sha(TELE/'independent-review.json')==EXPECTED['telescoper_review']
 prior=load(TELE/'independent-review.json')
 assert prior['verdict']=='PASS' and all(c['pass'] for c in prior['checks'])
 for r in prior['stable_files']: assert sha(ROOT/r['root_relative'])==r['sha256'],r['root_relative']
 author=[]
 for line in (AUTHOR/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
  if line.strip():
   h,path=line.split('  ',1); p=(TASK/path).resolve(); assert sha(p)==h,str(p)
   author.append({'path':str(p),'sha256':h})
 return {'telescoper_report_sha256':EXPECTED['telescoper_review'],'prior_bound_files':len(prior['stable_files']),
  'prior_cache':str(TELE/'build'),'author_manifest_bindings':author}
ap=argparse.ArgumentParser(); ap.add_argument('mode',choices=['native','boundary']); args=ap.parse_args()
reuse=gates(); rec=OUT/'independent-compile-receipt.json'; rows=load(rec)['rows'] if rec.exists() else []
cloned=[]
for src in (TELE/'build').rglob('*.olean'):
 dest=CACHE/src.relative_to(TELE/'build'); dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists(): shutil.copyfile(src,dest)
 assert sha(dest)==sha(src)
 cloned.append({'prior':str(src),'new':str(dest),'sha256':sha(dest)})
def run(label,src,output=None):
 assert not (OUT/f'{label}.log').exists()
 wrapper=OUT/f'{label}.ps1'; cmd=f'$env:LEAN_PATH="{CACHE.as_posix()};" + $env:LEAN_PATH\n& lean '
 if output:
  output.parent.mkdir(parents=True,exist_ok=True); cmd+=f'-o "{output.as_posix()}" '
 cmd+=f'"{src.as_posix()}"\nexit $LASTEXITCODE\n'; wrapper.write_text(cmd,encoding='utf-8')
 inv=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
 p=subprocess.run(inv,cwd=ROOT,capture_output=True)
 log=OUT/f'{label}.log'; log.write_bytes(p.stdout+p.stderr)
 ex=OUT/f'{label}-exit.txt'; ex.write_text(str(p.returncode)+'\n',encoding='utf-8')
 rows.append({'label':label,'command':inv,'cwd':str(ROOT),'source':str(src),'source_sha256':sha(src),
  'exit_code':p.returncode,'exit_file':str(ex),'exit_sha256':sha(ex),'log':str(log),'log_sha256':sha(log),
  'wrapper':str(wrapper),'wrapper_sha256':sha(wrapper),'output':str(output) if output else None,
  'output_sha256':sha(output) if output and output.exists() else None})
 gates(); write(rec,{'role':'Independent mathematical source and type replay','expected':EXPECTED,'reuse':reuse,
  'cloned_fixed_objects':cloned,'new_cache':str(CACHE),'rows':rows,'author_objects_used':False,'root_mission_objects_used':False})
 print(label+': '+str(p.returncode),flush=True)
 if p.returncode: print(log.read_text(encoding='utf-8-sig')[:14000],flush=True)
 return p.returncode
if args.mode=='native':
 for name in ['CoefficientMapShiftDegree','CoefficientMapKernelBridge']:
  if any(r['label'].startswith('native-'+name) and r['exit_code']==0 for r in rows): continue
  attempt=sum(r['label'].startswith('native-'+name) for r in rows)+1
  if run(f'native-{name}-{attempt:02}',TASK/'formalization'/f'{name}.lean',CACHE/'missions/zeta9/formalization'/f'{name}.olean'): sys.exit(1)
 if run('author-type-replay-01',AUTHOR/'type-audit.lean'): sys.exit(1)
else:
 assert any(r['label'].startswith('author-type-replay') and r['exit_code']==0 for r in rows)
 attempt=sum(r['label'].startswith('independent-boundary') for r in rows)+1
 sys.exit(run(f'independent-boundary-{attempt:02}',OUT/'independent-boundary.lean'))
