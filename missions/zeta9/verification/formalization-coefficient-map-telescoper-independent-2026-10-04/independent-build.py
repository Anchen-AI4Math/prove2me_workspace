from pathlib import Path
import argparse, hashlib, json, subprocess, sys, shutil
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]; ROOT=TASK.parents[1]
CACHE=OUT/'build'
PREV=TASK/'verification/formalization-coefficient-map-summation-independent-2026-10-04'
AUTHOR=TASK/'verification/formalization-coefficient-map-telescoper-2026-10-04'
EXPECTED={'source':'8792e8ba5c6abcbdbe83b0aa4ffa1ab716fd05fac10da7275b86ab2f780fd121',
 'receipt':'7deebfee272c749261e85381cf51262ac4c1692457e908c749bc20596884b8e4',
 'manifest':'c5b4984a10080e914929f9c81073a162eced7ec6c1aecae9d777aad222055de8',
 'prior_review':'fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa',
 'aggregate':'e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,v): p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def gates():
 assert sha(TASK/'formalization/CoefficientMapTelescoper.lean')==EXPECTED['source']
 assert sha(TASK/'formalization/CoefficientMapAggregate.lean')==EXPECTED['aggregate']
 assert sha(AUTHOR/'compile-receipt.json')==EXPECTED['receipt']
 assert sha(AUTHOR/'SHA256SUMS.txt')==EXPECTED['manifest']
 assert sha(PREV/'independent-review.json')==EXPECTED['prior_review']
 prior=load(PREV/'independent-review.json')
 assert prior['verdict']=='PASS' and all(c['pass'] for c in prior['checks'])
 bindings=prior['stable_files']
 for row in bindings:
  p=ROOT/row['root_relative']; assert sha(p)==row['sha256'],str(p)
 for name,h in prior['sources_sha256'].items(): assert sha(TASK/'formalization'/f'{name}.lean')==h
 author=[]
 for line in (AUTHOR/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
  if line.strip():
   h,path=line.split('  ',1); p=(TASK/path).resolve(); assert sha(p)==h,str(p)
   author.append({'path':str(p),'sha256':h})
 return {'prior_review_sha256':EXPECTED['prior_review'],'prior_file_bindings_recomputed':len(bindings),
  'prior_cache':str(PREV/'native/build'),'prior_observed_successes':load(PREV/'independent-compile-receipt.json')['rows'],
  'author_manifest_bindings_recomputed':author}
ap=argparse.ArgumentParser(); ap.add_argument('mode',choices=['native','boundary']); args=ap.parse_args()
reuse=gates(); receipt=OUT/'independent-compile-receipt.json'
rows=load(receipt)['rows'] if receipt.exists() else []
for src in (PREV/'native/build').rglob('*.olean'):
 dest=CACHE/src.relative_to(PREV/'native/build'); dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists(): shutil.copyfile(src,dest)
 assert sha(dest)==sha(src)
def run(label,source,output=None):
 assert not (OUT/f'{label}.log').exists(),'Use a new attempt label; preserve observed evidence.'
 wrapper=OUT/f'{label}.ps1'
 cmd=f'$env:LEAN_PATH="{CACHE.as_posix()};{(PREV/"native/build").as_posix()};" + $env:LEAN_PATH\n& lean '
 if output:
  output.parent.mkdir(parents=True,exist_ok=True); cmd+=f'-o "{output.as_posix()}" '
 cmd+=f'"{source.as_posix()}"\nexit $LASTEXITCODE\n'
 wrapper.write_text(cmd,encoding='utf-8')
 invocation=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
 p=subprocess.run(invocation,cwd=ROOT,capture_output=True)
 log=OUT/f'{label}.log'; log.write_bytes(p.stdout+p.stderr)
 ex=OUT/f'{label}-exit.txt'; ex.write_text(str(p.returncode)+'\n',encoding='utf-8')
 row={'label':label,'command':invocation,'cwd':str(ROOT),'exit_code':p.returncode,
  'source':str(source),'source_sha256':sha(source),'log':str(log),'log_sha256':sha(log),
  'exit_file':str(ex),'exit_sha256':sha(ex),'wrapper':str(wrapper),'wrapper_sha256':sha(wrapper),
  'output':str(output) if output else None,'output_sha256':sha(output) if output and output.exists() else None}
 rows.append(row); gates()
 write(receipt,{'role':'Independent source and statement replay with explicitly verified earlier independent cache',
  'expected_frozen_hashes':EXPECTED,'reuse':reuse,'new_cache':str(CACHE),'rows':rows,
  'author_objects_used':False,'root_objects_used_for_mission_imports':False})
 print(label+': '+str(p.returncode),flush=True)
 if p.returncode: print(log.read_text(encoding='utf-8-sig'),flush=True)
 return p.returncode
if args.mode=='native':
 for name in ['CoefficientMapAggregate','CoefficientMapTelescoper']:
  if any(r['label'].startswith('native-'+name) and r['exit_code']==0 for r in rows): continue
  attempt=sum(r['label'].startswith('native-'+name) for r in rows)+1
  if run(f'native-{name}-{attempt:02}',TASK/'formalization'/f'{name}.lean',CACHE/'missions/zeta9/formalization'/f'{name}.olean'): sys.exit(1)
 attempt=len(list(OUT.glob('author-type-replay*.log')))+1
 if run(f'author-type-replay-{attempt:02}',AUTHOR/'type-audit.lean'): sys.exit(1)
else:
 attempt=sum(r['label'].startswith('independent-boundary') for r in rows)+1
 sys.exit(run(f'independent-boundary-{attempt:02}',OUT/'independent-boundary.lean'))
