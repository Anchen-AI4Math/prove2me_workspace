"""Fresh independent replay of self-contained ShiftDegree source and closed audits."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.stdout.reconfigure(encoding="utf-8")
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parents[1]
AUTHOR=TASK/"verification/formalization-coefficient-map-shift-degree-2026-10-04"
CACHE=OUT/"native/build"
CONTROL={"source":"96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953",
 "receipt":"93595416db563dd9cd8ffb5030455eed1edfe678b392ec64b1bd4930fdb7f853",
 "manifest":"8918a99aed1d1ab8d75079feaac4996f70f0e96cf66cec2dff713a0454210044",
 "SHA256SUMS":"88f22efde6ad2e4552c878e55ca09f5247f9ab4ffa567c7d5edc91036808f4c5"}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding="utf-8-sig"))
def write(p,o):p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
def frozen():
 assert sha(TASK/"formalization/CoefficientMapShiftDegree.lean")==CONTROL['source']
 assert sha(AUTHOR/"compile-receipt.json")==CONTROL['receipt']
 assert sha(AUTHOR/"source-manifest.json")==CONTROL['manifest']
 assert sha(AUTHOR/"SHA256SUMS.txt")==CONTROL['SHA256SUMS']
 files=load(AUTHOR/"source-manifest.json")['files'];assert len(files)==27
 assert all(sha(ROOT/f['root_relative'])==f['sha256'] and (ROOT/f['root_relative']).stat().st_size==f['bytes'] for f in files)
 lines=[s.split('  ',1) for s in (AUTHOR/"SHA256SUMS.txt").read_text(encoding="utf-8").splitlines() if s.strip()]
 assert len(lines)==28 and all(sha(ROOT/n)==h for h,n in lines)
frozen();rows=[]
def run(label,source,output=None):
 wrapper=OUT/(label+'.ps1')
 if output:output.parent.mkdir(parents=True,exist_ok=True)
 wrapper.write_text(f'$env:LEAN_PATH = "{CACHE.as_posix()};" + $env:LEAN_PATH + ";{ROOT.as_posix()}"\n& lean '+
  (('-o "'+output.as_posix()+'" ') if output else '')+'"'+source.as_posix()+'"\nexit $LASTEXITCODE\n',encoding='utf-8')
 cmd=['lake','env','pwsh','-NoProfile','-ExecutionPolicy','Bypass','-File',str(wrapper)]
 p=subprocess.run(cmd,cwd=ROOT,capture_output=True)
 log=OUT/(label+'.log');log.write_bytes(p.stdout+p.stderr)
 ex=OUT/(label+'-exit.txt');ex.write_text(str(p.returncode)+'\n',encoding='utf-8')
 rows.append({'label':label,'command':cmd,'working_directory':str(ROOT),'exit_code':p.returncode,
  'source_root_relative':source.relative_to(ROOT).as_posix(),'source_sha256':sha(source),
  'log':log.name,'log_sha256':sha(log),'exit_file':ex.name,'exit_file_sha256':sha(ex),
  'wrapper':wrapper.name,'wrapper_sha256':sha(wrapper),'output':output.relative_to(OUT).as_posix() if output else None,
  'output_sha256':sha(output) if output and output.exists() else None})
 write(OUT/'independent-compile-receipt.json',{'review_role':'Independent mathematical reviewer, not parent author',
  'fixed_controls':CONTROL,'rows':rows,'all_exit_codes_actually_observed':True,'source_mathlib_only':True,
  'root_scope_API_credentials_writes':False})
 print(label+': exit '+str(p.returncode),flush=True);frozen()
 assert p.returncode==0,log.read_text(encoding='utf-8-sig')
if '--boundary-only' not in sys.argv:
 run('native-ShiftDegree',TASK/'formalization/CoefficientMapShiftDegree.lean',CACHE/'missions/zeta9/formalization/CoefficientMapShiftDegree.olean')
 audit=OUT/'author-type-replay.lean';audit.write_bytes((AUTHOR/'type-audit.lean').read_bytes())
 run('author-type-replay',audit)
else:
 rows=load(OUT/'independent-compile-receipt.json')['rows'][:-1]
 assert len(rows)==2 and all(r['exit_code']==0 for r in rows)
 for r in rows:
  assert sha(ROOT/r['source_root_relative'])==r['source_sha256']
  for f in ['log','exit_file','wrapper','output']:
   if r[f]:assert sha(OUT/r[f])==r[f+'_sha256']
run('independent-boundary-audit',OUT/'independent-boundary-audit.lean')
