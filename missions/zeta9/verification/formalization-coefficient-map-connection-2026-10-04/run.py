from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent
TASK=OUT.parent.parent
ROOT=TASK.parent.parent
P=OUT/'p'
SOURCE=TASK/'formalization/CoefficientMapConnection.lean'
MODULE='missions.zeta9.formalization.CoefficientMapConnection'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes(b if isinstance(b,bytes) else b.encode('utf-8'))
if not P.exists():
 write(P/'lakefile.lean','''import Lake
open Lake DSL
package zeta9Connection where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapConnection]
  globs := #[.one `missions.zeta9.formalization.CoefficientMapConnection]
''')
 for n in ['lean-toolchain','lake-manifest.json']:write(P/n,(ROOT/n).read_bytes())
 (P/'.lake').mkdir(exist_ok=True)
 rr=subprocess.run(['cmd','/c','mklink','/J',str(P/'.lake/packages'),str(ROOT/'.lake/packages')],capture_output=True)
 assert rr.returncode==0
receipt=OUT/'compile-receipt.json'
r=json.loads(receipt.read_text()) if receipt.exists() else {'only_Mathlib_package_cache_shared':True,'native_objects_borrowed':False,'rows':[],'complete':False}
i=len(r['rows'])+1
A=OUT/f'attempt-{i:02}'
write(A/'CoefficientMapConnection.lean',SOURCE.read_bytes())
write(P/(MODULE.replace('.','/')+'.lean'),SOURCE.read_bytes())
cmd=['lake','--no-cache','build',MODULE]
env=os.environ.copy();env.pop('LEAN_PATH',None);env['LEAN_NUM_THREADS']='1'
rr=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
write(A/'compile.log',rr.stdout+rr.stderr);write(A/'exit.txt',str(rr.returncode)+'\n')
assert SOURCE.read_bytes()==(A/'CoefficientMapConnection.lean').read_bytes(), 'Do not mutate source during an actual compile.'
row={'attempt':i,'command':cmd,'exit_code':rr.returncode,'source_sha256':sha(A/'CoefficientMapConnection.lean'),'source':str((A/'CoefficientMapConnection.lean').relative_to(OUT)),'log':str((A/'compile.log').relative_to(OUT)),'log_sha256':sha(A/'compile.log'),'exit_file':str((A/'exit.txt').relative_to(OUT)),'exit_sha256':sha(A/'exit.txt')}
obj=P/'b/lib/lean'/(MODULE.replace('.','/')+'.olean')
if rr.returncode==0:
 write(A/'compiled.olean',obj.read_bytes())
 row.update({'object':str(obj.relative_to(OUT)),'object_sha256':sha(obj),'retained_object':str((A/'compiled.olean').relative_to(OUT)),'retained_object_sha256':sha(A/'compiled.olean')})
r['rows'].append(row);r['complete']=rr.returncode==0
write(receipt,json.dumps(r,indent=2)+'\n')
print(f'Attempt {i}: actual exit {rr.returncode}',flush=True)
print((rr.stdout+rr.stderr).decode('utf-8',errors='replace'),flush=True)
sys.exit(rr.returncode)
