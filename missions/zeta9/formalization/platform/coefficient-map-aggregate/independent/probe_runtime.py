"""One observed runtime version probe; no proof cache is accessed."""
from pathlib import Path
import hashlib,json,subprocess
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[3];ROOT=TASK.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=subprocess.run(['lake','env','lean','--version'],cwd=ROOT,capture_output=True)
(OUT/'actual-toolchain.log').write_bytes(p.stdout+p.stderr)
(OUT/'actual-toolchain-exit.txt').write_bytes((str(p.returncode)+'\n').encode())
assert p.returncode==0 and b'4.33.1' in p.stdout
manifest=json.loads((ROOT/'lake-manifest.json').read_text(encoding='utf-8-sig'))
mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
data={'lean_toolchain':(ROOT/'lean-toolchain').read_text().strip(),'lean_runtime_stdout':p.stdout.decode(),
 'actual_runtime_exit_code':p.returncode,'mathlib_manifest_revision':mathlib['rev'],
 'root_lake_manifest_sha256':sha(ROOT/'lake-manifest.json'),'root_toolchain_sha256':sha(ROOT/'lean-toolchain')}
(OUT/'actual-environment.json').write_bytes((json.dumps(data,indent=2)+'\n').encode())
print('Actual runtime version probe: exit 0')
