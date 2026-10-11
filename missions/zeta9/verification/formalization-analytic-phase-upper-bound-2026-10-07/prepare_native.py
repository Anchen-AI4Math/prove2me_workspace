"""Fresh private native project preparation; no Lean, network or foreign objects."""
from pathlib import Path
import hashlib, json, sys
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/aph1'
PYTHON='C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'
REV='0df444a360eaa60ab8c11dca51a86af692955474'
EXPECTED={'AnalyticPhase':'475f95ba7e9c977a78b6efa8e0f1599d2ec32fcc20e46bfb1bfb3b5e309ea38c',
          'AnalyticPhaseUpperBound':'9e0ed4cb7757b17af9a64b69927a3fa47c440d1828f239be50e473ab24a21c16'}
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path):return json.loads(path.read_text(encoding='utf-8-sig'))
def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(value if isinstance(value,bytes) else value.encode('utf-8'))
def dump(path,value):write(path,json.dumps(value,ensure_ascii=False,indent=2)+'\n')
def binding(path):return dict(task_relative=path.relative_to(TASK).as_posix(),bytes=path.stat().st_size,sha256=sha(path))
def main():
    assert not PROJECT.exists(),'Fresh source-only project required'
    PROJECT.mkdir(parents=True)
    original=[]
    for module,expected in EXPECTED.items():
        path=TASK/'formalization'/(module+'.lean')
        assert sha(path)==expected
        destination=PROJECT/'missions/zeta9/formalization'/(module+'.lean')
        write(destination,path.read_bytes())
        original.append(dict(module='missions.zeta9.formalization.'+module,shared_source=binding(path),private_source=binding(destination)))
    write(PROJECT/'lean-toolchain',(ROOT/'lean-toolchain').read_bytes())
    write(PROJECT/'lake-manifest.json',(TASK/'.rt/pa1/lake-manifest.json').read_bytes())
    write(PROJECT/'lakefile.lean',f'''import Lake
open Lake DSL
package zeta9ActualPhaseNativeAuthor where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{REV}"
lean_lib ActualPhase where
  roots := #[`missions.zeta9.formalization.AnalyticPhaseUpperBound]
  globs := #[.one `missions.zeta9.formalization.AnalyticPhase, .one `missions.zeta9.formalization.AnalyticPhaseUpperBound]
''')
    write(PROJECT/'leaf.py',r'''from pathlib import Path
import json, os, subprocess, sys
PROJECT=Path(__file__).resolve().parent
PACKAGES=Path(r"D:\users\self_projects\prove2me_workspace\.lake\packages").resolve()
env=dict(os.environ)
selected={}
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    original=[raw for raw in env.get(key,'').split(os.pathsep) if raw]
    allowed=[]
    for raw in original:
        resolved=(PROJECT/Path(raw)).resolve()
        if resolved.is_relative_to(PROJECT.resolve()) or resolved.is_relative_to(PACKAGES):
            allowed.append(str(resolved))
    own=str(PROJECT/'b/lib/lean') if key=='LEAN_PATH' else str(PROJECT)
    if own not in allowed:allowed.insert(0,own)
    env[key]=os.pathsep.join(allowed)
    selected[key]=dict(original=original,filtered=allowed)
selected['actual_environment']={key:env.get(key) for key in ['LEAN_NUM_THREADS','LAKE_JOBS']}
Path(env['ACTUAL_PHASE_PATH_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
result=subprocess.run(sys.argv[1:],env=env)
sys.exit(result.returncode)
''')
    dump(OUT/'lane1-grant-2026-10-07.json',dict(lane=1,maximum_global_Lean_lanes=2,Root_explicit_grant=True,
      grant_message='Root formally grants lane1 for Phase native author compilation; Outputs lane1 is terminal. Fresh .rt/aph1 copies only the original15 and new19 true sources, fixed Mathlibpackages, no Root/other agent proof objects. Python312 explicit, require_escalated, Lean-j1 serial; source first, all34 full types/kernel/Std3/fullvalues/boundaries and failure receipts. No API. Phase PASS does not establish full moments/uniform Z9.A.'))
    dump(OUT/'preparation-state.json',dict(role='native Phase AUTHOR',fresh_project_task_relative='.rt/aph1',
      project_initially_absent=True,proof_objects_copied=False,Root_or_foreign_proof_fallback=False,
      original_sources=original,Mathlib_revision=REV,Lean_executed=False,
      configs=[binding(PROJECT/n) for n in ['lakefile.lean','lake-manifest.json','lean-toolchain','leaf.py']]))
    print('Fresh aph1 source-only project prepared; no Lean execution.',flush=True)
if __name__=='__main__':main()
