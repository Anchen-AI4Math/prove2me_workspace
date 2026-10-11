"""Serial lane1 native parameter-summation AUTHOR; frozen SOURCE is immutable."""
from pathlib import Path
from types import SimpleNamespace
import argparse, hashlib, importlib.util, inspect, json, os, sys

OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/ost1'
PREP=TASK/'verification/formalization-coefficient-map-parameter-summation-preparation-2026-10-07'
ORIGINAL=TASK/'verification/formalization-coefficient-map-formal-transport-outputs-preparation-2026-10-04'
GRANT=PREP/'Root-lane1-grant-2026-10-07.json'
SOURCE=TASK/'formalization/CoefficientMapParameterSummationTransport.lean'
SOURCE_SHA='bf21501e51b31a9e9e754f8c7f22dcd734aa1435d5770838d2118bb40b662446'
NATIVE='missions.zeta9.formalization.CoefficientMapParameterSummationTransport'
PY312=Path('C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe')
BIN=Path('C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
LAKE,LEAN=BIN/'lake.exe',BIN/'lean.exe'
LEAF=OUT/'execute_leaf.py'

def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while block:=f.read(8*1024*1024):h.update(block)
 return h.hexdigest()
def load(path):return json.loads(path.read_text(encoding='utf-8-sig'))
def write(path,data):
 path.parent.mkdir(parents=True,exist_ok=True)
 path.write_bytes(data if isinstance(data,bytes) else data.encode('utf-8'))
def dump(path,doc):write(path,json.dumps(doc,ensure_ascii=False,indent=2)+'\n')
def binding(path):return dict(task_relative=path.relative_to(TASK).as_posix(),bytes=path.stat().st_size,sha256=sha(path))
def headers(raw):
 lines=raw.decode('utf-8-sig').splitlines(keepends=True)
 return [dict(name=line.split()[1],header=''.join(lines[i:]).split(':=',1)[0].rstrip())
         for i,line in enumerate(lines) if line.startswith('theorem ')]
def definition(raw):
 return raw.split(b'def transferMultiplier ',1)[1].split(b'\ntheorem ',1)[0]

def gate():
 grant=load(GRANT)
 assert grant['owner']=='outputs_author_resume_1007' and grant['private_project']=='.rt/ost1'
 assert grant['source_sha256']==SOURCE_SHA and grant['required_serial_threads']==1
 assert grant['native_SOURCE_only_no_foreign_proof_objects'] and not grant['scope_helper_or_API_writes_permitted']
 assert sha(SOURCE)==SOURCE_SHA
 inputs=load(PREP/'source-inputs.json')
 ledger=load(OUT/'private-proof-repairs.json') if (OUT/'private-proof-repairs.json').exists() else {}
 allowed={r['task_relative']:r for r in ledger.get('allowed_current_source_bindings',[])}
 actual_failed=(OUT/'compile-receipt.json').exists() and any(r['exit_code']!=0 for r in load(OUT/'compile-receipt.json')['rows'])
 for row in load(PREP/'preparation-bindings.json')['files']:
  path=TASK/row['task_relative']
  if path.is_file() and path.stat().st_size==row['bytes'] and sha(path)==row['sha256']:continue
  assert actual_failed and row['task_relative'] in allowed,'Frozen binding changed without retained actual failure'
  assert binding(path)==allowed[row['task_relative']]
  assert ledger['original_source_headers_and_definition_preserved'] and ledger['frozen_origins_snapshots_and_preparation_unchanged']
 for row in inputs['sources']:
  origin=Path(row['origin_absolute']);snapshot=TASK/row['immutable_snapshot']['task_relative']
  assert origin.stat().st_size==row['bytes'] and sha(origin)==row['sha256']
  assert snapshot.stat().st_size==row['bytes'] and sha(snapshot)==row['sha256']
  own=PROJECT/row['project_relative']
  if sha(own)!=row['sha256']:
   assert row['module']==NATIVE and actual_failed
   assert headers(own.read_bytes())==headers(snapshot.read_bytes())
   assert definition(own.read_bytes())==definition(snapshot.read_bytes())
 for row in inputs['controls']:
  immutable=TASK/row['immutable_source']['task_relative']
  assert binding(immutable)==row['immutable_source']
  own=PROJECT/row['project_relative']
  if sha(own)!=row['immutable_source']['sha256']:
   assert actual_failed and binding(own)==allowed[own.relative_to(TASK).as_posix()]
   assert headers(own.read_bytes())==headers(immutable.read_bytes())
 assert len(inputs['sources'])==22 and len(inputs['controls'])==5
 assert headers(SOURCE.read_bytes())==load(PREP/'static-original-header-inventory.json')['records']
 assert next(r for r in inputs['sources'] if r['module'].endswith('.CoefficientMapFormalTransportOutputs'))['sha256']=='8b2fc477c10a698f9b5bef004531861c392d93da0377a2874965c8ce470d2fa6'
 assert next(r for r in inputs['sources'] if r['module'].endswith('.CoefficientMapFormalTransportJets'))['sha256']=='ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02'
 return inputs

def initial_preflight():
 inputs=gate();checks=[]
 for row in load(PREP/'preparation-bindings.json')['files']:
  path=TASK/row['task_relative'];assert binding(path)==row
  checks.append(row)
 assert len(checks)==66
 sums=[]
 for line in (PREP/'PREPARATION_SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
  expected,relative=line.split(maxsplit=1);path=TASK/relative.lstrip('*')
  assert sha(path)==expected;sums.append(dict(task_relative=relative,sha256=expected))
 assert len(sums)==66
 assert not (PROJECT/'b').exists() and not (PROJECT/'.lake').exists()
 assert not list(PROJECT.rglob('*.olean*'))
 dump(OUT/'initial-runtime-preflight.json',dict(role='PERSONAL PURE REHASH BEFORE ACTUAL AUTHOR LEAN',
  original_66_bindings=checks,original_66_sums=sums,source_origins=[dict(path=r['origin_absolute'],sha256=r['sha256']) for r in inputs['sources']],
  grant=binding(GRANT),no_own_cache=True,no_package_link=True,no_foreign_objects=True,Lean_calls=0))

def recorder():
 assert sha(ORIGINAL/'execute.py')=='7b17f375c271030e3b994340b58e1fb315b151cf9e316f0cef34e84f6e891067'
 p=SimpleNamespace(OUT=OUT,TASK=TASK,ROOT=ROOT,PROJECT=PROJECT,SOURCE_SHA=SOURCE_SHA,
                   sha=sha,load=load,write=write,dump=dump,binding=binding)
 sys.modules['prepare']=p;sys.path.insert(0,str(ORIGINAL))
 spec=importlib.util.spec_from_file_location('parameter_source_recorder',ORIGINAL/'execute.py')
 mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 original=inspect.getsource(mod.run)
 derived=original.replace("['lakefile.lean', 'lean-toolchain',\n                                                       'lake-manifest.json', 'lean_call.py']","['lakefile.toml', 'lean-toolchain', 'lake-manifest.json']")
 old="command = ['lake','env','python','lean_call.py','lean']+list(arguments)"
 assert derived.count(old)==1
 derived=derived.replace(old,"command = [str(LAKE),'env',str(PY312),str(LEAF),str(LEAN),'-j1']+list(arguments)")
 marker='    for argument in arguments:\n';assert derived.count(marker)==1
 derived=derived.replace(marker,"    inputs.extend([p.binding(Path(__file__)),p.binding(LEAF),p.binding(ORIGINAL/'execute.py'),p.binding(ORIGINAL/'retain_actual_inputs.py'),p.binding(GRANT),p.binding(PREP/'source-inputs.json')])\n"+marker)
 derived=derived.replace("role='Outputs native author, fresh source-only compilation; independent review required'","role='Parameter summation native AUTHOR, fresh own SOURCE compilation; independent review required'")
 derived=derived.replace("    environment.pop('LEAN_PATH', None); environment.pop('LEAN_SRC_PATH', None)","    environment.pop('LEAN_PATH', None); environment.pop('LEAN_SRC_PATH', None)\n    environment['LEAN_NUM_THREADS']='1';environment['LAKE_JOBS']='1'")
 path=OUT/'derived_run_source.py'
 if path.exists():assert path.read_text(encoding='utf-8')==derived
 else:write(path,derived)
 mod.__file__=str(Path(__file__));mod.gate=gate
 mod.ORIGINAL=ORIGINAL;mod.GRANT=GRANT;mod.PREP=PREP
 mod.LAKE=LAKE;mod.LEAN=LEAN;mod.PY312=PY312;mod.LEAF=LEAF
 exec(compile(derived,str(path),'exec'),mod.__dict__)
 return mod

def make_resolver(state):
 modules=[r['module'] for r in state['sources']+state['controls']]
 code='import Lean\nopen Lean\nrun_meta do\n  initSearchPath (← findSysroot)\n'
 code+='  for name in ['+', '.join('`'+n for n in modules)+'] do\n'
 code+='    let path ← findOLean name\n    IO.println (Json.mkObj [("module",Json.str name.toString),("olean",Json.str path.toString)]).compress\n'
 target=PROJECT/'resolver.lean'
 if target.exists():assert target.read_text(encoding='utf-8')==code
 else:write(target,code)
 return modules

def main():
 sys.stdout.reconfigure(encoding='utf-8')
 ap=argparse.ArgumentParser();ap.add_argument('--lane-granted',action='store_true',required=True);ap.parse_args()
 assert Path(sys.executable).resolve()==PY312.resolve()
 for path in [LAKE,LEAN,PY312,LEAF]:assert path.is_file()
 if not (OUT/'compile-receipt.json').exists():initial_preflight()
 state=gate();modules=make_resolver(state);mod=recorder()
 if not (OUT/'executor-provenance.json').exists():dump(OUT/'executor-provenance.json',dict(
  role='native parameter summation AUTHOR derivative',original_executor=binding(ORIGINAL/'execute.py'),
  actual_executor=binding(Path(__file__)),derived_run_source=binding(OUT/'derived_run_source.py'),actual_leaf=binding(LEAF),
  actual_PY312=str(PY312),actual_LAKE=str(LAKE),actual_LEAN=str(LEAN),grant=binding(GRANT),
  SOURCE_only=True,borrowed_objects=False,serial=True,Lean_threads=1,LEAN_NUM_THREADS='1',LAKE_JOBS='1',planned_calls=29))
 mod.configure_packages();mod.run('toolchain',['--version'])
 for r in state['sources']:
  obj='b/lib/lean/'+r['module'].replace('.','/')+'.olean';(PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
  mod.run('source-'+r['module'].rsplit('.',1)[1],['-o',obj,r['project_relative']])
 for r in state['controls']:
  mod.run('control-'+r['module'],['-o','b/lib/lean/'+r['module']+'.olean',r['project_relative']])
 mod.run('own-object-resolution',['resolver.lean'])
 receipt=load(OUT/'compile-receipt.json');latest={r['label']:r for r in receipt['rows']}
 assert len(latest)==29 and all(r['exit_code']==0 for r in latest.values())
 resolved=[]
 for row in mod.rows(OUT/'own-object-resolution.log'):
  raw=Path(row['olean']);absolute=raw.resolve() if raw.is_absolute() else (PROJECT/raw).resolve()
  expected=(PROJECT/'b/lib/lean'/(row['module'].replace('.','/')+'.olean')).resolve()
  assert absolute==expected
  resolved.append(dict(**row,actual_execution_cwd=str(PROJECT),resolved_absolute=str(absolute),own_object_resolution_passed=True))
 assert len(resolved)==27
 dump(OUT/'actual-own-object-resolution.json',resolved)
 dump(OUT/'terminal-runtime-state.json',dict(actual_rows=len(receipt['rows']),actual_successes=sum(r['exit_code']==0 for r in receipt['rows']),
  actual_failures=sum(r['exit_code']!=0 for r in receipt['rows']),planned_final_success_calls=29,own_object_resolutions=27,
  author_freeze_still_required=True,independent_review_still_required=True))
 print('All 29 planned author calls terminal; freeze and additional whole-function rfl still required.',flush=True)

if __name__=='__main__':main()
