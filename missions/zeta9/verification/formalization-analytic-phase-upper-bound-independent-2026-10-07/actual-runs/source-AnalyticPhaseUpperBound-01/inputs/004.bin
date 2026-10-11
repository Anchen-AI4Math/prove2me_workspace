"""Root-granted native executions, serial and resumable with lossless receipts."""
from pathlib import Path
import argparse, os, subprocess, sys, time
sys.dont_write_bytecode = True
import prepare_independent as p

PREPARATION_SHA = 'a56d7e71bb4d0372116eeea4de707e6b853b3420f90a51223c934d3c12174bf1'

def check(b):
 path = p.TASK / b['task_relative']
 assert path.stat().st_size == b['bytes'] and p.sha(path) == b['sha256'], str(path)
 return path

def gate():
 grant = p.OUT / 'Root-lean-lane-grant.json'
 assert grant.is_file(), 'No independent Lean call without a separate explicit Root lane grant'
 g = p.load(grant)
 assert g['Root_explicit_grant'] is True and g['maximum_global_Lean_lanes'] == 2
 assert g['role'] == 'phase_independent_1007' and g['lane'] in [1, 2]
 assert p.sha(p.OUT / 'preparation-state.json') == PREPARATION_SHA
 state = p.load(p.OUT / 'preparation-state.json')
 for b in state['configs']: check(b)
 for row in state['source_contracts']:
  for k in ['shared_source', 'frozen_author_export', 'independent_fresh_source']: check(row[k])
 assert p.sha(p.AUTHOR / 'author-audit.json') == p.AUTHOR_SHA
 junction = p.PROJECT / '.lake/packages'
 assert junction.is_junction() and junction.resolve() == (p.ROOT / '.lake/packages').resolve()
 return g

def module_inputs(module):
 result = []
 names = []
 if module == 'missions.zeta9.formalization.AnalyticPhaseUpperBound':
  names = ['AnalyticPhase']
 elif module.startswith('APIPhase'):
  names = ['AnalyticPhase', 'AnalyticPhaseUpperBound']
 for name in names:
  rel = 'missions/zeta9/formalization/' + name
  result.append(p.binding(p.PROJECT / (rel + '.lean')))
  obj = p.PROJECT / ('b/lib/lean/' + rel + '.olean')
  assert obj.exists(), 'Require own prior actual SOURCE success before dependency controls'
  receipt = p.load(p.OUT / 'compile-receipt.json')
  label = 'source-' + name
  preceding = next((r for r in reversed(receipt['rows']) if r['label'] == label and r['exit_code'] == 0), None)
  assert preceding, 'An object without its own actual SOURCE receipt cannot be reused'
  for b in preceding['output_bindings']: check(b)
  result += [p.binding(x) for x in sorted(obj.parent.glob(obj.name + '*')) if x.is_file()]
 return result

def run(label, arguments, module=None):
 grant = gate()
 receipt_path = p.OUT / 'compile-receipt.json'
 receipt = p.load(receipt_path) if receipt_path.exists() else dict(
  role='independent native actual phase', project='.rt/api1', initially_fresh=True,
  foreign_proof_objects_borrowed=False, Root_proof_fallback=False, rows=[])
 inputs = [p.binding(p.PROJECT / n) for n in ['lakefile.lean','lake-manifest.json','lean-toolchain','leaf.py']]
 inputs += [p.binding(Path(__file__)), p.binding(p.OUT / 'prepare_independent.py'),
            p.binding(p.OUT / 'Root-lean-lane-grant.json'), p.binding(p.OUT / 'preparation-state.json')]
 if module: inputs += module_inputs(module)
 actual = []
 for argument in arguments:
  if str(argument).endswith(('.lean', '.olean')):
   path = p.PROJECT / argument
   actual.append(str(path))
   if str(argument).endswith('.lean'): inputs.append(p.binding(path))
  else: actual.append(argument)
 old = next((r for r in reversed(receipt['rows']) if r['label'] == label and
             r['exit_code'] == 0 and r['input_bindings'] == inputs), None)
 if old:
  for b in old['output_bindings'] + [old[k] for k in ['stdout','stderr','log','exit_file','selected_paths']]: check(b)
  print(label + ': retained same-audit actual success, not rerun', flush=True)
  return
 attempt = 1 + sum(r['label'] == label for r in receipt['rows'])
 folder = p.OUT / 'actual-runs' / (label + '-' + str(attempt).zfill(2))
 folder.mkdir(parents=True, exist_ok=False)
 snapshots = []
 for i, b in enumerate(inputs):
  dst = folder / 'inputs' / (str(i).zfill(3) + '.bin')
  p.write(dst, check(b).read_bytes())
  snapshots.append(dict(original_binding=b, snapshot_binding=p.binding(dst)))
 env = dict(os.environ)
 for key in ['LEAN_PATH', 'LEAN_SRC_PATH']: env.pop(key, None)
 env['LEAN_NUM_THREADS'] = '1'; env['LAKE_JOBS'] = '1'
 env['PHASE_INDEPENDENT_PATH_RECEIPT'] = str(folder / 'selected-paths.json')
 command = ['lake','env',p.PYTHON,str(p.PROJECT / 'leaf.py'),'lean','-j1','--root=' + str(p.PROJECT)] + actual
 started = time.monotonic()
 result = subprocess.run(command, cwd=p.PROJECT, env=env, capture_output=True)
 for name, data in [('stdout.log',result.stdout),('stderr.log',result.stderr),
                    ('combined.log',result.stdout + result.stderr),('exit.txt',str(result.returncode) + '\n')]:
  p.write(folder / name, data)
 outputs = []
 if '-o' in arguments:
  obj = p.PROJECT / arguments[arguments.index('-o') + 1]
  if obj.exists(): outputs = [x for x in sorted(obj.parent.glob(obj.name + '*')) if x.is_file()]
 kept = []
 for i, path in enumerate(outputs):
  dst = folder / 'outputs' / (str(i).zfill(3) + '.bin')
  p.write(dst, path.read_bytes())
  kept.append(dict(original_binding=p.binding(path), snapshot_binding=p.binding(dst)))
 paths = folder / 'selected-paths.json'
 row = dict(label=label, attempt=attempt, module=module, command=command, cwd=str(p.PROJECT),
  actual_environment={k:env[k] for k in ['LEAN_NUM_THREADS','LAKE_JOBS']}, Root_granted_lane=grant['lane'],
  elapsed_seconds=round(time.monotonic() - started, 3), exit_code=result.returncode,
  input_bindings=inputs, retained_inputs=snapshots, output_bindings=[p.binding(x) for x in outputs],
  retained_outputs=kept, stdout=p.binding(folder / 'stdout.log'), stderr=p.binding(folder / 'stderr.log'),
  log=p.binding(folder / 'combined.log'), exit_file=p.binding(folder / 'exit.txt'),
  selected_paths=p.binding(paths) if paths.exists() else None,
  failed_attempt_retained=result.returncode != 0)
 receipt['rows'].append(row); p.dump(receipt_path, receipt)
 print(label + ': actual exit ' + str(result.returncode) + ', seconds ' + str(row['elapsed_seconds']), flush=True)
 if result.returncode:
  print('\n'.join(x for x in (result.stdout + result.stderr).decode('utf-8',errors='replace').splitlines()
                  if not x.startswith('PHI_RECORD|')), flush=True)
 assert result.returncode == 0, 'Actual failed attempt retained completely; no PASS'
 actual_paths = p.load(paths)
 for key in ['LEAN_PATH', 'LEAN_SRC_PATH']:
  assert all(Path(raw).is_absolute() and (Path(raw).resolve().is_relative_to(p.PROJECT.resolve()) or
             Path(raw).resolve().is_relative_to((p.ROOT / '.lake/packages').resolve()))
             for raw in actual_paths[key]['filtered'])
 gate()

def compile_module(label, module):
 obj = 'b/lib/lean/' + module.replace('.', '/') + '.olean'
 (p.PROJECT / obj).parent.mkdir(parents=True, exist_ok=True)
 run(label, ['-o', obj, module.replace('.', '/') + '.lean'], module)

def main():
 sys.stdout.reconfigure(encoding='utf-8')
 q = argparse.ArgumentParser()
 q.add_argument('--lane-granted', action='store_true', required=True)
 q.add_argument('--phase', choices=['source','types','kernel','boundary','resolver','all'], default='all')
 a = q.parse_args()
 if a.phase in ['source','all']:
  run('runtime-version',['--version'])
  for name in p.EXPECTED: compile_module('source-' + name, 'missions.zeta9.formalization.' + name)
 for phase, module in [('types','APIPhaseTypes'),('kernel','APIPhaseKernel'),
                       ('boundary','APIPhaseBoundary'),('resolver','APIPhaseResolver')]:
  if a.phase in [phase,'all']: compile_module('control-' + phase, module)

if __name__ == '__main__': main()
