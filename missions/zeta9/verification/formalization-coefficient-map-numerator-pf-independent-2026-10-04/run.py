"""Future serial fresh native NumeratorPF audit. No import-time execution.

Every actual Lean/Lake/compiler action requires the parent's explicit lane grant
to have been recorded in lane-grant.json. Pure preparation has no such grant.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

sys.stdout.reconfigure(encoding='utf-8')
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parent.parent
PROJECT = TASK / '.rt/pfi'
CACHE = PROJECT / 'b/lib/lean'
PREP_SHA = '94055899ce98fd780c118354986706bcc260f37a6c8c9d82387e968c9e7c47c2'
AUTHOR = TASK / 'verification/formalization-coefficient-map-numerator-pf-2026-10-04'
AUTHOR_SHA = '7285317314696ed866c4b9333e6b0b9fdc01df1813048192aad1ecfabb24f2a5'
PROGRAMS = ['source_audit.lean', 'expected_types_prepared.lean', 'whole_values.lean',
            'own_boundaries_prepared.lean', 'author_types_replay.lean',
            'author_values_replay.lean', 'author_boundaries_replay.lean', 'actual_resolver.lean']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def write(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content if isinstance(content, bytes) else content.encode('utf-8'))

def dump(path, value):
    write(path, json.dumps(value, ensure_ascii=False, indent=2) + '\n')

def check_records(records):
    for item in records:
        path = ROOT / item['root_relative']
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], str(path)

def verify():
    assert sha(OUT / 'preparation-freeze.json') == PREP_SHA
    prep = load(OUT / 'preparation-freeze.json')
    assert prep['Lean_Lake_compiler_invocations'] == 0 and prep['verdict'] is None
    assert sha(AUTHOR / 'author-audit.json') == AUTHOR_SHA
    author = load(AUTHOR / 'author-audit.json')
    assert author['verdict'] == 'PASS' and len(author['stable_files']) == 188
    check_records(author['stable_files'])
    check_records(prep['stable_files'])
    for item in prep['fresh_full_source_build_order']:
        assert (ROOT / item['root_relative']).read_bytes() == (PROJECT / item['project_relative']).read_bytes()
    assert (PROJECT / 'lean-toolchain').read_bytes() == (ROOT / 'lean-toolchain').read_bytes()
    assert (PROJECT / 'lake-manifest.json').read_bytes() == (ROOT / 'lake-manifest.json').read_bytes()
    return prep

def lane_grant():
    grant = load(OUT / 'lane-grant.json')
    assert grant['explicit_parent_Lean_lane_granted'] is True
    assert grant['lane'] in [1, 2] and grant['maximum_global_Lean_lanes'] == 2
    assert grant['preparation_sha256'] == PREP_SHA and grant['parent_message_verbatim']
    return grant

def configure(grant):
    verify()
    packages = PROJECT / '.lake/packages'
    if not packages.exists():
        assert not (PROJECT / 'b').exists() and not (PROJECT / '.lake/build').exists()
        assert not list(PROJECT.rglob('*.olean'))
        packages.parent.mkdir(parents=True, exist_ok=True)
        # Native PowerShell filesystem operation only; no deletion or shell mixing.
        result = subprocess.run(['pwsh', '-NoProfile', '-Command',
          'New-Item -ItemType Junction -Path "' + str(packages) +
          '" -Target "' + str(ROOT / '.lake/packages') + '" | Out-Null'], capture_output=True)
        write(OUT / 'package-junction.log', result.stdout + result.stderr)
        write(OUT / 'package-junction-exit.txt', str(result.returncode) + '\n')
        assert result.returncode == 0
    assert packages.is_junction() and packages.resolve() == (ROOT / '.lake/packages').resolve()
    names = [x['name'] for x in load(PROJECT / 'lake-manifest.json')['packages']]
    package_paths = [(ROOT / '.lake/packages' / name / '.lake/build/lib/lean').resolve() for name in names]
    assert all(path.is_dir() for path in package_paths)
    allowed = {'olean_paths': [str(CACHE.resolve())] + [str(p) for p in package_paths],
               'source_paths': [str(PROJECT.resolve())] +
                 [str((ROOT / '.lake/packages' / n).resolve()) for n in names]}
    write(PROJECT / 'allowed-paths.json', json.dumps(allowed, indent=2) + '\n')
    # The post-Lake helper permits exact enrolled paths, never a broad ancestor.
    wrapper = '''from pathlib import Path
import json,os,subprocess,sys
project=Path(__file__).resolve().parent
allowed=json.loads((project/'allowed-paths.json').read_text(encoding='utf8'))
env=dict(os.environ); selected={}
for key,allow_key in [('LEAN_PATH','olean_paths'),('LEAN_SRC_PATH','source_paths')]:
    raw=[s for s in env.get(key,'').split(os.pathsep) if s]
    allowed_set={str(Path(s).resolve()).casefold() for s in allowed[allow_key]}
    kept=[s for s in raw if str(Path(s).resolve()).casefold() in allowed_set]
    own=allowed[allow_key][0]
    if str(Path(own).resolve()).casefold() not in {str(Path(s).resolve()).casefold() for s in kept}:
        kept.append(own)
    env[key]=os.pathsep.join(kept)
    selected[key]={'original_Lake_paths':raw,'filtered_exact_allowed_paths':kept,'allowed_exact_set':allowed[allow_key]}
Path(env['NUMERATOR_PF_ENV_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\\n',encoding='utf8')
result=subprocess.run(sys.argv[1:],env=env)
sys.exit(result.returncode)
'''
    write(PROJECT / 'filtered_lean.py', wrapper)
    if not (OUT / 'actual-execution-receipt.json').exists():
        assert not (PROJECT / 'b').exists() and not (PROJECT / '.lake/build').exists()
        dump(OUT / 'actual-execution-receipt.json',
             {'status': 'IN_PROGRESS', 'empty_own_cache_before_first_Lean_call': True,
              'no_author_Root_old_independent_objects_borrowed': True,
              'lane_grant': grant, 'rows': []})

def run(logical, args, source=None, output=None, resume=False):
    verify()
    grant = lane_grant()
    receipt = load(OUT / 'actual-execution-receipt.json')
    previous = [row for row in receipt['rows'] if row['logical_step'] == logical]
    if previous:
        assert resume and len(previous) == 1 and previous[0]['actual_exit'] == 0
        row = previous[0]
        for key in ['log', 'exit_file', 'environment_receipt']:
            assert sha(OUT / row[key]) == row[key + '_sha256']
        if source:
            assert sha(source) == row['source_sha256']
        if output:
            assert sha(output) == row['object_sha256']
        print(logical + ': own successful actual execution verified; no rerun', flush=True)
        return row
    label = 'e' + str(len(receipt['rows']) + 1).zfill(2)
    log = OUT / (label + '.log')
    exitfile = OUT / (label + '-exit.txt')
    pathsreceipt = OUT / (label + '-paths.json')
    snapshot = OUT / (label + '-source.lean') if source else None
    if source:
        write(snapshot, source.read_bytes())
    if output:
        assert not output.exists(), 'Cannot replace an already frozen/successful object'
        output.parent.mkdir(parents=True, exist_ok=True)
    assert all(len(str(p)) + 64 <= 259 for p in [log, exitfile, pathsreceipt] + ([output] if output else []))
    environment = dict(os.environ)
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH']:
        environment.pop(key, None)
    environment.update(LEAN_NUM_THREADS='1', LAKE_JOBS='1', NUMERATOR_PF_ENV_RECEIPT=str(pathsreceipt))
    command = ['lake', 'env', sys.executable, str(PROJECT / 'filtered_lean.py'), 'lean'] + args
    start = time.monotonic()
    with log.open('wb') as stream:
        result = subprocess.run(command, cwd=PROJECT, env=environment, stdout=stream, stderr=subprocess.STDOUT)
    write(exitfile, str(result.returncode) + '\n')
    row = {'label': label, 'logical_step': logical, 'command': command,
           'cwd': str(PROJECT), 'actual_exit': result.returncode,
           'elapsed_seconds': round(time.monotonic() - start, 3),
           'serial_lane': grant['lane'], 'Lean_num_threads': 1,
           'log': log.name, 'log_sha256': sha(log),
           'exit_file': exitfile.name, 'exit_file_sha256': sha(exitfile),
           'environment_receipt': pathsreceipt.name,
           'environment_receipt_sha256': sha(pathsreceipt) if pathsreceipt.exists() else None,
           'source_task_relative': source.relative_to(TASK).as_posix() if source else None,
           'source_sha256': sha(source) if source else None,
           'source_snapshot': snapshot.name if snapshot else None,
           'source_snapshot_sha256': sha(snapshot) if snapshot else None,
           'object_task_relative': output.relative_to(TASK).as_posix() if output and output.exists() else None,
           'object_sha256': sha(output) if output and output.exists() else None,
           'inherited_Lean_paths_removed_before_Lake': True,
           'post_Lake_exact_allowed_path_filter': True,
           'whole_failed_run_excluded_from_success_evidence': result.returncode != 0}
    receipt['rows'].append(row)
    dump(OUT / 'actual-execution-receipt.json', receipt)
    print(logical + ': actual exit ' + str(result.returncode), flush=True)
    verify()
    if result.returncode != 0:
        raise SystemExit(result.returncode)
    return row

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=['source', 'controls'])
    parser.add_argument('--parent-lane-authorized', required=True, action='store_true')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    prep = verify()
    configure(lane_grant())
    if args.phase == 'source':
        for item in prep['fresh_full_source_build_order']:
            source = PROJECT / item['project_relative']
            output = CACHE / Path(item['module'].replace('.', '/')).with_suffix('.olean')
            run('fresh complete source ' + item['module'], ['-o', str(output), str(source)],
                source, output, args.resume)
        receipt = load(OUT / 'actual-execution-receipt.json')
        receipt['source_phase_complete'] = True
        dump(OUT / 'actual-execution-receipt.json', receipt)
    else:
        receipt = load(OUT / 'actual-execution-receipt.json')
        assert receipt['source_phase_complete'] and all(row['actual_exit'] == 0 for row in receipt['rows'])
        run('actual pinned runtime', ['--version'], resume=args.resume)
        for name in ['IndependentValues', 'ValueAliases']:
            source = PROJECT / (name + '.lean')
            run('fresh source-only definition alias ' + name,
                ['-o', str(CACHE / (name + '.olean')), str(source)], source,
                CACHE / (name + '.olean'), args.resume)
        for name in PROGRAMS:
            source = OUT / name
            run('actual independent control ' + name, [str(source)], source, resume=args.resume)
        receipt = load(OUT / 'actual-execution-receipt.json')
        receipt['controls_phase_complete'] = True
        receipt['status'] = 'ALL_REQUESTED_EXECUTIONS_FINISHED'
        dump(OUT / 'actual-execution-receipt.json', receipt)

if __name__ == '__main__':
    main()
