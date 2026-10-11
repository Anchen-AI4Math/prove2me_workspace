"""Matrix author replay in the existing verified author parent cache.

This explicitly reuses author PS parent compilation, not independent objects.
It never claims a fresh parent build; an independent fresh review is separate.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
PROJECT = TASK / '.rt/ps1'
AUTHOR = TASK / 'verification/formalization-coefficient-map-parameter-shift-2026-10-04/author-audit.json'
FROZEN = '4a8dbe4ff74047e223054a4b14ca034ca73c900513ed205dcdd8ff91bd670642'
SOURCE = TASK / 'formalization/CoefficientMapMatrix.lean'
MODULE = 'missions.zeta9.formalization.CoefficientMapMatrix'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def save(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')

def gate():
    assert sha(AUTHOR) == FROZEN
    author = json.loads(AUTHOR.read_text(encoding='utf-8'))
    assert author['verdict'] == 'PASS' and author['native_objects_borrowed'] is False
    for row in author['stable_files']:
        path = ROOT / row['root_relative']
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256']
    state = json.loads((AUTHOR.parent/'preparation-state.json').read_text(encoding='utf-8'))
    for row in state['sources']:
        path = ROOT / row['root_relative']
        copied = PROJECT / row['project_relative']
        assert copied.read_bytes() == path.read_bytes()
    assert (PROJECT/'.lake/packages').is_junction()
    assert (PROJECT/'.lake/packages').resolve() == (ROOT/'.lake/packages').resolve()

def run(command, folder, label):
    gate()
    environment = dict(os.environ)
    environment.pop('LEAN_PATH', None)
    environment.pop('LEAN_SRC_PATH', None)
    started = time.time()
    log = folder/(label+'.log')
    with log.open('w', encoding='utf-8') as stream:
        result = subprocess.run(command, cwd=PROJECT, env=environment,
            stdout=stream, stderr=subprocess.STDOUT, check=False)
    exit_path = folder/(label+'-exit.txt')
    exit_path.write_text(str(result.returncode)+'\n', encoding='utf-8')
    row = {'command': command, 'cwd': str(PROJECT), 'actual_exit': result.returncode,
           'elapsed_seconds': round(time.time()-started,3),
           'source_sha256': sha(SOURCE), 'inherited_Lean_search_paths_removed': True,
           'author_parent_cache_reused': True, 'fresh_parent_build_claimed': False,
           'independent_objects_borrowed': False, 'frozen_parent_author_sha256': FROZEN,
           'log': str(log.relative_to(OUT)), 'log_sha256': sha(log),
           'exit_file': str(exit_path.relative_to(OUT)), 'exit_sha256': sha(exit_path)}
    gate()
    print(label, 'actual exit', result.returncode, flush=True)
    return row

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('compile','source-audit','endpoint-audit'))
    parser.add_argument('--parent-lane-authorized', action='store_true', required=True)
    args = parser.parse_args()
    gate()
    counts = [int(p.name.rsplit('-',1)[1]) for p in OUT.glob(args.mode+'-[0-9][0-9]')]
    folder = OUT/(args.mode+f'-{max(counts,default=0)+1:02d}')
    folder.mkdir()
    (folder/SOURCE.name).write_bytes(SOURCE.read_bytes())
    if args.mode == 'compile':
        destination = PROJECT/'missions/zeta9/formalization'/SOURCE.name
        destination.write_bytes(SOURCE.read_bytes())
        row = run(['lake','--no-cache','build',MODULE],folder,'compile')
        if row['actual_exit'] == 0:
            obj = PROJECT/'b/lib/lean'/Path(MODULE.replace('.','/')).with_suffix('.olean')
            assert obj.exists()
            (folder/'compiled.olean').write_bytes(obj.read_bytes())
            row['retained_object_sha256'] = sha(folder/'compiled.olean')
    else:
        receipts = sorted(OUT.glob('compile-*/receipt.json'))
        assert receipts
        latest = json.loads(receipts[-1].read_text(encoding='utf-8'))
        assert latest['actual_exit'] == 0 and latest['source_sha256'] == sha(SOURCE)
        audit = OUT/('type-audit.lean' if args.mode == 'source-audit' else 'endpoint-audit.lean')
        destination = PROJECT/('MatrixSourceAudit.lean' if args.mode == 'source-audit' else 'MatrixEndpointAudit.lean')
        destination.write_bytes(audit.read_bytes())
        (folder/audit.name).write_bytes(audit.read_bytes())
        row = run(['lake','env','lean',str(destination)],folder,args.mode)
        row['audit_sha256'] = sha(audit)
    save(folder/'receipt.json',row)
    raise SystemExit(row['actual_exit'])

if __name__ == '__main__':
    main()
