"""Run one serial native author lane after orchestration explicitly releases it."""
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
SOURCE = TASK / 'formalization/CoefficientMapParameterShift.lean'
MODULE = 'missions.zeta9.formalization.CoefficientMapParameterShift'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def record(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def run(command, folder, label):
    started = time.time()
    log = folder / (label + '.log')
    with log.open('w', encoding='utf-8') as stream:
        environment = dict(os.environ)
        environment.pop('LEAN_PATH', None)
        environment.pop('LEAN_SRC_PATH', None)
        result = subprocess.run(command, cwd=PROJECT, env=environment,
                                stdout=stream, stderr=subprocess.STDOUT, check=False)
    exit_path = folder / (label + '-exit.txt')
    exit_path.write_text(str(result.returncode) + '\n', encoding='utf-8')
    row = {'command': command, 'cwd': str(PROJECT), 'actual_exit': result.returncode,
           'inherited_Lean_search_paths_removed': True,
           'elapsed_seconds': round(time.time() - started, 3),
           'log': str(log.relative_to(OUT)), 'log_sha256': digest(log),
           'exit_file': str(exit_path.relative_to(OUT)), 'exit_sha256': digest(exit_path)}
    print(label + ': actual exit ' + str(result.returncode), flush=True)
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('first', 'retry', 'audit'))
    parser.add_argument('--lane-released', action='store_true', required=True)
    args = parser.parse_args()
    state = json.loads((OUT / 'preparation-state.json').read_text(encoding='utf-8'))
    for row in state['sources']:
        if row['root_relative'].endswith('/CoefficientMapParameterShift.lean'):
            continue
        original = ROOT / row['root_relative']
        copy = PROJECT / row['project_relative']
        assert digest(original) == digest(copy) == row['sha256']
        assert original.stat().st_size == copy.stat().st_size == row['bytes']
    packages = PROJECT / '.lake/packages'
    assert packages.is_junction() and packages.resolve() == (ROOT / '.lake/packages').resolve()
    first_log = OUT / 'first-build-receipt.json'
    if args.mode == 'first':
        assert not first_log.exists() and not (PROJECT / 'b').exists(), 'Never reset or borrow a cache.'
        assert digest(SOURCE) == state['candidate_sha256']
        assert (PROJECT / 'missions/zeta9/formalization' / SOURCE.name).read_bytes() == SOURCE.read_bytes()
        initial_hash = digest(SOURCE)
        (OUT / 'initial-source.lean').write_bytes(SOURCE.read_bytes())
        rows = []
        order = ['Definitions.Def_ZetaNine_HarmonicStability'] + [
            'missions.zeta9.formalization.' + name for name in (
                'CoefficientMap', 'CoefficientMapJet', 'CoefficientMapInjectivity',
                'CoefficientMapPartialFractions', 'CoefficientMapReflection',
                'CoefficientMapFiniteSum', 'CoefficientMapSummation', 'CoefficientMapAggregate',
                'CoefficientMapShiftDegree', 'CoefficientMapTelescoper', 'CoefficientMapKernelBridge',
                'CoefficientMapConnection', 'CoefficientMapParameterShift')]
        for index, target in enumerate(order, 1):
            row = run(['lake', '--no-cache', 'build', target], OUT, f'first-{index:02d}')
            row['target'] = target
            rows.append(row)
            record(first_log, {'source_sha256': initial_hash, 'rows': rows,
                               'native_objects_borrowed': False, 'fresh_cache_before_first': True})
            if row['actual_exit']:
                raise SystemExit(row['actual_exit'])
        object_path = PROJECT / 'b/lib/lean' / (MODULE.replace('.', '/') + '.olean')
        assert object_path.exists() and digest(SOURCE) == initial_hash
        (OUT / 'first-compiled.olean').write_bytes(object_path.read_bytes())
        record(first_log, {'source_sha256': initial_hash, 'rows': rows,
                           'native_objects_borrowed': False, 'fresh_cache_before_first': True,
                           'retained_object_sha256': digest(OUT / 'first-compiled.olean')})
        return
    assert first_log.exists()
    if args.mode == 'retry':
        previous = json.loads(first_log.read_text(encoding='utf-8'))
        assert len(previous['rows']) == 14 and all(r['actual_exit'] == 0 for r in previous['rows'][:13])
        attempts = [int(p.name.split('-')[1]) for p in OUT.glob('attempt-[0-9][0-9]') if p.is_dir()]
        folder = OUT / f'attempt-{max(attempts, default=0) + 1:02d}'
        folder.mkdir()
        (folder / SOURCE.name).write_bytes(SOURCE.read_bytes())
        (PROJECT / 'missions/zeta9/formalization' / SOURCE.name).write_bytes(SOURCE.read_bytes())
        row = run(['lake', '--no-cache', 'build', MODULE], folder, 'compile')
        row['source_sha256'] = digest(SOURCE)
        object_path = PROJECT / 'b/lib/lean' / (MODULE.replace('.', '/') + '.olean')
        if row['actual_exit'] == 0:
            assert object_path.exists()
            (folder / 'compiled.olean').write_bytes(object_path.read_bytes())
            row['retained_object_sha256'] = digest(folder / 'compiled.olean')
        record(folder / 'receipt.json', row)
        raise SystemExit(row['actual_exit'])
    audit = OUT / 'type-audit.lean'
    assert audit.exists(), 'Prepare the exact audit before using this mode.'
    receipts = [json.loads(first_log.read_text(encoding='utf-8'))]
    receipts += [json.loads(p.read_text(encoding='utf-8')) for p in sorted(OUT.glob('attempt-*/receipt.json'))]
    latest = receipts[-1]
    assert latest['source_sha256'] == digest(SOURCE)
    assert latest.get('actual_exit', 0) == 0 and all(r['actual_exit'] == 0 for r in latest.get('rows', []))
    assert (PROJECT / 'missions/zeta9/formalization' / SOURCE.name).read_bytes() == SOURCE.read_bytes()
    destination = PROJECT / 'ParameterShiftAudit.lean'
    destination.write_bytes(audit.read_bytes())
    attempts = [int(p.name.split('-')[1]) for p in OUT.glob('audit-[0-9][0-9]') if p.is_dir()]
    folder = OUT / f'audit-{max(attempts, default=0) + 1:02d}'
    folder.mkdir()
    (folder / audit.name).write_bytes(audit.read_bytes())
    row = run(['lake', 'env', 'lean', str(destination)], folder, 'type-audit')
    row['source_sha256'] = digest(SOURCE)
    row['audit_source_sha256'] = digest(audit)
    record(folder / 'receipt.json', row)
    if row['actual_exit'] == 0:
        record(OUT / 'type-audit-receipt.json', row)
    raise SystemExit(row['actual_exit'])


if __name__ == '__main__':
    main()
