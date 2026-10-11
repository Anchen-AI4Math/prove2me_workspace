"""Pure recovery of immutable Outputs preparation. No Lean, Lake or API calls.

This is a new author recovery record. It does not edit or regenerate the old
preparation, source snapshots, original candidate, or any other lane's files.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
PREP = TASK / 'verification/formalization-coefficient-map-formal-transport-outputs-preparation-2026-10-04'
PROJECT = TASK / '.rt/oa1'


def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def binding(path):
    location = ({'task_relative': path.relative_to(TASK).as_posix()}
                if path.is_relative_to(TASK) else {'origin_absolute': str(path)})
    return {**location, 'bytes': path.stat().st_size, 'sha256': sha(path)}


def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def headers(raw):
    records = []
    lines = raw.decode('utf-8-sig').splitlines(keepends=True)
    for i, line in enumerate(lines):
        if line.startswith('theorem '):
            header = ''.join(lines[i:]).split(':=', 1)[0].rstrip()
            records.append({'name': line.split()[1], 'header': header})
    return records


def main():
    state = load(PREP / 'preparation-state.json')
    inputs = load(PREP / 'source-inputs.json')
    frozen = load(PREP / 'preparation-verification.json')
    contracts = load(PREP / 'endpoint-contracts.json')
    checks = []

    def check(group, row, path=None):
        path = path or TASK / row['task_relative']
        exists = path.is_file()
        actual = binding(path) if exists else None
        passed = exists and actual['bytes'] == row['bytes'] and actual['sha256'] == row['sha256']
        checks.append({'group': group, 'path': str(path), 'expected': row,
                       'actual': actual, 'passed': passed})

    for row in frozen['files']:
        check('preparation_freeze', row)
    for row in inputs['sources']:
        check('source_origin', row, Path(row['origin_absolute']))
        check('source_copy_or_snapshot', row['initial_project_copy'])
        check('source_copy_or_snapshot', row['immutable_initial_snapshot'])
    for row in inputs['prior_freeze_descriptors']:
        check('prior_freeze_descriptor', row)
    for row in state['controls']:
        check('control', row['immutable_source'])
        check('control', row['initial_project_copy'])
    assert len(checks) == 129 and all(row['passed'] for row in checks)

    sums = []
    for line in (PREP / 'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
        if not line.strip():
            continue
        expected, relative = line.split(maxsplit=1)
        relative = relative.lstrip('*')
        path = TASK / relative
        sums.append({'task_relative': relative, 'expected_sha256': expected,
                     'actual_sha256': sha(path), 'passed': sha(path) == expected})
    assert sums and all(row['passed'] for row in sums)

    source = TASK / 'formalization/CoefficientMapFormalTransportOutputs.lean'
    actual_headers = headers(source.read_bytes())
    assert actual_headers == contracts['all16_contracts'] == state['original_exact_headers']
    assert len(actual_headers) == 16
    assert sha(source) == 'f16dc8be54bd58c09f240ed3404ba3810297e1a8e9d9ab9806893d410862f09d'
    jets = next(row for row in state['source'] if row['module'].endswith('.CoefficientMapFormalTransportJets'))
    assert jets['sha256'] == 'ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02'
    assert not any(path.exists() for path in [PROJECT / 'b', PROJECT / '.lake',
        PREP / 'compile-receipt.json', PREP / 'actual-runs', PREP / 'Root-lane-grant.json'])
    assert not list(PROJECT.rglob('*.olean'))
    assert not list(PROJECT.rglob('*.ilean'))

    paths = []
    for row in state['path_checks']:
        own_path = PROJECT / 'b/lib/lean' / (row['module'].replace('.', '/') + '.olean')
        length = len(str(own_path)) + 64
        assert length == row['path_plus_64'] and length <= 259
        paths.append({'module': row['module'], 'path': str(own_path), 'path_plus_64': length})

    source_hashes = []
    for row in state['source']:
        private = PROJECT / row['project_relative']
        imports = [line[7:].split() for line in private.read_text(encoding='utf-8-sig').splitlines()
                   if line.startswith('import ')]
        source_hashes.append({'module': row['module'], 'origin_absolute': row['origin_absolute'],
                             'private_source': binding(private),
                             'immutable_snapshot': row['immutable_initial_snapshot'],
                             'text_import_schedule_only': [name for line in imports for name in line]})

    report = {'status': 'PURE_RECOVERY_ALL_ORIGINAL_BINDINGS_MATCH',
              'observed_at_utc': datetime.now(timezone.utc).isoformat(),
              'author_recovery_not_independent_review': True,
              'Lean_invocations': 0, 'Lake_invocations': 0, 'API_invocations': 0,
              'candidate_actually_compiled': False, 'author_PASS_claimed': False,
              'original_preparation_modified': False, 'shared_source_modified': False,
              'old_source_snapshots_modified': False, 'Root_scope_or_credentials_modified': False,
              'original_binding_occurrences': len(checks),
              'unique_original_paths_rehashed': len({row['path'] for row in checks}),
              'sha256sum_occurrences': len(sums),
              'failed_rehashes': 0, 'original_binding_checks': checks, 'sha256sum_checks': sums,
              'candidate_source': binding(source),
              'verified_jets_source_sha256': jets['sha256'],
              'source_only_project_task_relative': '.rt/oa1',
              'cache_package_link_actual_runs_and_lane_grant_absent': True,
              'own_olean_ilean_counts': [0, 0],
              'borrowed_ja1_Root_tj1_proof_objects': False,
              'native_source_schedule_count': len(source_hashes),
              'source_schedule_not_actual_Lean_graph': True,
              'exact_original_text_headers': actual_headers,
              'primary_exact_contracts': contracts['primary_endpoints'],
              'boundary_candidate_count': len(state['boundary_names']),
              'boundary_candidate_names': state['boundary_names'],
              'source_control_count': len(state['controls']),
              'future_object_path_checks': paths,
              'max_object_path_plus_64': max(row['path_plus_64'] for row in paths),
              'planned_calls_not_actual_invocations': state['future_actual_calls'],
              'startup_requires_new_Root_lane_grant_and_grant_file': True,
              'repair_only_after_retained_actual_failure_in_private_newversion': True,
              'recorder_source_provenance': load(PREP / 'runner-provenance.json'),
              'recovery_script': binding(Path(__file__))}
    save('pure-recovery.json', report)
    save('actual-source-hashes.json', source_hashes)
    print(json.dumps({key: report[key] for key in [
        'status', 'original_binding_occurrences', 'unique_original_paths_rehashed',
        'sha256sum_occurrences', 'failed_rehashes', 'Lean_invocations', 'Lake_invocations',
        'API_invocations', 'native_source_schedule_count', 'max_object_path_plus_64']}, ensure_ascii=False))


if __name__ == '__main__':
    main()
