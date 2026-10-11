"""Fail-closed independent handoff gate. No Lean, API or Root mutation."""
from pathlib import Path
import hashlib, json, sys

sys.stdout.reconfigure(encoding='utf-8')
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[3]
ROOT = TASK.parents[1]
BATCH = OUT.parent
PROJECT = TASK / '.rt/ki1'
BUILD = PROJECT / 'b'
N = BUILD / 'n/lib/lean'
P = BUILD / 'p/lib/lean'
SOURCE_SHA = '1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb'
CONTROLS = {
    'author-audit.json': 'd0c86d3cb8f08e6c9e961782718cbedb8c319f4805002586cfa286f68d7eb057',
    'root-copy-plan.json': '6767eca98651d8c1e5867134bb981b1ccf3a45ed24ea5603b067c71a113abf28',
    'source-manifest.json': '97937c0d4883a77198ba9726faf80fc257f832462632ae89a239dc73a48d65c8',
    'SHA256SUMS.txt': 'ca8db6a63860e624fb94d675677d54a34bb0269547f8823fc7ef214b511548e8',
}
ROOT_RECORDS = ['root-install-receipt.json', 'task-build.log', 'task-build-exit.txt',
                'task-check.log', 'task-check-exit.txt']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def load(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def write(p, value):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(value if isinstance(value, bytes) else value.encode('utf-8'))

def dump(p, value):
    write(p, json.dumps(value, ensure_ascii=False, indent=2) + '\n')

def verify(require_root=True):
    for name, digest in CONTROLS.items():
        assert sha(BATCH / name) == digest, ('fixed author control changed', name)
    author = load(BATCH / 'author-audit.json')
    assert author['source_sha256'] == SOURCE_SHA and author['verdict'] == 'PASS'
    assert len(author['checks']) == 52 and all(r['pass'] for r in author['checks'])
    manifest = load(BATCH / 'source-manifest.json')
    assert len(manifest['files']) == 319 and len(manifest['fresh_compiler_cache_bindings']) == 252
    for row in manifest['files'] + manifest['fresh_compiler_cache_bindings']:
        path = (TASK / row['task_relative']).resolve()
        assert path.is_relative_to(TASK.resolve())
        assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes']
    sums = (BATCH / 'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines()
    assert len(sums) == 321
    for line in sums:
        digest, relative = line.split('  ', 1)
        path = (BATCH / relative).resolve()
        assert path.is_relative_to(BATCH.resolve()) and sha(path) == digest
    prep = load(OUT / 'preparation-state.json')
    for row in prep['source_and_pure_Definition_bindings']:
        original = ROOT / row['root_relative']
        own = PROJECT / row['root_relative']
        assert original.stat().st_size == own.stat().st_size == row['bytes']
        assert sha(original) == sha(own) == row['sha256']
    plan = load(BATCH / 'root-copy-plan.json')
    assert len(plan['files']) == 7 and len(plan['required_existing_Definitions']) == 11
    for row in plan['files']:
        assert sha(TASK / row['staged_task_relative']) == row['sha256']
        if require_root:
            path = ROOT / row['root_relative_destination']
            assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes']
    for row in plan['required_existing_Definitions']:
        assert sha(ROOT / row['root_relative']) == sha(TASK / row['task_relative']) == row['sha256']
    result = {'author_controls': CONTROLS, 'manifest_members': 319,
              'author_fresh_artifacts_hashed_only_never_borrowed': 252, 'sums_members': 321,
              'native11_trueDef11_own_sources_verified': True,
              'Root7_and_11_source_bytes_required': require_root}
    if require_root:
        freeze = load(OUT / 'root-frozen-inputs.json')
        assert freeze['status'] == 'ROOT_FIVE_RECORDS_FROZEN'
        parent_freeze_path = TASK / freeze['parent_freeze_task_relative']
        assert sha(parent_freeze_path) == freeze['parent_freeze_sha256'] == '8fe7972f7c8b0dbd42cc6d5d87dc27a8f72a087acae26a9810098d44550081bd'
        parent_freeze = load(parent_freeze_path)
        assert parent_freeze['actual_scoped_build_exit'] == 0 and parent_freeze['actual_scope_check_exit'] == 1
        assert parent_freeze['scope_check_only_preexisting_other_task_unassigned']
        assert len(parent_freeze['installed_and_existing_modules']) == 18
        for row in parent_freeze['installed_and_existing_modules']:
            path = ROOT / row['root_relative']
            assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes']
        assert set(freeze['records']) == set(ROOT_RECORDS)
        for name, row in freeze['records'].items():
            path = BATCH / name
            assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes']
        assert (BATCH / 'task-build-exit.txt').read_text().strip() == '0'
        assert (BATCH / 'task-check-exit.txt').read_text().strip() == '1'
        check = (BATCH / 'task-check.log').read_text(encoding='utf-8-sig')
        expected_check_lines = {
            'ERROR: Unassigned solution: Solutions/Sol_TaoFivePrimes_mertens_tail_upper_bound.lean; add it to a mission scope.json',
            'ERROR: Unassigned solution: Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large_mawia_v2.lean; add it to a mission scope.json',
        }
        assert set(line for line in check.splitlines() if line.strip()) == expected_check_lines
        result['root_records'] = freeze['records']
        result['parent_root_build_freeze_sha256'] = freeze['parent_freeze_sha256']
    return result

if __name__ == '__main__':
    dump(OUT / 'current-input-preflight.json', verify(require_root='--author-only' not in sys.argv))
    print('Actual frozen input gate verified; no Lean/Lake or publication operation.')
