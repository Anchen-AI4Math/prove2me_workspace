"""Read-only hash preflight and new preparation receipt; no Lean/API calls."""
from pathlib import Path
import hashlib, json, sys
sys.stdout.reconfigure(encoding='utf-8')
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
SOURCE = TASK/'formalization/CoefficientMapConnection.lean'
SOURCE_SHA = '098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8'
IND = TASK/'verification/formalization-coefficient-map-connection-independent-2026-10-04/independent-review.json'
IND_SHA = '92940f9b02161210e55af39c625e0cd233eaf7a5bf9d5c1aa2238f0506e28d82'
PREP_SHA = 'e9264bc22d85c02e82513e96f802740227616dd622d0d4730e52615a2d78cfc2'
assert sha(SOURCE) == SOURCE_SHA and SOURCE.stat().st_size == 20507
assert sha(IND) == IND_SHA
ind = read(IND)
assert ind['verdict'] == 'PASS' and len(ind['checks']) == 28
assert all(r['pass'] for r in ind['checks']) and len(ind['stable_files']) == 108
verified = []
for r in ind['stable_files']:
    p = ROOT/r['root_relative'] if 'root_relative' in r else TASK/r['task_relative']
    assert p.resolve().is_relative_to(TASK.resolve())
    assert sha(p) == r['sha256'] and p.stat().st_size == r['bytes']
    verified.append(r)
prepfile = OUT/'preparation-verification.json'
assert sha(prepfile) == PREP_SHA
prep = read(prepfile)
for r in prep['preparation_files']:
    p = TASK/r['task_relative']
    assert sha(p) == r['sha256'] and p.stat().st_size == r['bytes']
project = TASK/'.rt/ca1'
assert not (project/'b').exists() and not (project/'.lake/build').exists()
assert sha(project/'missions/zeta9/formalization/CoefficientMapConnection.lean') == SOURCE_SHA
receipt = dict(status='PREPARATION_ONLY', Lean_Lake_executed=False,
    source_sha256=SOURCE_SHA, source_bytes=20507,
    independent_native_review_sha256=IND_SHA, independently_rehashed_bindings=verified,
    independently_rehashed_binding_count=108, native_independent_checks=28,
    inherited_preparation_sha256=PREP_SHA, inherited_preparation_files=len(prep['preparation_files']),
    fresh_project=project.relative_to(TASK).as_posix(), build_cache_absent=True,
    planned_max_object_path_plus_64=prep['planned_object_path_plus_64_max'],
    serial_Lean_lane_allocated=False, root_API_scope_credential_writes=False,
    remaining='Actual native compile, graph/parser/header, exact staged proof closure, full definition kernel equality, types/axioms/boundaries; separate independent platform review and parent installation.')
target = OUT/'author-resume-preflight.json'
assert not target.exists(), 'Do not overwrite a recorded preflight.'
target.write_text(json.dumps(receipt, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
print(json.dumps(dict(status=receipt['status'], native_bindings=108,
    preparation_files=len(prep['preparation_files']), fresh_cache_absent=True,
    receipt_sha256=sha(target)), ensure_ascii=False))
