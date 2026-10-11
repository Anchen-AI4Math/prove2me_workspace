"""Pure, source-only Jets independent preparation. Never invokes Lean/Lake."""
from pathlib import Path
import hashlib, json, re, sys, time

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parent.parent
PROJECT = TASK / '.rt/tj1'
AUTHOR = TASK / 'verification/formalization-coefficient-map-formal-transport-jets-author-2026-10-04'
AUTHOR_SHA = '8b3f2da6d46de5f320ce2d6033535502e72dc79c46703c321211f646f6ccd3f3'
SOURCE_SHA = 'ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02'
NATIVE = 'missions.zeta9.formalization.CoefficientMapFormalTransportJets'

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(value if isinstance(value, bytes) else value.encode('utf-8'))

def dump(path, value):
    write(path, json.dumps(value, ensure_ascii=False, indent=2) + '\n')

def binding(path):
    return dict(task_relative=path.resolve().relative_to(TASK.resolve()).as_posix(),
                bytes=path.stat().st_size, sha256=sha(path))

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not PROJECT.exists(), 'New independent project must be absent.'
    assert sha(AUTHOR/'author-audit.json') == AUTHOR_SHA
    author = load(AUTHOR/'author-audit.json')
    assert author['verdict'] == 'PASS' and len(author['checks']) == 21
    assert all(r['passed'] for r in author['checks']) and len(author['stable_files']) == 439
    verified = []
    start = time.monotonic()
    for row in author['stable_files']:
        path = (TASK/row['task_relative']).resolve()
        assert path.is_relative_to(TASK.resolve())
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], str(path)
        verified.append(row)
    export = TASK/author['verified_source']['task_relative']
    assert sha(export) == SOURCE_SHA and export.stat().st_size == 17475
    assert author['actual_final_source_sha256'] == SOURCE_SHA
    assert not author['shared_initial_candidate_actually_compiled_successfully']
    historical = TASK/'formalization/CoefficientMapFormalTransportJets.lean'
    assert sha(historical) == author['initial_shared_candidate_sha256']
    dump(OUT/'author-binding-review.json', dict(
        author_report=binding(AUTHOR/'author-audit.json'), verified_bindings=verified,
        verified_count=len(verified), verified_bytes=sum(r['bytes'] for r in verified),
        elapsed_seconds=round(time.monotonic()-start,3), mismatch_count=0,
        actual_final_export=binding(export), excluded_shared_historical_candidate=binding(historical),
        role_disclosure='Reviewer previously authored Data/Bounds foundations; did not author the 26 Jets/rho proofs.',
        Lean_Lake_compiler_invocations=0, independent_PASS_claimed=False))
    print('Personally streamed and verified 439 frozen author bindings.', flush=True)
    state = load(AUTHOR/'preparation-state.json')
    assert len(state['source']) == 19
    native = []
    for old in state['source']:
        source = export if old['module'] == NATIVE else ROOT/old['root_relative']
        expected = SOURCE_SHA if old['module'] == NATIVE else old['sha256']
        assert sha(source) == expected
        relative = old['module'].replace('.','/') + '.lean'
        target = PROJECT/relative
        snapshot = OUT/'source-only-snapshots'/relative
        write(target, source.read_bytes()); write(snapshot, source.read_bytes())
        assert target.read_bytes() == snapshot.read_bytes() == source.read_bytes()
        native.append(dict(module=old['module'], project_relative=relative,
            actual_source=binding(source) if source.is_relative_to(TASK) else
                dict(root_relative=source.relative_to(ROOT).as_posix(), bytes=source.stat().st_size, sha256=sha(source)),
            project_copy=binding(target), immutable_source_snapshot=binding(snapshot),
            import_scheduling_only=re.findall(r'^import\s+([^\n]+)', target.read_text(encoding='utf-8-sig'), re.M)))
    copied = []
    for module,expected in [('IndependentExprDagV3','1322612913bdc66d360720f64f9c72fa6047234e0717024ebb01a6c1303044e7'),
                            ('IndependentExprDagValidationV3','5c8ef7f4dc5c512497479b47ec4cd50280042febcc7ed45ed793360ad75ab693')]:
        original=AUTHOR/'copied-serializer-source'/(module+'.lean')
        assert sha(original)==expected
        write(PROJECT/(module+'.lean'), original.read_bytes())
        write(OUT/'serializer-source-only'/(module+'.lean'), original.read_bytes())
        copied.append(dict(module=module, original=binding(original),
            project_copy=binding(PROJECT/(module+'.lean')),
            immutable_source_snapshot=binding(OUT/'serializer-source-only'/(module+'.lean'))))
    for filename in ['lean-toolchain','lake-manifest.json']:
        write(PROJECT/filename, (ROOT/filename).read_bytes())
    lake=(TASK/'.rt/ja1/lakefile.lean').read_text(encoding='utf-8-sig')
    lake=lake.replace('package zeta9JetsNativeAuthor', 'package zeta9JetsNativeIndependent')
    lake=lake[:lake.index('lean_lib Controls')]
    write(PROJECT/'lakefile.lean', lake)
    wrapper=(TASK/'formalization/platform/coefficient-map-matrix/independent/lean_call.template.py').read_text(encoding='utf-8-sig')
    wrapper=wrapper.replace('MATRIX_RUN_PATHS_RECEIPT','JETS_INDEPENDENT_PATH_RECEIPT')
    write(PROJECT/'lean_call.py', wrapper)
    replay=AUTHOR/'JetsBoundaryAudit.lean'
    write(PROJECT/'AuthorBoundaryReplay.lean', replay.read_bytes())
    write(OUT/'AuthorBoundaryReplay.lean', replay.read_bytes())
    path_checks=[]
    for row in native:
        path=PROJECT/'b/lib/lean'/(row['module'].replace('.','/')+'.olean')
        path_checks.append(dict(path=str(path),path_plus_64=len(str(path))+64,passed=len(str(path))+64<=259))
    assert all(r['passed'] for r in path_checks)
    assert not (PROJECT/'b').exists() and not (PROJECT/'.lake').exists()
    assert not list(PROJECT.rglob('*.olean'))
    dump(OUT/'source-preparation.json', dict(status='PURE_SOURCE_ONLY_PREPARATION',
        Lean_Lake_compiler_invocations=0,project_task_relative=PROJECT.relative_to(TASK).as_posix(),
        project_previously_absent=True, cache_absent=True, source=native,
        serializer_source_only=copied,path_checks=path_checks,object_borrowing_permitted=False,
        Root_or_author_proof_fallback_permitted=False, complete_independent_PASS_claimed=False))
    write(OUT/'pure-source-preparation-exit.txt','0\n')
    print('Prepared 19 own source copies + 2 validated serializer source copies; cache absent.',flush=True)

if __name__ == '__main__':
    main()
