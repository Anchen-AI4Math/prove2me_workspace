"""Read-only verification of the inherited Jets native independent checkpoint.

This script invokes no Lean, Lake, compiler, API, or process mutation.
It only writes its own new inspection report and an immutable receipt snapshot.
"""
from pathlib import Path
import hashlib, json, re, sys, time

HERE = Path(__file__).resolve().parent
OUT = HERE.parent
TASK = OUT.parents[1]
ROOT = TASK.parent.parent
PROJECT = TASK / '.rt/tj1'
AUTHOR = TASK / 'verification/formalization-coefficient-map-formal-transport-jets-author-2026-10-04'
AUTHOR_SHA = '8b3f2da6d46de5f320ce2d6033535502e72dc79c46703c321211f646f6ccd3f3'
PREP_SHA = '7bcab39149d160e4bd4b947f227de8c0b002a49c4ac9a9de53962c46cec55dc0'
SOURCE_SHA = 'ccef5eaf7bad1b86ce8da45401b2ed3d5bb28e55aafc2626a92d4fc2a4cf4c02'

def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def binding(path):
    return dict(task_relative=path.resolve().relative_to(TASK.resolve()).as_posix(),
                bytes=path.stat().st_size, sha256=sha(path))

def check(rows):
    for row in rows:
        path = (TASK / row['task_relative']).resolve()
        assert path.is_relative_to(TASK.resolve())
        assert binding(path) == row, row['task_relative']

def schedule(rows):
    bymodule = {r['module']: r for r in rows}
    active, done, result = set(), set(), []
    def visit(module):
        if module in done: return
        assert module not in active
        active.add(module)
        source = PROJECT / bymodule[module]['project_relative']
        for line in re.findall(r'^import\s+([^\n]+)', source.read_text(encoding='utf-8-sig'), re.M):
            for dep in line.split():
                if dep in bymodule: visit(dep)
        active.remove(module); done.add(module); result.append(bymodule[module])
    for module in bymodule: visit(module)
    return result

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    started = time.monotonic()
    assert sha(AUTHOR / 'author-audit.json') == AUTHOR_SHA
    assert sha(OUT / 'preparation-freeze.json') == PREP_SHA
    author, prep = load(AUTHOR / 'author-audit.json'), load(OUT / 'preparation-freeze.json')
    assert author['verdict'] == 'PASS' and len(author['checks']) == 21
    assert len(author['stable_files']) == 439 and len(prep['stable_files']) == 64
    check(author['stable_files']); print('author439 current stream rehash: 0 mismatches', flush=True)
    check(prep['stable_files']); print('preparation64 current stream rehash: 0 mismatches', flush=True)
    export = AUTHOR / 'JetsVerifiedSource.lean'
    assert sha(export) == SOURCE_SHA
    historical = TASK / 'formalization/CoefficientMapFormalTransportJets.lean'
    assert sha(historical) == author['initial_shared_candidate_sha256']
    receipt_path = OUT / 'execution-receipt.json'
    receipt = load(receipt_path)
    initial_bytes = receipt_path.read_bytes()
    snapshot = HERE / 'inherited-execution-receipt.json'
    if snapshot.exists(): assert snapshot.read_bytes() == initial_bytes
    else: snapshot.write_bytes(initial_bytes)
    verified_receipts = []
    for row in receipt['rows']:
        check(row['input_bindings'] + row['output_bindings'] + row['evidence_bindings'])
        check([r['retained'] for r in row['immutable_input_snapshots']])
        check([row['actual_executor']])
        for retained in row['immutable_input_snapshots']:
            assert retained['retained']['bytes'] == retained['original']['bytes']
            assert retained['retained']['sha256'] == retained['original']['sha256']
        folder = TASK / row['folder_task_relative']
        assert int((folder / 'exit.txt').read_text()) == row['exit_code'] == 0
        stream_hash = hashlib.sha256()
        for name in ['stdout.log', 'stderr.log']:
            with (folder / name).open('rb') as f:
                while chunk := f.read(8 * 1024 * 1024): stream_hash.update(chunk)
        assert stream_hash.hexdigest() == sha(folder / 'combined.log')
        selected = load(folder / 'selected-paths.json')
        for key in ['LEAN_PATH', 'LEAN_SRC_PATH']:
            allowed = {str(Path(x).resolve()).casefold() for x in selected[key]['allowed_exact_set']}
            assert all(str(Path(x).resolve()).casefold() in allowed for x in selected[key]['filtered'])
            own = PROJECT / 'b/lib/lean' if key == 'LEAN_PATH' else PROJECT
            assert str(own.resolve()).casefold() in allowed
            assert str(ROOT.resolve()).casefold() not in allowed
            assert not any('/.rt/ja1/' in x.replace('\\', '/').lower() for x in selected[key]['filtered'])
        verified_receipts.append(dict(label=row['label'], exit_code=row['exit_code'],
            folder_task_relative=row['folder_task_relative'], elapsed_seconds=row['elapsed_seconds'],
            input_bindings=len(row['input_bindings']), output_bindings=len(row['output_bindings']),
            evidence_bindings=len(row['evidence_bindings']), actual_log_exit_output_verified=True))
    expected = [('runtime', ['--version'], None)]
    for row in schedule(prep['source_records']):
        obj = 'b/lib/lean/' + row['module'].replace('.', '/') + '.olean'
        expected.append(('source-' + row['module'].rsplit('.', 1)[-1], ['-o', obj, row['project_relative']], obj))
    for module in ['IndependentExprDagV3', 'IndependentExprDagValidationV3'] + prep['planned_control_modules']:
        obj = 'b/lib/lean/' + module + '.olean'
        prefix = 'serializer-' if module.startswith('IndependentExprDag') else 'control-'
        expected.append((prefix + module, ['-o', obj, module + '.lean'], obj))
    expected.append(('actual-own-object-resolution', ['JetsActualResolver.lean'], None))
    successful = {r['label'] for r in receipt['rows'] if r['exit_code'] == 0}
    missing = [dict(label=label, lean_arguments=args, output_object=obj) for label,args,obj in expected if label not in successful]
    assert len(expected) == 27 and len(successful) == 14 and len(missing) == 13
    known = {str((TASK / r['folder_task_relative']).resolve()).casefold() for r in receipt['rows']}
    orphans = []
    for folder in sorted((OUT / 'actual-runs').iterdir()):
        if str(folder.resolve()).casefold() in known: continue
        assert folder.is_dir()
        files = [binding(x) for x in sorted(folder.iterdir()) if x.is_file()]
        matches = []
        if (folder / 'i04').exists():
            snapshot_hash = sha(folder / 'i04')
            matches = [r['module'] for r in prep['source_records'] if r['project_copy']['sha256'] == snapshot_hash]
        orphans.append(dict(folder_task_relative=folder.relative_to(TASK).as_posix(), files=files,
            source_modules_matching_snapshot=matches, exit_present=(folder/'exit.txt').exists(),
            combined_log_present=(folder/'combined.log').exists(), receipt_present=False,
            excluded_from_success_and_failure_counts=True,
            status='UNRECORDED_INTERRUPTED_ATTEMPT_NO_TERMINAL_EXIT_EVIDENCE'))
    assert len(orphans) == 1 and not orphans[0]['exit_present']
    imports = []
    for row in prep['source_records']:
        source = PROJECT / row['project_relative']
        assert source.read_bytes() == (TASK / row['immutable_source_snapshot']['task_relative']).read_bytes()
        imports.append(dict(module=row['module'], source=binding(source),
            actual_import_statements=re.findall(r'^import\s+([^\n]+)',source.read_text(encoding='utf-8-sig'),re.M)))
    report = dict(status='PURE_CHECKPOINT_INSPECTION_NO_LEAN_INVOCATION',
        reviewer_role='New independent takeover reviewer; did not author Jets proofs; inherited prior reviewer source-build evidence',
        inherited_reviewer_disclosure=prep['role_disclosure'],
        author_report=binding(AUTHOR/'author-audit.json'), preparation=binding(OUT/'preparation-freeze.json'),
        successful_export=binding(export), historical_shared_source=binding(historical),
        author_bindings_personally_rehashed=439, preparation_bindings_personally_rehashed=64,
        inherited_receipt=binding(snapshot), inherited_successful_calls=14, inherited_fresh_native_source_calls=13,
        verified_inherited_receipts=verified_receipts, source_copies_and_actual_imports=imports,
        orphan_attempts=orphans, missing_planned_calls=missing,
        process_observation=dict(parent_authoritative_report='Old session78002 Missing; Root query found no tj1 or driver residual processes',
            local_CIM_query='Denied by environment; no command-line process claim made from this query',
            Lean_Lake_invocations=0),
        continuation_requires_new_parent_lane2_grant=True,
        original_executor_direct_restart_blocked='c015-a01 exists without receipt; original mkdir(exist_ok=False) would collide',
        original64_author439_and_proof_bytes_modified=False, mismatches=0,
        elapsed_seconds=round(time.monotonic()-started,3))
    (HERE/'checkpoint-inspection.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:report[k] for k in ['status','author_bindings_personally_rehashed','preparation_bindings_personally_rehashed','inherited_successful_calls','orphan_attempts','missing_planned_calls','mismatches','elapsed_seconds']},ensure_ascii=False,indent=2))

if __name__ == '__main__': main()
