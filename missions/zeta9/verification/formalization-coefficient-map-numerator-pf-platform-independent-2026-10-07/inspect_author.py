"""Pure, personally hashed input inspection for an independent PF platform audit."""
from pathlib import Path
import hashlib, json, sys, time

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parent.parent
AUTHOR = TASK / 'formalization/platform/coefficient-map-numerator-pf'
PROJECT = TASK / '.rt/pfi1'
AUTHOR_SHA = '5a9491c73cbbb980b411a3389a4c5acd6f0e5ceb71149c8a508f9553660f0ebf'
PREPARATION_SHA = '2dddbef40532b0a7c423fae9d310423456ce4d2f2562223b95edff1869eea606'
NATIVE_AUTHOR_SHA = '7285317314696ed866c4b9333e6b0b9fdc01df1813048192aad1ecfabb24f2a5'
NATIVE_INDEPENDENT_SHA = '49a69e8a35d4325c77aee2543a5aa7aed630838bcdfa6dbd16225f35e0c7dc97'

def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def resolve(row):
    if row.get('task_relative') is not None:
        path = TASK / row['task_relative']
        if row.get('root_relative') is not None:
            assert path.resolve() == (ROOT / row['root_relative']).resolve()
        return path
    return ROOT / row['root_relative']

def check(rows):
    for row in rows:
        path = resolve(row)
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], str(path)

def bind(path):
    return dict(task_relative=path.resolve().relative_to(TASK.resolve()).as_posix(),
                bytes=path.stat().st_size, sha256=sha(path))

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    started = time.monotonic()
    assert not PROJECT.exists(), 'Independent project must initially be absent.'
    ap, pp = AUTHOR/'author-audit.json', AUTHOR/'preparation-verification.json'
    assert sha(ap) == AUTHOR_SHA and sha(pp) == PREPARATION_SHA
    author, prep = load(ap), load(pp)
    assert author['verdict'] == 'PASS' and len(author['checks']) == 24
    assert all(row['passed'] for row in author['checks'])
    assert len(author['stable_files']) == 1441 and len(prep['files']) == 80
    check(author['stable_files']); check(prep['files'])
    na = TASK/'verification/formalization-coefficient-map-numerator-pf-2026-10-04/author-audit.json'
    ni = TASK/'verification/formalization-coefficient-map-numerator-pf-independent-2026-10-04/independent-review.json'
    assert sha(na) == NATIVE_AUTHOR_SHA and sha(ni) == NATIVE_INDEPENDENT_SHA
    native_author, native_independent = load(na), load(ni)
    na_rows = native_author.get('stable_files', native_author.get('files'))
    ni_rows = native_independent.get('stable_files', native_independent.get('files'))
    assert len(na_rows) == 188 and len(ni_rows) == 388
    check(na_rows); check(ni_rows); check(author['seven_payloads'])
    state = load(AUTHOR/'preparation-state.json')
    source_records = state['native_sources']
    assert len(source_records) == 16
    for row in source_records:
        check([row])
    official = ROOT/'references/upload_full_project.md'
    skill = ROOT/'SKILL.md'
    assert 'version: "0.12.1"' in skill.read_text(encoding='utf-8-sig')
    report = dict(status='PURE_PERSONAL_INPUT_INSPECTION_COMPLETE',
        role='Independent platform reviewer; did not author the NumeratorPF platform payloads',
        prior_role='Completed the resumed independent Jets review; no PF payload authorship',
        author_report=bind(ap), author_checks=24, author_bindings_personally_rehashed=1441,
        author_binding_bytes=sum(row['bytes'] for row in author['stable_files']),
        original_preparation=bind(pp), original_preparation_bindings_personally_rehashed=80,
        native_author_report=bind(na), native_author_bindings_personally_rehashed=188,
        native_independent_report=bind(ni), native_independent_bindings_personally_rehashed=388,
        seven_immutable_payloads=author['seven_payloads'],
        author_actual_calls=dict(attempts=author['actual_receipt_rows'],
            successful=author['actual_successful_rows'], failed_Lean=author['actual_failed_Lean_rows']),
        historical_author_errors=author['complete_continuation_failure_classification'],
        excluded_unreachable_weighted_boundary=author['excluded_unreachable_weighted_boundary'],
        native_source_closure=source_records, parent_definition_source_plan=state['parent_definitions'],
        independent_project_task_relative='.rt/pfi1', independent_project_initially_absent=True,
        independent_cache_initially_absent=True,
        foreign_author_Root_or_prior_Jets_proof_objects_permitted=False,
        shared_objects_permitted='Only the pinned existing package caches; not Root .lake/build or any .rt sibling cache',
        official_workflow=dict(root_relative='references/upload_full_project.md',
            bytes=official.stat().st_size, sha256=sha(official), version='0.12.1',
            rule='Fresh declaration graph and all participating source parser facts; exact seven upload bytes; complete original and staged types'),
        independence_plan=dict(native_SOURCE_compiles=16, existing_pure_definition_SOURCE_compiles=5,
            exact_payloads=7, native_definition_full_type_values=11, native_named_proof_full_types=34,
            native_generated_equation_helpers=1, complete_own_forall_endpoints=3,
            solution_environments=3, reachable_boundaries_per_environment=9,
            new_pure_definition_Expr_equal_isDefEq_and_whole_rfl_per_environment=5,
            own_Stage1_and_Stage2_oracles_required=True,
            actual_findOLean_and_module_header_required=True,
            every_actual_input_full_log_exit_output_and_error_retained=True),
        no_Lean_Lake_compiler_invocations=True, no_API_credentials_Root_or_mission_writes=True,
        no_independent_PASS_claimed=True, mismatches=0,
        finite_scope=author['mathematical_boundary'], elapsed_seconds=round(time.monotonic()-started,3))
    (OUT/'author-input-inspection.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({key:report[key] for key in ['status','author_bindings_personally_rehashed',
        'original_preparation_bindings_personally_rehashed','native_author_bindings_personally_rehashed',
        'native_independent_bindings_personally_rehashed','independent_project_task_relative',
        'independent_project_initially_absent','independent_cache_initially_absent','mismatches',
        'elapsed_seconds']},ensure_ascii=False,indent=2))

if __name__ == '__main__':
    main()
