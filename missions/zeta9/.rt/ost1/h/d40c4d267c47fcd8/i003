"""One missing resolver call only, after an explicit current Root lane grant."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import json
import execute_native_author as e
import resume_author_v3


def main():
    e.sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser()
    parser.add_argument('--root-lane-granted', action='store_true', required=True)
    parser.add_argument('--grant-record', type=Path, required=True)
    args = parser.parse_args()
    assert Path(e.sys.executable).resolve() == e.PY312.resolve()
    grant = args.grant_record.resolve()
    assert grant.is_relative_to(e.TASK.resolve()) and grant.is_file()
    grant_binding = e.binding(grant)
    current_grant = e.load(grant)
    assert current_grant['owner'] == 'parameter_author_recovery_1007' and current_grant['lane'] == 1
    assert current_grant['explicit_Lean_execution_granted'] and current_grant['private_project'] == '.rt/ost1'
    assert current_grant['only_permitted_new_Lean_call'] == 'additional-own-object-resolution attempt 2'
    assert not current_grant['source_rebuilds_permitted'] and not current_grant['Root_runs_Lean']
    assert current_grant['preserve_prior_failures'] and current_grant['max_global_zeta9_lanes'] == 2
    state = resume_author_v3.install_gate()
    preflight = e.load(e.OUT / 'recovery-preflight-2026-10-07.json')
    assert preflight['Lean_calls_by_recovery'] == 0
    assert preflight['actual_attempts'] == 33 and preflight['actual_failures'] == 3
    receipt = e.load(e.OUT / 'compile-receipt.json')
    assert e.binding(e.OUT / 'compile-receipt.json') == preflight['original_receipt']
    for b in preflight['exact_previous_author_bindings']:
        assert e.binding(e.TASK / b['task_relative']) == b
    latest = {r['label']: r for r in receipt['rows']}
    assert len(latest) == 31
    assert [r['label'] for r in latest.values() if r['exit_code']] == ['additional-own-object-resolution']
    standard = Path(preflight['standard_library_current_status']['absolute'])
    assert standard.is_file() and standard.stat().st_size == preflight['standard_library_current_status']['bytes']
    assert e.sha(standard) == preflight['standard_library_current_status']['sha256']
    provenance = dict(role='same native AUTHOR continuation; no independent review claim',
                      started_at_utc=datetime.now(timezone.utc).isoformat(),
                      current_root_grant=grant_binding, recovery_preflight=e.binding(e.OUT / 'recovery-preflight-2026-10-07.json'),
                      actual_recovery_executor=e.binding(Path(__file__)),
                      previous_terminal_rows=33, previous_successful_calls=30, previous_failed_calls_retained=3,
                      prior_source_compilations_rehashed=22, prior_own_objects_rehashed=28,
                      continuation_reuse_of_same_author_SOURCE_objects_disclosed=True,
                      foreign_proof_objects_borrowed=False, source_rebuilds_by_recovery=0,
                      only_permitted_call='additional-own-object-resolution', required_Lean_threads=1,
                      API_Root_module_scope_or_mission_operations=False)
    e.dump(e.OUT / 'recovery-provenance-2026-10-07.json', provenance)
    runner = e.recorder()
    runner.__file__ = str(Path(__file__))
    runner.run('additional-own-object-resolution', ['additional_resolver.lean'])
    receipt = e.load(e.OUT / 'compile-receipt.json')
    latest = {r['label']: r for r in receipt['rows']}
    assert len(receipt['rows']) == 34 and len(latest) == 31 and all(r['exit_code'] == 0 for r in latest.values())
    expected_modules = [r['module'] for r in state['sources'] + state['controls']] + ['ParameterSummationWholeFunctionRflAudit']
    resolved = []
    for row in runner.rows(e.OUT / 'additional-own-object-resolution.log'):
        raw = Path(row['olean'])
        actual = raw.resolve() if raw.is_absolute() else (e.PROJECT / raw).resolve()
        expected = (e.PROJECT / 'b/lib/lean' / (row['module'].replace('.', '/') + '.olean')).resolve()
        assert actual == expected and actual.is_file()
        resolved.append(dict(**row, resolved_absolute=str(actual), actual_execution_cwd=str(e.PROJECT),
                             own_object_resolution_passed=True))
    assert [r['module'] for r in resolved] == expected_modules and len(resolved) == 28
    e.dump(e.OUT / 'additional-actual-own-object-resolution.json', resolved)
    e.dump(e.OUT / 'additional-terminal-runtime-state.json',
           dict(actual_rows=len(receipt['rows']), actual_successes=sum(r['exit_code'] == 0 for r in receipt['rows']),
                actual_failures=sum(r['exit_code'] != 0 for r in receipt['rows']),
                original_planned_final_calls=29, additional_rfl_and_resolver_final_success_calls=2,
                additional_resolver_prior_failed_attempt_retained=True, final_own_objects=28,
                whole_function_rfl_reached=True, continuation_recovery_actual_Lean_calls=1,
                author_freeze_still_required=True, independent_review_still_required=True))
    print(json.dumps(dict(additional_resolver='actual terminal PASS', actual_rows=34,
                          actual_successes=31, actual_failures=3, own_objects=28,
                          source_rebuilds_by_recovery=0, author_freeze_still_required=True)))


if __name__ == '__main__':
    main()
