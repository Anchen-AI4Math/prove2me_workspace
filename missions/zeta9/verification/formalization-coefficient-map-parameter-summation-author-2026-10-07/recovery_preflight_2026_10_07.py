"""Pure recovery verification. No Lean, Lake, API or shared module operations."""
from pathlib import Path
from datetime import datetime, timezone
import json
import execute_native_author as e
import resume_author_v3


def main():
    e.sys.stdout.reconfigure(encoding='utf-8')
    state = resume_author_v3.install_gate()
    receipt = e.load(e.OUT / 'compile-receipt.json')
    assert len(receipt['rows']) == 33
    latest = {r['label']: r for r in receipt['rows']}
    assert len(latest) == 31
    assert [r['label'] for r in latest.values() if r['exit_code']] == ['additional-own-object-resolution']
    assert latest['control-ParameterSummationWholeFunctionRflAudit']['exit_code'] == 0
    assert latest['additional-own-object-resolution']['exit_code'] == 1
    checks, bindings = [], {}

    def check(name, condition):
        assert condition, name
        checks.append({'name': name, 'passed': True})

    def rehash(record):
        raw = record['task_relative']
        relative = Path(raw)
        check('contained relative binding ' + raw, not relative.is_absolute() and '..' not in relative.parts)
        check('no credential binding ' + raw, relative.name not in {'credentials.json', '.env'})
        path = e.TASK / relative
        check('rehash ' + raw, path.is_file() and e.binding(path) == record)
        bindings[raw] = record

    for r in receipt['rows']:
        check('actual command ' + r['label'] + '-' + str(r['attempt']),
              r['command'][:6] == [str(e.LAKE), 'env', str(e.PY312), str(e.LEAF), str(e.LEAN), '-j1']
              and r['cwd'] == str(e.PROJECT))
        for key in ['stdout', 'stderr', 'log', 'exit_file', 'selected_paths']:
            rehash(r[key])
        check('actual exit text ' + r['label'] + '-' + str(r['attempt']),
              int((e.TASK / r['exit_file']['task_relative']).read_text().strip()) == r['exit_code'])
        check('actual failed row retained ' + r['label'] + '-' + str(r['attempt']),
              not r['exit_code'] or r['failure_retained'])
        for actual_key, retained_key in [('input_bindings', 'retained_input_bindings'),
                                         ('output_bindings', 'retained_output_bindings')]:
            original = {b['task_relative']: b for b in r[actual_key]}
            check('all retained ' + retained_key + ' ' + r['label'] + '-' + str(r['attempt']),
                  len(r[retained_key]) == len(original))
            for b in r[retained_key]:
                snapshot = b['snapshot_binding']
                orig = original[b['original_task_relative']]
                check('original bytes/hash paired ' + snapshot['task_relative'],
                      (orig['bytes'], orig['sha256']) == (snapshot['bytes'], snapshot['sha256']))
                rehash(snapshot)
        selected = e.load(e.TASK / r['selected_paths']['task_relative'])
        for key in ['LEAN_PATH', 'LEAN_SRC_PATH']:
            check('only own/fixed packages ' + key + ' ' + r['label'] + '-' + str(r['attempt']),
                  all(Path(raw).resolve().is_relative_to(e.PROJECT.resolve()) or
                      Path(raw).resolve().is_relative_to((e.ROOT / '.lake/packages').resolve())
                      for raw in selected[key]['filtered']))
    for r in latest.values():
        for b in r['input_bindings'] + r['output_bindings']:
            rehash(b)
    for r in state['sources']:
        rehash(r['immutable_snapshot'])
        origin = Path(r['origin_absolute'])
        check('native SOURCE origin ' + r['module'],
              origin.stat().st_size == r['bytes'] and e.sha(origin) == r['sha256'])
        own = e.PROJECT / r['project_relative']
        check('same author own native SOURCE ' + r['module'], e.sha(own) == r['sha256'])
    for r in state['controls']:
        rehash(r['immutable_source'])
    logs = {}
    for label in ['ParameterSummationFullTypeAudit', 'ParameterSummationDefinitionAudit',
                  'ParameterSummationBoundaryAudit', 'ParameterSummationWholeFunctionRflAudit',
                  'IndependentExprDagValidationV3']:
        logs[label] = [json.loads(line) for line in (e.OUT / ('control-' + label + '.log')).read_text(encoding='utf-8-sig').splitlines()
                       if line.startswith('{')]
    full = logs['ParameterSummationFullTypeAudit']
    definitions = logs['ParameterSummationDefinitionAudit']
    bounds = logs['ParameterSummationBoundaryAudit']
    whole = logs['ParameterSummationWholeFunctionRflAudit']
    fixtures = [r for r in logs['IndependentExprDagValidationV3'] if r['kind'] == 'expr_dag_validation']
    small = [r for r in logs['IndependentExprDagValidationV3'] if r['kind'] == 'expr_dag_small_source_validation']
    names = ['ZetaNine.CoefficientMapParameterSummationTransport.' + r['name'] for r in e.headers(e.SOURCE.read_bytes())]
    check('17 exact complete original types', len(full) == 17 and [r['declaration'] for r in full] == names
          and all(r['type_kernel_equal'] and r['all_fields_Expr_equal_roundtrip'] for r in full))
    check('one complete definition type and value', len(definitions) == 1
          and definitions[0]['type_kernel_equal'] and definitions[0]['value_kernel_equal'])
    check('nine closed typed boundary proofs', len(bounds) == 9 and all(r['kind'] == 'actual_closed_boundary' for r in bounds))
    check('whole-function rfl', len(whole) == 1 and whole[0]['kind'] == 'actual_whole_function_rfl')
    check('20 fixtures and three own small SOURCE controls', len(fixtures) == 20 and len(small) == 3
          and all(r['all_fields_roundtrip'] and r['raw_repr_reconstruction_equal'] for r in fixtures + small))
    std3 = []
    for r in full + definitions + bounds + whole + small:
        for key in ['axioms', 'source_axioms', 'expected_axioms']:
            if key in r:
                check('Std3 ' + r.get('declaration', r.get('source_name', '')) + ' ' + key,
                      set(r[key]) <= {'propext', 'Classical.choice', 'Quot.sound'})
                std3.append(r[key])
    check('49 actual Std3 reports', len(std3) == 49)
    own = e.load(e.OUT / 'actual-own-object-resolution.json')
    check('27 prior actual own resolver outputs', len(own) == 27 and all(r['own_object_resolution_passed'] for r in own))
    check('original native source exact', e.sha(e.SOURCE) == e.SOURCE_SHA)
    private = e.PROJECT / (e.NATIVE.replace('.', '/') + '.lean')
    check('unchanged private native source exact', e.sha(private) == e.SOURCE_SHA)
    check('failed additional resolver log is real', 'failed to read file' in
          (e.TASK / latest['additional-own-object-resolution']['log']['task_relative']).read_text()
          and 'RawLemmas.olean' in (e.TASK / latest['additional-own-object-resolution']['log']['task_relative']).read_text())
    check('supplemental resolver final report genuinely absent', not (e.OUT / 'additional-actual-own-object-resolution.json').exists())
    standard = e.BIN.parent / 'lib/lean/Std/Data/DHashMap/RawLemmas.olean'
    check('failed standard-library path readable now', standard.is_file() and standard.stat().st_size > 0)
    standard_status = {'absolute': str(standard), 'bytes': standard.stat().st_size,
                       'sha256': e.sha(standard), 'observed_at_utc': datetime.now(timezone.utc).isoformat()}
    result = dict(verdict='PREVIOUS_SUCCESS_REHASH_PASS; SUPPLEMENTAL_RESOLVER_RETRY_REQUIRED',
                  observed_at_utc=datetime.now(timezone.utc).isoformat(), role='same native AUTHOR continuation; independent review required',
                  original_receipt=e.binding(e.OUT / 'compile-receipt.json'), actual_attempts=33,
                  actual_successes=30, actual_failures=3, latest_labels=31, latest_successes=30,
                  fresh_native_source_calls=22, whole_original_theorems=17, whole_definition_type_and_value=1,
                  whole_function_rfl=1, actual_typed_boundaries=9, Std3_reports=49,
                  actual_original_own_object_resolutions=27, additional_28_object_resolution_complete=False,
                  author_freeze_complete=False, independent_review_complete=False, Lean_calls_by_recovery=0,
                  required_next_call='additional-own-object-resolution only, after explicit Root lane grant',
                  native_original=e.binding(e.SOURCE), native_private=e.binding(private),
                  standard_library_current_status=standard_status, checks=checks,
                  exact_previous_author_bindings=list(bindings.values()),
                  continuation_reuse_of_same_author_SOURCE_objects_disclosed=True,
                  foreign_objects_borrowed=False, API_Root_install_scope_or_mission_operations=False)
    e.dump(e.OUT / 'recovery-preflight-2026-10-07.json', result)
    print(json.dumps(dict(verdict=result['verdict'], checks=len(checks), bindings=len(bindings),
                         recovery_preflight_sha256=e.sha(e.OUT / 'recovery-preflight-2026-10-07.json'),
                         actual_attempts=33, actual_successes=30, actual_failures=3,
                         standard_library_current_status=standard_status), ensure_ascii=False))


if __name__ == '__main__':
    main()
