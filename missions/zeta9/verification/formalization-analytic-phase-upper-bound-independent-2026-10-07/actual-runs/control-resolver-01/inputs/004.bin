"""Original runner remains immutable; serial SOURCE-only DAG extension."""
from pathlib import Path
import argparse
import sys
sys.dont_write_bytecode = True
import prepare_independent as p
import run_independent as r

LEGACY_GATE = r.gate
LEGACY_INPUTS = r.module_inputs
CORE = 'APIPhaseExprDagV1'
VALIDATION = 'APIPhaseExprDagValidationV1'


def gate():
    grant = LEGACY_GATE()
    ext = p.load(p.OUT / 'Root-lean-lane-grant-dag-extension.json')
    assert ext['Root_explicit_grant'] and ext['current_owner'] == 'parameter_author_recovery_1007'
    assert ext['role'] == 'phase_independent_1007' and ext['lane'] == grant['lane'] == 1
    assert ext['maximum_global_Lean_lanes'] == 2 and ext['serial_lean_j1_only']
    assert not ext['recompile_successful_original_source2_permitted']
    assert ext['foreign_proof_objects_forbidden'] and not ext['API_calls_permitted']
    prep = p.load(p.OUT / 'lossless-dag-v2-preparation.json')
    assert p.binding(p.OUT / 'run_independent.py') == prep['original_runner']
    assert p.binding(p.OUT / 'preparation-state.json') == prep['original_preparation']
    assert p.binding(p.OUT / 'Root-lean-lane-grant-dag-extension.json') == prep['extension_grant']
    for row in prep['new_private_controls']:
        assert p.binding(p.TASK / row['immutable_source']['task_relative']) == row['immutable_source']
        assert p.binding(p.TASK / row['private_source']['task_relative']) == row['private_source']
    return grant


def module_inputs(module):
    result = LEGACY_INPUTS(module)
    result += [p.binding(p.OUT / 'Root-lean-lane-grant-dag-extension.json'), p.binding(p.OUT / 'lossless-dag-v2-preparation.json')]
    if module in [VALIDATION, 'APIPhaseTypes']:
        receipt = p.load(p.OUT / 'compile-receipt.json')
        row = next((x for x in reversed(receipt['rows']) if x['label'] == 'control-serializer' and x['exit_code'] == 0), None)
        assert row, 'Never consume a generic serializer object without own actual SOURCE success'
        for b in row['input_bindings'] + row['output_bindings']:
            r.check(b)
        result += [p.binding(p.PROJECT / (CORE + '.lean'))] + row['output_bindings']
    if module == 'APIPhaseResolver':
        receipt = p.load(p.OUT / 'compile-receipt.json')
        for label in ['control-serializer', 'control-serializer-validation']:
            row = next((x for x in reversed(receipt['rows']) if x['label'] == label and x['exit_code'] == 0), None)
            assert row
            for b in row['input_bindings'] + row['output_bindings']: r.check(b)
            result += row['output_bindings']
    return result


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser()
    parser.add_argument('--lane-granted', action='store_true', required=True)
    parser.parse_args()
    assert Path(sys.executable).resolve() == Path(p.PYTHON).resolve()
    r.gate = gate
    r.module_inputs = module_inputs
    r.__file__ = str(Path(__file__))
    gate()
    receipt = p.load(p.OUT / 'compile-receipt.json')
    for name in p.EXPECTED:
        rows = [x for x in receipt['rows'] if x['label'] == 'source-' + name]
        assert len(rows) == 1 and rows[0]['exit_code'] == 0
        for b in rows[0]['input_bindings'] + rows[0]['output_bindings']:
            r.check(b)
    if not (p.OUT / 'lossless-dag-v2-executor-provenance.json').exists():
        p.dump(p.OUT / 'lossless-dag-v2-executor-provenance.json', dict(
            role='same independent api1 SOURCE audit; failed OOM retained',
            original_runner_unchanged=p.binding(p.OUT / 'run_independent.py'),
            actual_resume_runner=p.binding(Path(__file__)),
            extension_grant=p.binding(p.OUT / 'Root-lean-lane-grant-dag-extension.json'),
            old_successful_source_compiler_calls_rehashed=2, old_source2_recompilations_permitted=False,
            only_own_prior_SOURCE_objects_consumed=True, foreign_objects_borrowed=False,
            new_generic_SOURCE_compiler_calls=2, serial_threads=1,
            API_Root_install_scope_or_mission_operations=False))
    for label, module in [('control-serializer', CORE), ('control-serializer-validation', VALIDATION),
                          ('control-types', 'APIPhaseTypes'), ('control-kernel', 'APIPhaseKernel'),
                          ('control-boundary', 'APIPhaseBoundary'), ('control-resolver', 'APIPhaseResolver')]:
        r.compile_module(label, module)
    final = p.load(p.OUT / 'compile-receipt.json')
    latest = {x['label']: x for x in final['rows']}
    assert len(latest) == 9 and all(x['exit_code'] == 0 for x in latest.values())
    print('All nine original/extended final labels actual terminal PASS; independent freeze still required.', flush=True)


if __name__ == '__main__':
    main()
