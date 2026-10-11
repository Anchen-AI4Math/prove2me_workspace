"""Pure preparation freeze; no Lean/Lake/compiler invocation."""
from pathlib import Path
from datetime import datetime, timezone
import ast
import hashlib
import json
import os

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[3]
ROOT = TASK.parent.parent
AUTHOR = OUT.parent
PROJECT = TASK / '.rt/mt1'
ROOTFREEZE = TASK / 'verification/formalization-coefficient-map-matrix-root-preflight-2026-10-04/root-build-freeze.json'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
load = lambda path: json.loads(path.read_text(encoding='utf-8-sig'))

def binding(path):
    return {'task_relative': path.relative_to(TASK).as_posix(),
            'sha256': sha(path), 'bytes': path.stat().st_size}

def verify(records):
    for row in records:
        path = ROOT / row['root_relative'] if 'root_relative' in row else TASK / row['task_relative']
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes'], str(path)

def files(path):
    for base, dirs, names in os.walk(path, followlinks=False):
        dirs[:] = [name for name in dirs if name != '__pycache__'
                   and not (Path(base) / name).is_junction() and not (Path(base) / name).is_symlink()]
        for name in names:
            yield Path(base) / name

def main():
    assert not (OUT / 'preparation-verification.json').exists()
    assert sha(AUTHOR / 'author-audit.json') == 'c908b981d4fbb5b9c84ec137e829e1a1ac06b382640ef447811208b23bc09f8e'
    author = load(AUTHOR / 'author-audit.json')
    assert author['verdict'] == 'PASS' and len(author['checks']) == 33 and len(author['stable_files']) == 1543
    verify(author['stable_files'])
    assert sha(AUTHOR / 'root-copy-plan.json') == '94e573d015d6aba167adc32bad6e7b6427a81cfdf290e7483415ce2fbee7498c'
    copy = load(AUTHOR / 'root-copy-plan.json')
    assert len(copy['files']) == 7
    for row in copy['files']:
        source = TASK / row['staged_task_relative']
        assert sha(source) == row['sha256'] and source.stat().st_size == row['bytes']
        assert (PROJECT / row['root_relative_destination']).read_bytes() == source.read_bytes()
    assert sha(ROOTFREEZE) == '8aaece8c6d1e5fee406fc93b3c5d9f4399570b156d061367d14f25e9058a732c'
    root = load(ROOTFREEZE)
    assert len(root['Root_controls']) == 5 and len(root['installed_modules']) == 7
    verify(root['Root_controls'] + root['installed_modules'])
    assert root['actual_scoped_build_exit'] == 0 and root['actual_scoped_build_jobs'] == 3831
    assert root['actual_workspace_check_exit'] == 1 and len(root['preserved_other_task_check_errors']) == 2
    assert root['all_Root_compiler_handles_terminal']
    build = ROOT / root['Root_controls'][1]['root_relative']
    check = ROOT / root['Root_controls'][3]['root_relative']
    assert '3831' in build.read_text(encoding='utf-8-sig')
    assert check.read_text(encoding='utf-8-sig').splitlines() == root['preserved_other_task_check_errors']
    for index, expected in [(2, 0), (4, 1)]:
        assert int((ROOT / root['Root_controls'][index]['root_relative']).read_text(encoding='utf-8-sig').strip()) == expected
    state = load(OUT / 'preparation-state.json')
    assert not state['Lean_executed'] and len(state['native_sources']) == 13
    verify(state['native_sources'])
    for row in state['native_sources']:
        assert (PROJECT / row['project_relative']).read_bytes() == (ROOT / row['root_relative']).read_bytes()
    assert not (PROJECT / 'b').exists() and not (PROJECT / '.lake').exists()
    assert not list(PROJECT.rglob('*.olean'))
    assert all(row['passed'] for row in state['path_checks'])
    for path in OUT.glob('*.py'):
        ast.parse(path.read_text(encoding='utf-8-sig'))
    graph = [json.loads(line) for line in (AUTHOR / 'decl_graph.jsonl').read_text(encoding='utf-8-sig').splitlines() if line.startswith('{')]
    native_modules = {row['module'] for row in state['native_sources']}
    defs = [row for row in graph if row['kind'] == 'def' and row['startLine'] > 0 and row['module'] in native_modules]
    assert len(graph) == 415 and len(defs) == 70 and not any(row['isPrivate'] for row in defs)
    core = [row for row in graph if row['module'] == 'missions.zeta9.formalization.CoefficientMapMatrix' and row['startLine'] > 0]
    assert len(core) == 22
    facts = load(AUTHOR / 'integration-provenance.json')
    assert len(facts['inline_helper_names']) == 169 and facts['proof_records_per_solution'] == 187
    # These are historical author facts to be independently re-derived. No own
    # graph/parser/kernel result is claimed before execution.
    all_files = sorted(set(files(OUT)) | set(files(PROJECT)), key=lambda p: p.as_posix().casefold())
    frozen = {'status': 'PREPARATION_ONLY_BYTES_VERIFIED',
              'checked_at': datetime.now(timezone.utc).isoformat(),
              'Lean_executed': False, 'author_PASS_claimed': False,
              'independent_PASS_claimed': False, 'own_Lean_Lake_compiler_invocations': 0,
              'new_independent_project_initially_absent': True,
              'build_and_package_junction_still_absent': True,
              'source_only_no_author_mi1_ma1_Root_objects_copied': True,
              'author_report': binding(AUTHOR / 'author-audit.json'),
              'all_author1543_bindings_verified': True,
              'prior_native517_bindings_verified': True,
              'Root_freeze': binding(ROOTFREEZE),
              'actual_Root5_control_bindings_verified': root['Root_controls'],
              'actual_installed7_source_bindings_verified': root['installed_modules'],
              'Root_actual_build_exit': 0, 'Root_actual_build_jobs': 3831,
              'Root_check1_two_old_other_task_errors_preserved': root['preserved_other_task_check_errors'],
              'own_fresh_build_plan': {'native_modules': 13, 'staged_additional_modules': 18,
                                      'total_distinct_fresh_source_modules': 31,
                                      'HS_shared_same_module': 'personally fresh compiled once in native13; not historical reuse'},
              'prepared_author_facts_pending_own_oracles': {'graph_records': 415, 'native_source_defs': 70,
                'Matrix_defs': 5, 'Matrix_proofs': 17, 'cross_module_helpers': 169,
                'proof_records_each_full_Solution': 187, 'three_Solutions': 3,
                'separate_canonical_definition_contexts': 7},
              'prepared_additional_true_kernel_controls':
                {'native_and_staged70_complete_Def_type_value_Meta': 140,
                 'native_and_staged70_complete_function_rfl': 140,
                 'complete_proof_fields_retained': True,
                 'actual_findOLean_own_modules': 37},
              'original_native_controls_and_own_boundaries':
                {'native_author_source_records': 22, 'native_author_endpoints': 12,
                 'native_independent_source_records': 22, 'native_independent_boundaries': 26,
                 'staged_complete_expected_types_Meta': 51},
              'actual_own_graph_parser_header_kernel_and_boundaries_pending': True,
              'future_execution_requires_parent_lane2_and_Root5_gate': True,
              'Reference_admission': 'intentional sorryAx; statements only and completely excluded from complete proof evidence',
              'raw_parent21_proof_PP_value_differences': 'historical author diagnostic; no PP proof-erasure or value-equality gate',
              'scope': 'Even n>=2, actual F monomial rows/output columns, inverse rational quartic for integer b,a; true prescribed HasSum and absolute convergence. No integer inverse coefficients/heights, parameter transport, or irrationality.',
              'pure_schema_diagnostic': binding(OUT / 'root-schema-01-diagnostic.json'),
              'files': [binding(path) for path in all_files]}
    path = OUT / 'preparation-verification.json'
    path.write_text(json.dumps(frozen, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    verify(frozen['files'])
    print(json.dumps({'status': frozen['status'], 'preparation_sha256': sha(path),
                      'files': len(frozen['files']), 'own_Lean_Lake_compiler_invocations': 0,
                      'Root5_and_installed7_verified': True,
                      'longest_object_path_plus64': max(row['path_plus_64'] for row in state['path_checks'])}, indent=2))

if __name__ == '__main__':
    main()
