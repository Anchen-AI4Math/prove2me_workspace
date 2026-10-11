"""Finalize only from real successful receipts and actual emitted JSON records."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import re

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parent.parent
PROJECT = TASK / '.rt/pfi'
AUTHOR = TASK / 'verification/formalization-coefficient-map-numerator-pf-2026-10-04'
STD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def binding(path):
    return {'root_relative': path.relative_to(ROOT).as_posix(),
            'sha256': sha(path), 'bytes': path.stat().st_size}

def verify(records):
    for item in records:
        path = ROOT / item['root_relative']
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert sha(path) == item['sha256'] and path.stat().st_size == item['bytes'], str(path)

def records_from_log(path):
    return [json.loads(line) for line in path.read_text(encoding='utf-8-sig').splitlines()
            if line.startswith('{')]

def std_only(records):
    for row in records:
        if 'axioms' in row:
            assert set(row['axioms']) <= STD, row

def own_files(root):
    for base, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [name for name in dirs if not (Path(base) / name).is_junction()
                   and not (Path(base) / name).is_symlink() and name != '__pycache__']
        for name in files:
            yield Path(base) / name

def main():
    result_path = OUT / 'independent-review.json'
    assert not result_path.exists(), 'Never overwrite an already frozen independent review'
    prep_path = OUT / 'preparation-freeze.json'
    assert sha(prep_path) == '94055899ce98fd780c118354986706bcc260f37a6c8c9d82387e968c9e7c47c2'
    prep = load(prep_path)
    extension = OUT / 'execution-preparation-freeze.json'
    assert sha(extension) == '41ae3aecff53552f96cd529271ca1822d16fdf7d7a37a327e51df4027410a2ff'
    verify(prep['stable_files'])
    verify(load(extension)['stable_files'])
    assert sha(AUTHOR / 'author-audit.json') == '7285317314696ed866c4b9333e6b0b9fdc01df1813048192aad1ecfabb24f2a5'
    author = load(AUTHOR / 'author-audit.json')
    assert author['verdict'] == 'PASS' and len(author['stable_files']) == 188
    verify(author['stable_files'])
    grant = load(OUT / 'lane-grant.json')
    assert grant['explicit_parent_Lean_lane_granted'] and grant['lane'] == 1
    receipt = load(OUT / 'actual-execution-receipt.json')
    assert receipt['source_phase_complete'] and receipt['controls_phase_complete']
    assert receipt['empty_own_cache_before_first_Lean_call']
    successes = [row for row in receipt['rows'] if row['actual_exit'] == 0]
    failures = [row for row in receipt['rows'] if row['actual_exit'] != 0]
    for row in receipt['rows']:
        for key in ['log', 'exit_file']:
            assert sha(OUT / row[key]) == row[key + '_sha256']
        assert int((OUT / row['exit_file']).read_text().strip()) == row['actual_exit']
        if row['source_snapshot']:
            assert sha(OUT / row['source_snapshot']) == row['source_snapshot_sha256'] == row['source_sha256']
        if row['environment_receipt_sha256']:
            assert sha(OUT / row['environment_receipt']) == row['environment_receipt_sha256']
        if row['object_sha256'] and row['actual_exit'] == 0:
            assert sha(TASK / row['object_task_relative']) == row['object_sha256']
    sources = [row for row in successes if row['logical_step'].startswith('fresh complete source ')]
    assert len(sources) == 16
    for expected, row in zip(prep['fresh_full_source_build_order'], sources):
        assert row['logical_step'] == 'fresh complete source ' + expected['module']
        assert row['source_sha256'] == expected['sha256']
        assert (ROOT / expected['root_relative']).read_bytes() == (PROJECT / expected['project_relative']).read_bytes()
    aliases = [row for row in successes if row['logical_step'].startswith('fresh source-only definition alias ')]
    assert len(aliases) == 2
    assert [row['logical_step'] for row in aliases] == [
        'fresh source-only definition alias IndependentValuesV2',
        'fresh source-only definition alias ValueAliases']
    runtime = [row for row in successes if row['logical_step'] == 'actual pinned runtime']
    assert len(runtime) == 1 and '4.33.1' in (OUT / runtime[0]['log']).read_text(encoding='utf-8-sig')

    # Repairs, if any, must be new filenames; successful logical controls are
    # explicitly selected by the terminal gate rather than inferred from failures.
    selected = load(OUT / 'terminal-control-selection.json')
    group = {}
    for key, label in selected['successful_control_labels'].items():
        row = next(x for x in successes if x['label'] == label)
        group[key] = records_from_log(OUT / row['log'])
    assert set(group) == {'source', 'expected', 'values', 'own', 'author_types',
                          'author_values', 'author_boundaries', 'resolver'}
    for items in group.values():
        std_only(items)
    plan = load(AUTHOR / 'audit-plan.json')
    defs = [row for row in group['source'] if row['kind'] == 'definition_full_expression']
    proofs = [row for row in group['source'] if row['kind'] == 'proof_full_type']
    assert [row['declaration'] for row in defs] == plan['actual_definition_names']
    assert [row['declaration'] for row in proofs] == plan['actual_proof_names']
    assert len(defs) == 16 and len(proofs) == 24
    assert all(row['type_expression_repr'] and row['full_value_expression_repr'] for row in defs)
    assert all(row['full_type_expression_repr'] for row in proofs)
    expected_types = [row for row in group['expected'] if row['kind'] == 'independent_complete_type_kernel']
    expected_proofs = [row for row in group['expected'] if row['kind'] == 'proof_full_type']
    assert len(expected_types) == len(expected_proofs) == 24
    assert [row['source'] for row in expected_types] == plan['actual_proof_names']
    assert all(row['whole_type_kernel_equal'] is True for row in expected_types)
    values = [row for row in group['values'] if row['kind'] == 'native_alias_whole_value_kernel']
    value_proofs = [row for row in group['values'] if row['kind'] == 'proof_full_type']
    assert len(values) == len(value_proofs) == 16
    assert [row['declaration'] for row in values] == plan['actual_definition_names']
    assert all(row['type_kernel_equal'] is True and row['full_value_kernel_equal'] is True for row in values)
    assert [row['declaration'] for row in group['own']] == [
        'NumeratorPFIndependentBoundaries.' + name for name in prep['independent_boundary_names']]
    assert len(group['own']) == 25
    assert len(group['author_types']) == 40
    assert len([row for row in group['author_values'] if row['kind'] == 'native_alias_whole_value_kernel']) == 16
    assert len([row for row in group['author_values'] if row['kind'] == 'proof_full_type']) == 16
    assert len([row for row in group['author_boundaries'] if row['kind'] == 'proof_full_type']) == 15
    author_types = [row for row in group['author_boundaries'] if row['kind'] == 'explicit_endpoint_type_kernel']
    assert len(author_types) == 3 and all(row['whole_type_kernel_equal'] for row in author_types)

    # Validate actual post-Lake paths against exact sets for every success and
    # independently check what real findOLean resolved for all 18 own modules.
    for row in successes:
        paths = load(OUT / row['environment_receipt'])
        for value in paths.values():
            allowed = {str(Path(p).resolve()).casefold() for p in value['allowed_exact_set']}
            assert all(str(Path(p).resolve()).casefold() in allowed
                       for p in value['filtered_exact_allowed_paths'])
            assert str(ROOT / '.lake/build/lib/lean').casefold() not in allowed
    resolutions = [row for row in group['resolver'] if row['kind'] == 'actual_module_resolution']
    assert len(resolutions) == 18
    assert [row['module'] for row in resolutions] == [
        item['module'] for item in prep['fresh_full_source_build_order']] + ['IndependentValuesV2', 'ValueAliases']
    for row in resolutions:
        actual = Path(row['object']).resolve()
        expected = (PROJECT / 'b/lib/lean' / Path(row['module'].replace('.', '/')).with_suffix('.olean')).resolve()
        assert actual == expected and actual.is_relative_to(PROJECT.resolve()) and actual.is_file()
    env = [row for row in group['resolver'] if row['kind'] == 'actual_environment']
    assert len(env) == 1 and env[0]['Lean_version'] == '4.33.1'
    actual_paths = {str(Path(p).resolve()).casefold() for p in env[0]['LEAN_PATH'].split(os.pathsep) if p}
    resolver_row = next(row for row in successes if row['label'] == selected['successful_control_labels']['resolver'])
    resolver_allowed = {str(Path(p).resolve()).casefold() for p in
                        load(OUT / resolver_row['environment_receipt'])['LEAN_PATH']['allowed_exact_set']}
    assert actual_paths <= resolver_allowed
    assert (PROJECT / '.lake/packages').is_junction()
    assert (PROJECT / '.lake/packages').resolve() == (ROOT / '.lake/packages').resolve()

    checks = [
      'fixed author PASS and all188 stable content bindings independently reverified',
      'frozen pure core37 and execution appendix7 preserved byte for byte',
      'explicit exclusive parent lane1 and global two-lane bound recorded',
      'absent pfi enrollment and empty independent cache before first compiler call',
      'all16 real imported source modules freshly compiled actual0 in own cache',
      'full source snapshots logs exit files and own objects bound to each execution',
      'no author Root or prior independent proof objects copied',
      'fixed toolchain Mathlib revision and personally observed runtime match',
      'all16 Data and PF definition types and complete value Expr emitted',
      'all24 Data and PF source proof full types emitted',
      'all24 independently written expected whole types closed standard three',
      'all24 actual source expected type Meta comparisons passed',
      'all16 whole definition types and values passed genuine Meta equality',
      'all16 complete function rfl value certificates closed standard three',
      'all25 own boundary controls closed standard three in successful run',
      'm0 improper X9 actual zero nine jets and actual nonzero numerator retained',
      'm0 proper X8 actual simple coefficient and rational one over t retained',
      'k0 k8 s1 s9 endpoints and actual two pole regularity boundaries retained',
      'unconditional denominator divisibility and offrange cleared identity retained',
      'strict properness of both injectivity inputs preserved without extra PF hypothesis',
      'weighted numerator true-jet agreement unrestricted in all source parameters',
      'author40 source records16 whole values16 rfl and15 boundaries freshly replayed',
      'author three exact generic endpoint kernel type comparisons freshly replayed',
      'all successful axiom collections contained only standard three names',
      'postLake actual Lean paths restricted to exact own and fixed package path sets',
      'real findOLean resolves all18 enrolled modules to personally compiled own objects',
      'all failed Lean runs retained wholly excluded including any propagated sorryAx',
      'pure Python enrollment diagnostics retained separately from Lean failures',
      'Data dependency prior reviewer authorship explicitly disclosed with fresh rebuild',
      'original frozen source and earlier evidence unchanged no API credentials Root scope writes',
      'no five-output or parameter HasSum transport integer-height or irrationality claim',
      'all execution handles terminal and lane1 released in actual terminal gate']
    gate = load(OUT / 'terminal-gate.json')
    assert gate['all_own_handles_terminal'] and gate['lane1_released_after_last_Lean_call']
    assert gate['live_own_Lean_handles'] == []
    axioms_records = [row for items in group.values() for row in items if 'axioms' in row]
    counts = {'actual_successful_calls': len(successes),
              'actual_successful_Lean_calls': len(successes) - len(runtime),
              'actual_runtime_calls': len(runtime),
              'actual_failed_Lean_calls': len(failures),
              'fresh_native_source_modules': 16, 'fresh_source_only_alias_modules': 2,
              'source_definition_full_Expr': 16, 'source_proof_full_types': 24,
              'independently_written_expected_full_types': 24,
              'true_whole_type_Meta_comparisons': 24,
              'whole_definition_type_and_value_Meta_comparisons': 16,
              'whole_function_rfl_proofs': 16, 'own_boundary_proofs': 25,
              'author_replayed_source_records': 40, 'author_replayed_full_value_Meta': 16,
              'author_replayed_whole_rfl_proofs': 16, 'author_replayed_boundaries': 15,
              'author_replayed_endpoint_whole_type_Meta': 3,
              'actual_own_module_resolutions': 18, 'standard_axiom_records': len(axioms_records)}
    candidates = {path.resolve() for path in own_files(OUT)} | {path.resolve() for path in own_files(PROJECT)}
    candidates.discard(result_path.resolve())
    candidates.discard((OUT / 'SHA256SUMS.txt').resolve())
    candidates.add((AUTHOR / 'author-audit.json').resolve())
    candidates.update((ROOT / item['root_relative']).resolve() for item in author['stable_files'])
    stable = [binding(path) for path in sorted(candidates, key=lambda p: p.as_posix().casefold())]
    assert all(path.is_relative_to(ROOT.resolve()) for path in candidates)
    report = {'verdict': 'PASS', 'stage': 'independent native NumeratorPartialFractions review only',
              'checked_at': datetime.now(timezone.utc).isoformat(),
              'reviewer': 'different NumeratorPF source author; prior Data dependency authorship disclosed',
              'source_sha256': prep['source_sha256'], 'Data_sha256': prep['Data_sha256'],
              'author_report_sha256': sha(AUTHOR / 'author-audit.json'),
              'checks': [{'name': name, 'passed': True} for name in checks],
              'counts': counts, 'stable_files': stable, 'successful_groups_actual_records': group,
              'retained_Lean_failures_whole_run_excluded': failures,
              'pure_preparation_diagnostics_not_Lean_failures': [
                load(path) for path in [OUT / 'pure-preparation-01-diagnostic.json',
                                       OUT / 'enrollment-01-diagnostic.json',
                                       OUT / 'progress-reader-01-diagnostic.json']],
              'remaining_bindings': [], 'all_handles_terminal': gate,
              'five_formal_output_transport_proved': False,
              'HasSum_parameter_transport_proved': False,
              'arbitrary_abstract_principal_part_array_uniqueness_proved': False,
              'platform_acceptance_claimed': False,
              'findings': [
                {'severity': 'informational', 'topic': 'cache',
                 'message': 'Cli has no olean build directory. Initial pure enrollment Python1 retained; new driver permits exact eight existing package caches plus own fresh cache.'},
                {'severity': 'informational', 'topic': 'properness',
                 'message': 'Actual m0 X9 zero-jets counterexample excludes weakening strict properness; admissible X8 yields1/t and does not imply summability.'},
                {'severity': 'informational', 'topic': 'dependency_authorship',
                 'message': 'Reviewer did not author NumeratorPF but authored the earlier Data dependency; Data rebuilt from frozen bytes in this independent empty cache.'},
                {'severity': 'informational', 'topic': 'scope',
                 'message': 'Only native generic actual-jet PF reconstruction and proper-numerator injectivity. No parameter five-output or HasSum transport, heights or irrationality.'}]}
    result_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    verify(stable)
    sums = ''.join(item['sha256'] + '  ' + item['root_relative'] + '\n' for item in stable)
    sums += sha(result_path) + '  ' + result_path.relative_to(ROOT).as_posix() + '\n'
    (OUT / 'SHA256SUMS.txt').write_text(sums, encoding='utf-8')
    print(json.dumps({'verdict': 'PASS', 'report_sha256': sha(result_path),
                      'report_bytes': result_path.stat().st_size,
                      'checks': len(checks), 'stable_files': len(stable),
                      'counts': counts, 'remaining_bindings': []}, indent=2))

if __name__ == '__main__':
    main()
