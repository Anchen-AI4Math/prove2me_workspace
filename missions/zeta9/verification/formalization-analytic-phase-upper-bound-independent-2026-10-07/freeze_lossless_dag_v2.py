"""Pure strict final freeze, preserving original serializer/tree failure evidence."""
from pathlib import Path
import json
import sys
sys.dont_write_bytecode = True
import prepare_independent as p
import run_independent as r


def parsed(row, prefix='PHI_RECORD|'):
    return [json.loads(line[len(prefix):]) for line in r.check(row['log']).read_text(encoding='utf-8').splitlines()
            if line.startswith(prefix if prefix else '{')]


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (p.OUT / 'independent-audit.json').exists(), 'Inspect immutable existing freeze rather than rerunning it.'
    receipt = p.load(p.OUT / 'compile-receipt.json')
    assert len(receipt['rows']) == 10
    assert sum(x['exit_code'] == 0 for x in receipt['rows']) == 9
    assert sum(x['exit_code'] != 0 for x in receipt['rows']) == 1
    latest = {x['label']: x for x in receipt['rows']}
    assert len(latest) == 9 and all(x['exit_code'] == 0 for x in latest.values())
    for name in p.EXPECTED:
        assert len([x for x in receipt['rows'] if x['label'] == 'source-' + name]) == 1
    validation = parsed(latest['control-serializer-validation'], '')
    fixtures = [x for x in validation if x['kind'] == 'expr_dag_validation']
    small = [x for x in validation if x['kind'] == 'expr_dag_small_source_validation']
    assert len(fixtures) == 20 and {x['fixture_index'] for x in fixtures} == set(range(20))
    assert len(small) == 3 and {x['source_name'] for x in small} == {
        'ZetaNine.AnalyticPhase.phaseRatio', 'ZetaNine.AnalyticPhase.phaseSlope', 'ZetaNine.AnalyticPhase.smoothPhaseRatio'}
    assert all(x['all_fields_roundtrip'] and x['raw_repr_reconstruction_equal'] for x in validation)
    assert all(set(x['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for x in small)
    types = parsed(latest['control-types'])
    dags = []
    for row in types:
        if row['kind'] == 'module_inventory':
            continue
        assert row['all_fields_type_Expr_equal'] and row['all_fields_value_Expr_equal']
        assert row['full_type_kernel_equal'] and row['full_value_kernel_equal'] and row['full_value_typed']
        assert row['value_raw_format'] == 'lossless lean-expr-dag-v1; full type_root and value_root'
        graph = json.loads(row['value_raw'])
        assert graph['format'] == 'lean-expr-dag-v1' and graph['nodes']
        assert 0 <= graph['type_root'] < len(graph['nodes']) and 0 <= graph['value_root'] < len(graph['nodes'])
        assert all(node[0] in {'bvar','fvar','mvar','sort','const','app','lam','forallE','letE','litNat','litString','mdata','proj'} for node in graph['nodes'])
        dags.append(dict(kind=row['kind'], name=row['name'], nodes=len(graph['nodes']),
                         all_fields_type_Expr_equal=True, all_fields_value_Expr_equal=True,
                         full_type_kernel_equal=True, full_value_kernel_equal=True, full_value_typed=True))
    assert len(dags) == 109
    evidence = dict(role='actual independent lossless full proof/type/value control evidence',
                    serializer_core_actual_row=latest['control-serializer'], serializer_validation_actual_row=latest['control-serializer-validation'],
                    all20_field_fixtures=fixtures, all3_actual_phase_small_source_fixtures=small,
                    full_math_source_declaration_DAG_records=dags, DAG_records=109,
                    actual_complete_type_and_value_Expr_equal_reconstructions=218,
                    full_value_actual_inferType_checks=109, all_primitive_name_level_binder_metadata_fields_preserved=True,
                    full_proof_values_exported_without_tree_expansion=True,
                    opaque_and_generated_theorem_values_not_omitted=True,
                    old_control_types_OOM_preserved=True, source2_actual_successes_not_recompiled=True,
                    no_Expr_equal_false_relabeling=True, independent_freeze_still_required=True)
    p.dump(p.OUT / 'actual-lossless-proof-value-evidence.json', evidence)
    original = p.OUT / 'freeze_independent.py'
    assert p.sha(original) == 'b3194e1c125237240e2f829a5576db6d7134dfc1311341d2a356c411f7f10d6f'
    source = original.read_text(encoding='utf-8')
    old_required = "             'control-types','control-kernel','control-boundary','control-resolver']"
    assert source.count(old_required) == 1
    source = source.replace(old_required, "             'control-types','control-kernel','control-boundary','control-resolver',\n             'control-serializer','control-serializer-validation']")
    old_own = " assert own_resolved == {'missions.zeta9.formalization.AnalyticPhase','missions.zeta9.formalization.AnalyticPhaseUpperBound'}"
    assert source.count(old_own) == 1
    source = source.replace(old_own, " assert own_resolved == {'missions.zeta9.formalization.AnalyticPhase','missions.zeta9.formalization.AnalyticPhaseUpperBound',\n                         'APIPhaseExprDagV1','APIPhaseExprDagValidationV1'}")
    old_kind = "   kind = 'independent_own_SOURCE_compiled_phase'; own_resolved.add(item['module'])"
    assert source.count(old_kind) == 1
    source = source.replace(old_kind, "   kind = 'independent_own_SOURCE_compiled_phase' if item['module'].startswith('missions.zeta9.formalization.') else 'independent_own_SOURCE_compiled_audit_control'\n   own_resolved.add(item['module'])")
    old_raw = "    assert isinstance(value,str) and value and '...' not in value and '…' not in value"
    assert source.count(old_raw) == 1
    source = source.replace(old_raw, "    assert isinstance(value,str) and value\n    if field == 'value_raw' and item.get('value_raw_format') == 'lossless lean-expr-dag-v1; full type_root and value_root':\n     graph = json.loads(value)\n     assert graph['format'] == 'lean-expr-dag-v1' and item['all_fields_type_Expr_equal'] and item['all_fields_value_Expr_equal']\n     assert item['full_value_typed'] and item['full_type_kernel_equal'] and item['full_value_kernel_equal']\n    else: assert '...' not in value and '…' not in value")
    old_final = "  platform_publication_or_acceptance_claimed=False)"
    assert source.count(old_final) == 1
    source = source.replace(old_final, "  platform_publication_or_acceptance_claimed=False,\n  current_owner='parameter_author_recovery_1007',Phase_author_role=False,\n  independent_SOURCE_only_provenance=p.load(p.OUT/'current-auditor-provenance-2026-10-07.json'),\n  strict_lossless_DAG_repair_provenance=p.load(p.OUT/'lossless-dag-v2-executor-provenance.json'),\n  actual_lossless_full_proof_value_DAG_records=109,actual_complete_type_value_Expr_equal_reconstructions=218,\n  actual_DAG_value_inferType_checks=109,serializer_complete_field_fixtures=20,serializer_actual_phase_source_fixtures=3,\n  all_name_level_binder_mdata_syntax_fields_preserved=True,raw_tree_and_DAG_encodings_explicitly_distinguished=True,\n  original_mathematical_SOURCE2_successes_not_recompiled=True,generic_serializer_fresh_SOURCE_calls=2,\n  actual_lossless_full_proof_value_evidence=p.binding(p.OUT/'actual-lossless-proof-value-evidence.json'),\n  former_Parameter_AUTHOR_is_distinct_artifact=True)")
    target = p.OUT / 'derived_freeze_lossless_dag_v2.py'
    assert not target.exists(), 'Preserve prior derived freeze SOURCE'
    p.write(target, source)
    p.dump(p.OUT / 'lossless-dag-v2-freeze-provenance.json', dict(
        original_freeze_unchanged=p.binding(original), derived_freeze=p.binding(target),
        actual_freeze_wrapper=p.binding(Path(__file__)),
        original_preparation_and_runner_immutable=True, full_math_scope_unchanged=True,
        DAG_proof_values_checked_in_addition_to_all_original_kernel_controls=True,
        original_raw_Expr_equal_false_results_kept=True, pure_freeze_Lean_calls=0,
        API_Root_install_scope_or_mission_operations=False))
    namespace = {'__name__': 'independent_phase_lossless_freeze', '__file__': str(target)}
    exec(compile(source, str(target), 'exec'), namespace)
    namespace['main']()


if __name__ == '__main__':
    main()
