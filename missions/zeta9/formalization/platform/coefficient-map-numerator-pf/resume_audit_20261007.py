"""Pure resumed-author byte audit. No subprocess and no Lean execution."""
from pathlib import Path
import json, sys
sys.dont_write_bytecode = True
import prepare as p
import execute_oracles as e

EXPECTED_PREPARATION = '2dddbef40532b0a7c423fae9d310423456ce4d2f2562223b95edff1869eea606'

def main():
    assert p.sha(p.OUT/'preparation-verification.json') == EXPECTED_PREPARATION
    state = e.gate()
    receipt = p.load(p.OUT/'compile-receipt.json')
    checked = {}
    def check(binding):
        assert binding is not None
        path = p.TASK/binding['task_relative']
        assert path.resolve().is_relative_to(p.ROOT.resolve())
        if binding['task_relative'] not in checked:
            assert path.stat().st_size == binding['bytes']
            assert p.sha(path) == binding['sha256'], str(path)
            checked[binding['task_relative']] = binding
        else:
            assert checked[binding['task_relative']] == binding
        return path
    records = []
    for row in receipt['rows']:
        assert row['cwd'] == str(p.PROJECT)
        assert row['command'][:5] == ['lake','env','python','lean_call.py','lean']
        for binding in row['input_bindings'] + row['output_bindings']:
            check(binding)
        for key in ['stdout','stderr','log','exit_file','selected_paths']:
            check(row[key])
        assert int(check(row['exit_file']).read_text().strip()) == row['exit_code']
        assert check(row['log']).read_bytes() == check(row['stdout']).read_bytes() + check(row['stderr']).read_bytes()
        for original, retained in [('input_bindings','retained_input_bindings'),('output_bindings','retained_output_bindings')]:
            assert len(row[original]) == len(row[retained])
            for live, kept in zip(row[original], row[retained]):
                assert live['task_relative'] == kept['original_task_relative']
                assert check(live).read_bytes() == check(kept['snapshot_binding']).read_bytes()
        selected = p.load(check(row['selected_paths']))
        for key in ['LEAN_PATH','LEAN_SRC_PATH']:
            assert selected[key]['filtered']
            assert all(Path(raw).resolve().is_relative_to(p.PROJECT.resolve()) or
                       Path(raw).resolve().is_relative_to((p.ROOT/'.lake/packages').resolve())
                       for raw in selected[key]['filtered'])
        assert row['actual_executor_sha256'] == p.sha(p.OUT/'execute_oracles.py')
        assert row['exit_code'] == 0 and not row['failure_retained']
        records.append(dict(label=row['label'],attempt=row['attempt'],exit_code=row['exit_code'],
                            own_output_files=[b['task_relative'] for b in row['output_bindings']]))
    latest = {r['label']:r for r in receipt['rows']}
    initial = ['toolchain'] + ['build-native-'+r['parser_name'] for r in state['native_sources']] + \
              ['native-control-'+r['module'] for r in state['native_controls']] + ['stage1-extract'] + \
              ['stage2-'+r['parser_name'] for r in state['native_sources']] + ['stage2-header'] + \
              ['build-parent-'+r['module'].rsplit('.',1)[1] for r in state['parent_definitions']
               if r['module'] != 'Definitions.Def_ZetaNine_HarmonicStability']
    assert len(initial) == 43 and all(label in latest for label in initial)
    graph = e.rows(p.OUT/'decl_graph.jsonl')
    provenance = p.load(p.OUT/'integration-provenance.json')
    assert len(graph) == provenance['graph_records'] == 545
    assert len(provenance['PF_proof_names']) == 18 and len(provenance['parent_helper_names']) == 16
    assert len(provenance['new_definition_names']) == 5
    assert provenance['source_sha256'] == p.SOURCE_SHA
    plan = p.load(p.OUT/'target-plan.json')
    expected = [('build-definition',plan['local_definition'])]
    expected += [('build-'+str(i)+'-'+kind,r['local_'+kind])
                 for i,r in enumerate(plan['targets']) for kind in ['solution','reference']]
    staging = []
    missing = []
    for label, relative in expected:
        own = p.PROJECT/relative
        staged = p.OUT/'staged'/relative
        assert own.read_bytes() == staged.read_bytes()
        status = dict(label=label,relative=relative,own_input=p.binding(own),staged_input=p.binding(staged),
                      retained_actual_success=label in latest)
        if label not in latest:
            obj = 'b/lib/lean/'+relative.removesuffix('.lean')+'.olean'
            status['next_arguments'] = ['-o',obj,relative]
            assert not (p.PROJECT/obj).exists()
            missing.append(status)
        staging.append(status)
    assert len(receipt['rows']) == 54 and len(latest) == 54
    assert [row['label'] for row in missing] == ['build-2-reference']
    report = dict(role='Continued same platform AUTHOR batch; pure byte audit only',
                  Lean_executed=False,new_independent_review_claimed=False,author_PASS_claimed=False,
                  preparation_sha256=EXPECTED_PREPARATION,preparation_bindings=80,
                  native_reports_reverified=True,receipt=p.binding(p.OUT/'compile-receipt.json'),
                  actual_receipt_rows=len(records),prior_initial_calls_reused=43,
                  all_actual_rows_exit_zero=True,unique_receipt_bound_files=len(checked),
                  records=records,staging=staging,missing_actual_calls=missing,
                  pending_author_controls=['exact forall endpoint types','all proof and private helper types and standard axioms',
                    'full definition types and values: raw expression equality and kernel isDefEq',
                    'whole function rfl for all five included definitions','closed native/staged boundary controls',
                    'resolver/path checks and final hash freeze'],
                  next_command_requires_new_Root_lane1_grant=True,
                  byte_bound_files=list(checked.values()))
    p.dump(p.OUT/'resume-audit-2026-10-07.json',report)
    print(json.dumps({k:v for k,v in report.items() if k not in ['records','staging','byte_bound_files']},ensure_ascii=False))

if __name__ == '__main__': main()
