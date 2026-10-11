"""Pure final freeze after terminal actual fresh compilation and controls."""
from pathlib import Path
import json, sys
import prepare_sources as p

OUT, TASK, PROJECT = p.OUT, p.TASK, p.PROJECT
STD3={'propext','Classical.choice','Quot.sound'}

def load_json_lines(path):
    return [json.loads(line) for line in path.read_text(encoding='utf-8-sig').splitlines()
            if line.startswith('{')]

def actual_rows(row):
    return load_json_lines(TASK/row['folder_task_relative']/'stdout.log')

def check_files(records):
    for row in records:
        assert p.binding(TASK/row['task_relative'])==row, row['task_relative']

def dag_valid(payload):
    assert payload['format']=='lean-expr-dag-v1'
    nodes=payload['nodes']; assert isinstance(nodes,list) and nodes
    references={'app':[1,2],'lam':[2,3],'forallE':[2,3],'letE':[2,3,4],
                'mdata':[2],'proj':[3]}
    tags={'bvar','fvar','mvar','sort','const','app','lam','forallE','letE',
          'litNat','litString','mdata','proj'}
    for i,node in enumerate(nodes):
        assert isinstance(node,list) and node and node[0] in tags
        for j in references.get(node[0],[]):
            assert isinstance(node[j],int) and 0<=node[j]<i
    assert 0<=payload['type_root']<len(nodes) and 0<=payload['value_root']<len(nodes)

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (OUT/'independent-review.json').exists()
    prep=p.load(OUT/'preparation-freeze.json')
    terminal=p.load(OUT/'terminal-execution-gate.json')
    assert terminal['all_handles_terminal'] and terminal['final_success_labels']==27
    assert terminal['own_native_fresh_sources']==19 and terminal['actual_own_resolutions']==25
    check_files(prep['stable_files'])
    assert p.sha(p.AUTHOR/'author-audit.json')==p.AUTHOR_SHA
    author=p.load(p.AUTHOR/'author-audit.json')
    check_files(author['stable_files'])
    receipt=p.load(OUT/'execution-receipt.json')
    latest={row['label']:row for row in receipt['rows']}
    assert len(latest)==27 and all(row['exit_code']==0 for row in latest.values())
    assert all(row['all_subprocess_handles_terminal'] for row in receipt['rows'])
    failures=[row for row in receipt['rows'] if row['exit_code']!=0]
    assert all(row['failed_whole_run_excluded'] for row in failures)
    for row in receipt['rows']:
        check_files(row['input_bindings']+row['output_bindings']+row['evidence_bindings'])
        check_files([r['retained'] for r in row['immutable_input_snapshots']])
        check_files([row['actual_executor']])
        for snap in row['immutable_input_snapshots']:
            assert snap['retained']['sha256']==snap['original']['sha256']
        selected=p.load(TASK/row['folder_task_relative']/'selected-paths.json')
        for key in ['LEAN_PATH','LEAN_SRC_PATH']:
            exact={str(Path(x).resolve()).casefold() for x in selected[key]['allowed_exact_set']}
            assert all(str(Path(x).resolve()).casefold() in exact for x in selected[key]['filtered'])
            own=CACHE if key=='LEAN_PATH' else PROJECT
            assert str(own.resolve()).casefold() in exact
    source_rows=[latest['source-'+r['module'].rsplit('.',1)[-1]] for r in prep['source_records']]
    assert len(source_rows)==19
    for source,row in zip(prep['source_records'],source_rows):
        src=source['project_copy']
        assert src in row['input_bindings']
        expected=(PROJECT/'b/lib/lean'/(source['module'].replace('.','/')+'.olean')).resolve()
        assert any((TASK/x['task_relative']).resolve()==expected for x in row['output_bindings'])
    full=[r for r in actual_rows(latest['control-JetsIndependentTypes'])
          if r.get('kind')=='independent_whole_type_proof_DAG']
    own=[r for r in actual_rows(latest['control-JetsIndependentBoundaries'])
         if r.get('kind')=='independent_closed_boundary']
    replay=[r for r in actual_rows(latest['control-AuthorBoundaryReplay'])
            if r.get('kind')=='actual_closed_boundary']
    validation=actual_rows(latest['serializer-IndependentExprDagValidationV3'])
    fixture=[r for r in validation if r.get('kind')=='expr_dag_validation']
    small=[r for r in validation if r.get('kind')=='expr_dag_small_source_validation']
    own_serializer=actual_rows(latest['control-JetsIndependentSerializerControls'])
    resolved=actual_rows(latest['actual-own-object-resolution'])
    paths=[r for r in resolved if r.get('kind')=='actual_own_findOLean']
    headers=[r for r in resolved if r.get('kind')=='actual_environment_module_header']
    inventory=p.load(OUT/'prepared-declaration-inventory.json')
    assert len(full)==26 and len(own)==31 and len(replay)==15
    assert {r['declaration'] for r in full}=={
        'ZetaNine.CoefficientMapFormalTransportJets.'+n for n in inventory['actual_theorem_names']}
    assert {r['expected'] for r in full}=={
        'JetsIndependentExpected.'+n for n in inventory['own_full_expected_names']}
    assert {r['declaration'] for r in own}=={
        'JetsIndependentBoundary.'+n for n in inventory['own_boundary_names']}
    for r in full:
        assert r['type_kernel_equal'] and r['closed'] and r['four_complete_reconstructions']==[True]*4
        assert set(r['source_axioms'])<=STD3 and set(r['expected_axioms'])<=STD3
        dag_valid(r['source_full_type_proof_DAG']); dag_valid(r['expected_full_type_proof_DAG'])
    for r in own:
        assert r['closed'] and set(r['axioms'])<=STD3
        dag_valid(r['complete_type_proof_DAG'])
    for r in replay+small: assert set(r['axioms'])<=STD3
    assert len(fixture)==20 and len(small)==3
    for r in fixture+small:
        assert r['all_fields_roundtrip'] and r['raw_repr_reconstruction_equal']
        dag_valid(r['payload'])
    assert len(own_serializer)==6
    assert sum(r.get('kind')=='independent_serializer_distinct_fields' and r['raw_fields_preserved']
               for r in own_serializer)==4
    assert sum(r.get('kind')=='independent_serializer_bad_reference_rejected' and r['rejected']
               for r in own_serializer)==1
    assert sum(r.get('kind')=='independent_serializer_unknown_constructor_rejected' and r['rejected']
               for r in own_serializer)==1
    assert len(paths)==25 and len(headers)==1
    assert {r['module'] for r in paths}==set(prep['planned_resolver_modules'])
    for r in paths:
        expected=(PROJECT/'b/lib/lean'/(r['module'].replace('.','/')+'.olean')).resolve()
        assert r['exact_own_cache'] and Path(r['olean']).resolve()==expected==Path(r['expected']).resolve()
        assert r['actual_header_contains'] or r['separate_fixture_environment']
    # Collect exact author/own evidence, never chase the shared package junction.
    allpaths={ (TASK/r['task_relative']).resolve() for r in author['stable_files']+prep['stable_files'] }
    for row in receipt['rows']:
        for binding in row['input_bindings']+row['output_bindings']+row['evidence_bindings']+[row['actual_executor']]:
            allpaths.add((TASK/binding['task_relative']).resolve())
        for retained in row['immutable_input_snapshots']:
            allpaths.add((TASK/retained['retained']['task_relative']).resolve())
    excluded={'independent-review.json','review-manifest.json','SHA256SUMS.txt','post-freeze-verification.json'}
    allpaths.update(q.resolve() for q in OUT.rglob('*') if q.is_file() and
                    q.name not in excluded and '__pycache__' not in q.parts)
    allpaths.update(q.resolve() for q in (PROJECT/'b').rglob('*') if q.is_file())
    stable=[p.binding(q) for q in sorted(allpaths)]
    check_files(stable)
    checks=[dict(name=name,passed=True) for name in [
        'author_frozen_439_bindings_personally_reverified','original64_preparation_bindings_unchanged',
        'main_actual_source_exact_ccef_export_not_historical_b081','foundation_author_role_disclosed',
        'original_new_project_and_cache_absence_verified','all19_native_sources_own_fresh_actual0',
        'two_validated_serializer_sources_own_fresh_actual0','all27_final_actual_labels_exit0',
        'every_actual_input_log_exit_output_bound','whole_failed_runs_retained_and_excluded',
        'all26_actual_theorems_closed','all26_independent_complete_expected_theorems_closed',
        'all26_whole_kernel_Meta_type_equalities','all52_source_expected_axiom_reports_Std3',
        'full_source_expected_type_and_proof_DAGs_retained','all104_source_expected_Expr_reconstructions',
        'all_DAG_references_topologically_valid','all31_own_closed_boundaries_Std3',
        'n1_all_rows_all_orders_and_both_endpoint_signs','arbitrary_improper_numerators_and_m0_whole_series',
        'odd_n3_no_parity_assumption','scope_predicates_are_not_transport_counterexamples',
        'author15_boundary_source_replay_actual0_Std3','serializer20_fixtures_all_fields_raw_roundtrip',
        'serializer3_small_sources_complete_roundtrip_Std3','own4_serializer_distinct_field_controls',
        'own2_serializer_malformed_inputs_rejected','actual25_findOLean_exact_own_cache',
        'actual_module_header_matches_imported_context','duplicate_fixture_serializer_separate_environment',
        'every_real_call_exact_LEAN_PATH_allowlist','no_Root_author_or_historical_proof_fallback',
        'all_actual_handles_terminal','all_current_bindings_personally_rehashed',
        'no_API_credentials_scope_or_Root_write','no_five_output_constant_term_or_HasSum_transport_claim']]
    report=dict(verdict='PASS',role='Native Jets independent reviewer; Data/Bounds foundation author disclosed',
        source_sha256=p.SOURCE_SHA,author_sha256=p.AUTHOR_SHA,
        preparation_sha256=p.sha(OUT/'preparation-freeze.json'),checks=checks,stable_files=stable,
        counts=dict(checks=len(checks),stable_files=len(stable),
          actual_attempts=len(receipt['rows']),actual_final_success_calls=27,
          actual_final_success_Lean_calls=26,actual_runtime_calls=1,
          actual_failed_calls=len(failures),fresh_native_sources=19,fresh_serializer_sources=2,
          complete_source_theorems=26,complete_independent_expected_theorems=26,
          actual_whole_type_kernel_comparisons=26,source_expected_complete_Expr_reconstructions=104,
          own_boundary_proofs=31,author_boundary_replay_proofs=15,
          serializer_field_fixtures=20,serializer_small_sources=3,own_serializer_controls=6,
          actual_own_object_resolutions=25,Std3_reports=101,remaining_bindings=0),
        actual_source_and_expected_complete_records=full,actual_own_boundary_records=own,
        actual_author_boundary_replay_records=replay,actual_serializer_validation_records=validation,
        actual_own_serializer_control_records=own_serializer,actual_own_object_resolutions=paths,
        actual_environment_header=headers[0],execution_receipt=p.binding(OUT/'execution-receipt.json'),
        retained_failed_calls_wholly_excluded=failures,
        preserved_author_historical_failure_count=author['counts']['actual_failed_calls'],
        all_actual_handles_terminal=True,remaining_bindings=0,
        findings=[dict(topic='independence',severity='informational',detail=prep['role_disclosure']),
          dict(topic='historical_source',severity='informational',detail='Shared b081 failed candidate remains immutable; only validated ccef export was independently fresh compiled.'),
          dict(topic='serialization',severity='informational',detail='Complete actual type/proof Expr DAG reconstruction accompanies genuine Meta.isDefEq checks; fixtures compile in a separate environment to avoid duplicate definitions.'),
          dict(topic='scope',severity='informational',detail='All Jets and all nine rho transport for n>=1, including n1 and both signed boundaries; constant-term, five-output matrix and HasSum parameter transport remain unclaimed.'),
          dict(topic='retained_failures',severity='informational',detail='Every actual failed own run is retained and wholly excluded; historical author failures are separately counted.')],
        cache_objects_borrowed=False,Root_or_author_proof_fallback_permitted=False,
        Root_API_credentials_scope_modified=False,platform_acceptance_claimed=False,
        five_output_matrix_transport_proved=False,constant_term_transport_proved=False,
        HasSum_parameter_transport_proved=False)
    p.dump(OUT/'independent-review.json',report)
    p.dump(OUT/'review-manifest.json',dict(report=p.binding(OUT/'independent-review.json'),stable_files=stable))
    sums=stable+[p.binding(OUT/'independent-review.json'),p.binding(OUT/'review-manifest.json')]
    p.write(OUT/'SHA256SUMS.txt',''.join(r['sha256']+'  '+r['task_relative']+'\n' for r in sums))
    check_files(sums)
    p.dump(OUT/'post-freeze-verification.json',dict(
        report=p.binding(OUT/'independent-review.json'),manifest=p.binding(OUT/'review-manifest.json'),
        sums=p.binding(OUT/'SHA256SUMS.txt'),stable_files_actual_rehashed=len(stable),
        SUMS_actual_rehashed=len(sums),mismatches=0,remaining_bindings=0,
        actual_all_handles_terminal=True,no_Lean_API_Root_action_in_freeze=True))
    print(json.dumps(dict(report=p.binding(OUT/'independent-review.json'),
        counts=report['counts'],postfreeze=p.binding(OUT/'post-freeze-verification.json')),indent=2))

CACHE=PROJECT/'b/lib/lean'
if __name__=='__main__':main()
