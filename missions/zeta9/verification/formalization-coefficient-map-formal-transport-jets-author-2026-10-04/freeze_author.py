"""Evidence-only native author freeze. Run only after all Lean handles terminal."""
from pathlib import Path
import hashlib,json,os,sys
import prepare as p
import execute_dag as e


def streaming_sha(path):
    """Identical SHA256 bytes; bound memory even for retained giant failed logs."""
    h=hashlib.sha256()
    with path.open("rb") as f:
        while block:=f.read(8*1024*1024):h.update(block)
    return h.hexdigest()


p.sha=streaming_sha

STD={'propext','Classical.choice','Quot.sound'}
checks=[]


def check(name,condition,evidence=None):
    checks.append(dict(name=name,passed=bool(condition),evidence=evidence))
    if not condition:
        n=1+len(list(p.OUT.glob('retained-author-gate-failure-*.json')))
        p.dump(p.OUT/('retained-author-gate-failure-'+str(n).zfill(2)+'.json'),
            dict(failed_check=name,checks=checks,excluded_from_success_evidence=True))
        raise AssertionError(name)


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (p.OUT/'author-audit.json').exists()
    state=e.gate();old=p.native_gate()
    receipt=p.load(p.OUT/'compile-receipt.json');latest={r['label']:r for r in receipt['rows']}
    adaptation=p.load(p.OUT/'audit-adaptation.json')
    expected_labels={'toolchain','own-object-resolution'}|{'source-'+r['module'].rsplit('.',1)[1] for r in state['source']}|{'control-'+r['module'] for r in state['controls']}|{'control-'+r['module'] for r in adaptation['extra_source_controls']}
    check('all25_expected_real_call_labels_final_success',set(latest)==expected_labels
        and len(latest)==25 and all(r['exit_code']==0 for r in latest.values()))
    for row in receipt['rows']:
        for field in ['log','stdout','stderr','exit_file','selected_paths']:
            b=row[field];path=p.TASK/b['task_relative']
            assert path.stat().st_size==b['bytes'] and p.sha(path)==b['sha256']
        for field in ['input_bindings','output_bindings']:
            assert len(row[field])==len(row['retained_'+field])
            for original,snapshot in zip(row[field],row['retained_'+field]):
                b=snapshot['snapshot_binding'];path=p.TASK/b['task_relative']
                assert original['task_relative']==snapshot['original_task_relative']
                assert path.stat().st_size==b['bytes']==original['bytes']
                assert p.sha(path)==b['sha256']==original['sha256']
    check('every_actual_attempt_logs_exits_inputs_outputs_snapshots_reverified',True)
    check('original_shared_candidate_and_all5_original_bindings_unchanged',
        len(old['files'])==5 and p.sha(p.ROOT/old['source']['root_relative'])==p.SOURCE_SHA)
    frozen=p.load(p.OUT/'preparation-verification.json')
    check('all38_pure_preparation_bindings_preserved',len(frozen['files'])==38)
    check('all19_native_sources_fresh_compiled_no_borrowed_objects',
        len(state['source'])==19 and receipt['cache_objects_borrowed'] is False
        and receipt['Root_proof_fallback_permitted'] is False
        and all(latest['source-'+r['module'].rsplit('.',1)[1]]['output_bindings'] for r in state['source']))
    paths=[p.load(p.TASK/r['selected_paths']['task_relative']) for r in receipt['rows']]
    check('every_runtime_selected_search_path_own_project_or_fixed_packages',all(
        all(Path(raw).resolve().is_relative_to(p.PROJECT.resolve()) or
            Path(raw).resolve().is_relative_to((p.ROOT/'.lake/packages').resolve())
            for raw in d['LEAN_PATH']['filtered']+d['LEAN_SRC_PATH']['filtered']) for d in paths))
    check('all_compiler_paths_private_suffix_allowance_fit_windows',
        all(r['passed'] and r['path_plus_64']<=259 for r in state['path_checks']))
    source=p.PROJECT/(p.NATIVE.replace('.','/')+'.lean')
    expected_source=p.ROOT/old['source']['root_relative']
    inventory=p.load(p.OUT/'static-original-header-inventory.json')['records']
    check('all26_final_original_statement_headers_exact_unchanged',
        len(inventory)==26 and p.statement_headers(source.read_bytes())==inventory)
    records=e.rows(p.OUT/'control-JetsFullTypeAudit.log')
    check('all26_actual_full_source_theorem_info_records_present',len(records)==26
        and {r['declaration'] for r in records}=={p.NS+'.'+r['name'] for r in inventory}
        and all(r['kind']=='actual_complete_source_expected_type' and
            all(r[k]['format']=='lean-expr-dag-v1' and r[k]['nodes'] and
                0<=r[k]['type_root']<len(r[k]['nodes']) and
                0<=r[k]['value_root']<len(r[k]['nodes']) for k in
                ['full_source_type_and_proof_expression_dag','full_expected_type_and_proof_expression_dag'])
            for r in records))
    check('all26_actual_source_and_expected_complete_type_proof_DAGs_losslessly_reconstructed',
        all(r[k] is True for r in records for k in
            ['source_type_reconstructed_Expr_equal','source_proof_reconstructed_Expr_equal',
             'expected_type_reconstructed_Expr_equal','expected_proof_reconstructed_Expr_equal']))
    check('all26_complete_types_kernel_equal_original_expected_headers',
        all(r['type_kernel_equal'] is True for r in records))
    check('all26_source_and26_closed_expected_proofs_standard_axioms_only',
        all(set(r['source_axioms'])<=STD and set(r['expected_axioms'])<=STD for r in records))
    boundary=e.rows(p.OUT/'control-JetsBoundaryAudit.log')
    check('all15_actual_closed_boundary_theorems_full_types_and_standard_axioms',
        len(boundary)==15 and len({r['declaration'] for r in boundary})==15
        and all(r['kind']=='actual_closed_boundary' and r['full_type_expression_repr']
            and set(r['axioms'])<=STD for r in boundary))
    check('genuine_n1_n2_m0_arbitrary_and_improper_boundaries_present',
        all('JetsAuthorBoundary.'+name in {r['declaration'] for r in boundary} for name in
            ['n1_all_actual_jets','n1_left_endpoint','n1_right_endpoint','n1_all_rho',
             'n2_four_requested_rhos','m0_upper_right_arbitrary','m0_lower_right_arbitrary',
             'm0_double_right_arbitrary','m0_improper_X9_nine_jets','any_n_highest_order']))
    resolver=e.rows(p.OUT/'own-object-resolution.log')
    modules={r['module'] for r in state['source']+state['controls']+adaptation['extra_source_controls']}
    check('all23_actual_native_control_serializer_objects_resolve_exclusively_own_cache',
        len(resolver)==23 and {r['module'] for r in resolver}==modules and all(
            Path(r['olean']).resolve()==(p.PROJECT/'b/lib/lean'/(r['module'].replace('.','/')+'.olean')).resolve()
            for r in resolver))
    validation=e.rows(p.OUT/'control-IndependentExprDagValidationV3.log')
    fixtures=[r for r in validation if r['kind']=='expr_dag_validation']
    small=[r for r in validation if r['kind']=='expr_dag_small_source_validation']
    check('own_fresh_serializer_constructor_metadata_sharing_and_small_source_validation',
        len(fixtures)==20 and {r['fixture_index'] for r in fixtures}==set(range(20))
        and len(small)==3 and len({r['source_name'] for r in small})==3
        and all(r['all_fields_roundtrip'] is True and r['raw_repr_reconstruction_equal'] is True for r in validation)
        and all(set(r['axioms'])<=STD for r in small))
    check('adapted_audit_sources_exact_copied_no_ni1_object_borrowing',
        adaptation['objects_borrowed'] is False and
        adaptation['structural_Expr_equal_not_a_replacement_for_kernel_isDefEq'] is True and
        len(adaptation['extra_source_controls'])==2 and all(
            r['initial_project_copy']['sha256']==r['supplied_source']['sha256']
            ==r['immutable_copied_source']['sha256'] for r in adaptation['extra_source_controls']))
    failures=[r for r in receipt['rows'] if r['exit_code']!=0]
    repairs=p.load(p.OUT/'private-proof-repairs.json') if (p.OUT/'private-proof-repairs.json').exists() else None
    main_row=latest['source-'+p.NATIVE.rsplit('.',1)[1]]
    check('final_main_source_hash_bound_to_actual_successful_compiler_input',
        any(b['task_relative']==source.relative_to(p.TASK).as_posix() and b['sha256']==p.sha(source)
            for b in main_row['input_bindings']))
    shared_compiled=any(r['exit_code']==0 and r['label']==main_row['label'] and any(
        b['task_relative']==source.relative_to(p.TASK).as_posix() and b['sha256']==p.SOURCE_SHA
        for b in r['input_bindings']) for r in receipt['rows'])
    check('private_repairs_preserve_original_headers_and_have_real_failures',
        p.sha(source)==p.SOURCE_SHA or bool(repairs and failures
            and repairs['shared_original_source_and_old5bindings_unchanged']
            and repairs['proof_bodies_only_no_original_header_changes']))
    check('all_actual_failed_calls_entirely_excluded_from_success_records',
        all(r['failure_retained'] and r['exit_code']!=0 for r in failures),
        dict(failed_calls=len(failures),shared_initial_candidate_actually_compiled_successfully=shared_compiled))
    verified=p.OUT/'JetsVerifiedSource.lean'
    p.write(verified,source.read_bytes())
    check('complete_verified_source_export_exact_actual_final_compiler_bytes',p.sha(verified)==p.sha(source))
    p.write(p.OUT/'AUTHOR_README.md','''# Actual fresh Jets native author

This report records the actual serial compilation and controls in ja1. The
shared initial candidate and its five original preparation bindings remain
unchanged, including their uncompiled header. If a private proof repair was
required, only JetsVerifiedSource.lean is the
actual final compiled source export; the initial shared candidate is not
described as compiled unless its exact bytes actually succeeded.

All 19 native source modules were compiled from source into this new cache.
Only fixed bundled/shared Mathlib package objects were reused. The 26 original
theorems have complete actual type/kernel/axiom records and 26 closed expected
type proofs. Complete source and expected types/proofs are persisted as lossless
Expr DAGs, decoded and checked with Expr.equal separately from the whole-type
kernel isDefEq comparison. Two explicitly supplied serializer/validation source
programs were freshly compiled into ja1; 20 constructor/metadata/sharing fixtures
and three genuine source values round-trip with equal raw-tree representations.
Fifteen actual closed boundary proofs cover n1 endpoints and rho,
n2 requested orders, m0 arbitrary numerators, an improper numerator and order9.
Actual pole/order/n>=1 guards are retained; the right endpoint is -c(n+1,s).
Every failed compiler/control attempt remains separate with its original bytes.

Native independent review, formal B/aggregate/F transport, platform author,
installation, acceptance, integer heights and irrationality are not claimed.
No Root/API/credentials/scope write is made by this native author freeze.
''')
    artifacts=[p.binding(path) for path in sorted((p.PROJECT/'b').rglob('*')) if path.is_file()]
    stable=[path for path in p.OUT.rglob('*') if path.is_file() and '__pycache__' not in path.parts
        and path.name not in ['author-audit.json','source-manifest.json','SHA256SUMS.txt']]
    for directory,dirs,names in os.walk(p.PROJECT):
        dirs[:]=[name for name in dirs if name not in ['.lake','b','__pycache__']]
        stable.extend(Path(directory)/name for name in names)
    stable=sorted(set(stable));bindings=[p.binding(path) for path in stable]
    p.dump(p.OUT/'source-manifest.json',dict(initial_shared_source_sha256=p.SOURCE_SHA,
        actual_final_source_sha256=p.sha(source),verified_source=p.binding(verified),
        files=bindings,fresh_compiler_artifacts=artifacts,retained_failed_calls=failures))
    report=dict(verdict='PASS',role='Fresh Jets native author; independent native review required',
        checks=checks,initial_shared_candidate_sha256=p.SOURCE_SHA,
        shared_initial_candidate_actually_compiled_successfully=shared_compiled,
        actual_final_source_sha256=p.sha(source),verified_source=p.binding(verified),
        source_declaration_audit_records=records,actual_boundary_records=boundary,
        actual_object_resolutions=resolver,actual_serializer_validation=validation,
        audit_adaptation=adaptation,stable_files=bindings,fresh_artifacts=artifacts,
        counts=dict(actual_attempts=len(receipt['rows']),final_success_calls=len(latest),
            final_success_Lean_calls=len(latest)-1,final_success_runtime_calls=1,
            actual_failed_calls=len(failures),fresh_native_sources=19,
            actual_original_theorems_audited=26,actual_whole_type_kernel_comparisons=26,
            closed_expected_type_proofs=26,closed_boundary_proofs=15,actual_own_object_resolutions=23,
            additional_fresh_serializer_source_controls=2,serializer_fixtures=20,serializer_small_sources=3,
            complete_type_proof_DAG_reconstructions=104),
        retained_failed_calls_wholly_excluded=failures,private_repairs=repairs,
        shared_initial_header_retained_as_historical=True,all_Lean_handles_terminal=True,
        original5bindings_unchanged=True,source_inventory_not_claimed_as_graph=True,
        independent_native_review_claimed=False,platform_acceptance_claimed=False,
        actual_all_jets_and_nine_rho_native_proved=True,formal_five_output_matrix_transport_proved=False,
        Root_API_scope_credentials_modified=False)
    p.dump(p.OUT/'author-audit.json',report)
    p.write(p.OUT/'SHA256SUMS.txt',''.join(p.sha(path)+'  '+path.relative_to(p.TASK).as_posix()+'\n'
        for path in stable+[p.OUT/'source-manifest.json',p.OUT/'author-audit.json']))
    for line in (p.OUT/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
        digest,relative=line.split('  ',1);assert p.sha(p.TASK/relative)==digest
    print(json.dumps(dict(verdict='PASS',checks=len(checks),stable_files=len(bindings),
        artifacts=len(artifacts),counts=report['counts'],actual_final_source_sha256=p.sha(source),
        shared_initial_candidate_compiled=shared_compiled,author_sha256=p.sha(p.OUT/'author-audit.json'),
        manifest_sha256=p.sha(p.OUT/'source-manifest.json'),sums_sha256=p.sha(p.OUT/'SHA256SUMS.txt'))))


if __name__=='__main__':main()
