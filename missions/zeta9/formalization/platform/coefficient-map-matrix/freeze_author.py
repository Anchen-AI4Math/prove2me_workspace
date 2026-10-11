"""Evidence-only Matrix author gate. Never invokes Lean, installs, or publishes."""
from pathlib import Path
import hashlib,json,os,re,sys
import prepare as p
import execute_oracles as e
import author_stage as s

OUT,TASK,ROOT,PROJECT,NS=p.OUT,p.TASK,p.ROOT,p.PROJECT,p.NS
checks=[]


def check(name,condition,evidence=None):
    checks.append(dict(name=name,**{'pass':bool(condition)},evidence=evidence))
    if not condition:
        number=1+len(list(OUT.glob('retained-author-gate-failure-*.json')))
        p.dump(OUT/('retained-author-gate-failure-'+str(number).zfill(2)+'.json'),
            dict(failed_check=name,checks=checks,excluded_from_success_evidence=True))
        raise AssertionError(name)


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (OUT/'author-audit.json').exists()
    state=e.gate();c=s.context();prov=p.load(OUT/'integration-provenance.json')
    receipt=p.load(OUT/'compile-receipt.json');latest={row['label']:row for row in receipt['rows']}
    check('all_final_81_actual_calls_zero',len(latest)==81 and all(row['exit_code']==0 for row in latest.values()),
        dict(unique_successes=len(latest),actual_attempts=len(receipt['rows']),
            historical_failed_attempts=sum(row['exit_code']!=0 for row in receipt['rows'])))
    for row in receipt['rows']:
        for key in ['log','stdout','stderr','exit_file','selected_paths']:
            binding=row[key];path=TASK/binding['task_relative']
            assert path.stat().st_size==binding['bytes'] and p.sha(path)==binding['sha256']
        for key in ['retained_input_bindings','retained_output_bindings']:
            assert len(row[key])==len(row[key.removeprefix('retained_')])
            for old,snapshot in zip(row[key.removeprefix('retained_')],row[key]):
                bound=snapshot['snapshot_binding'];path=TASK/bound['task_relative']
                assert old['task_relative']==snapshot['original_task_relative']
                assert path.stat().st_size==old['bytes']==bound['bytes'] and p.sha(path)==old['sha256']==bound['sha256']
    check('every_actual_log_exit_input_output_and_historical_snapshot_fixed',True)
    check('actual_failed_reference_and_two_python_preparation_failures_retained',
        any(row['label']=='build-1-reference' and row['exit_code']==1 for row in receipt['rows'])
        and all((OUT/('retained-preparation-attempt-'+str(n).zfill(2))/'failure.json').exists() for n in [1,2]))
    paths=[p.load(TASK/row['selected_paths']['task_relative']) for row in receipt['rows']]
    check('own_short_cache_package_only_search_paths_no_Root_proof_fallback',
        not receipt['cache_objects_borrowed'] and not receipt['Root_proof_fallback_permitted']
        and all(all(Path(raw).resolve().is_relative_to(PROJECT.resolve()) or
            Path(raw).resolve().is_relative_to((ROOT/'.lake/packages').resolve())
            for raw in doc['LEAN_PATH']['filtered']+doc['LEAN_SRC_PATH']['filtered']) for doc in paths))
    check('73_original_pure_preparation_files_preserved',
        len(p.load(OUT/'preparation-verification.json')['files'])==73)
    check('all_actual_paths_plus64_fit_windows',all(row['passed'] and row['path_plus_64']<=259 for row in state['path_checks']),
        dict(maximum=max(row['path_plus_64'] for row in state['path_checks'])))
    normalization=p.load(OUT/'parser-input-normalization.json')
    check('actual_parser_input_offsets_with_explicit_CRLF_normalization',len(normalization['records'])==13
        and all(row['only_CRLF_to_LF'] for row in normalization['records'])
        and sum(not row['identical_bytes'] for row in normalization['records'])==1)
    check('actual_graph_415_Matrix22_5defs_17proofs_and_project70defs',
        len(c['graph'])==prov['graph_records']==415 and len(c['core'])==22
        and prov['source_defs']==5 and prov['source_proofs']==17 and len(c['definition_names'])==70)
    check('real_data_value_edges_only_actual_aggregate_inverse_and_selected_output',
        set(prov['actual_definition_valueDeps']['actualFMatrix'])=={'ZetaNine.CoefficientMapAggregate.aggregate'}
        and set(prov['actual_definition_valueDeps']['selectedIntegerMultiplier'])=={
            NS+'.selectedIntegerOutput','ZetaNine.CoefficientMapKernelBridge.inverseMultiplier'}
        and all(prov['actual_definition_valueDeps'][name]==[] for name in ['selectionMatrix','selectedIntegerPair','selectedIntegerOutput']))
    check('169_parent_helpers_and_all17_original_proofs_preserved_per_Solution',
        len(c['helpers'])==len(prov['inline_helper_facts'])==169 and prov['proof_records_per_solution']==187
        and prov['new_external_theorem_boundaries']==[])
    check('exact_actual_source_spans_and_closed_proof_closure',prov['statement_proof_spans_from_actual_parser_only']
        and all(prov['targets'][NS+'.'+name]['extra_hypotheses']==[] for name in p.TARGETS))
    kernel=[];rfl=[]
    for environment,label in [('native','native-value-comparison'),('staged','staged-value-comparison')]:
        records=e.rows(OUT/(label+'.log'))
        full=[row for row in records if row['kind']=='whole_definition_kernel_equality']
        closed=[row for row in records if row['kind']=='whole_function_rfl']
        check(environment+'_five_genuine_whole_type_value_kernel_equalities',len(full)==5
            and {row['declaration'] for row in full}=={NS+'.'+name for name in p.DEFS}
            and all(row['type_kernel_equal'] and row['full_value_kernel_equal']
                and row['original_value_expression_repr'] and row['alias_value_expression_repr']
                and set(row['axioms'])<=p.STD for row in full))
        check(environment+'_five_closed_whole_function_rfl_proofs',len(closed)==5
            and all(set(row['axioms'])<=p.STD for row in closed))
        kernel += [dict(row,environment=environment) for row in full]
        rfl += [dict(row,environment=environment) for row in closed]
    aliases=(OUT/'NativeValueComparisonDefinition.lean').read_bytes()
    staged=(OUT/'StagedValueComparisonDefinition.lean').read_bytes()
    check('shared_alias_program_differs_only_by_genuine_import',aliases.replace(
        ('import '+p.NATIVE).encode(),('import '+s.DEF_PATH.removesuffix('.lean').replace('/','.')).encode())==staged)
    original={row['label']:row for row in e.rows(OUT/'types-original.log')}
    contexts=['types-definition']+['types-'+str(i)+'-'+kind for i in range(3) for kind in ['solution','reference']]
    reports={label:{row['label']:row for row in e.rows(OUT/(label+'.log'))} for label in contexts}
    comparisons=[];differences=[]
    proof_bearing_parents={'ZetaNine.CoefficientMapAggregate.aggregateLinearMap',
        'ZetaNine.CoefficientMapAggregate.coordinateLinearMap',
        'ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap',
        'ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv'}
    for name in c['definition_names']:
        old=original[name]
        for context,records in reports.items():
            row=records[name];same=old['value']==row['value']
            canonical=row['value']==reports['types-definition'][name]['value']
            comparisons.append(dict(declaration=name,context=context,type_equal=old['type']==row['type'],
                value_equal=same or name in proof_bearing_parents and canonical,
                native_pretty_value_equal=same,canonical_staged_value_equal=canonical,
                axioms=row['axioms']))
            if not same:differences.append(dict(declaration=name,context=context,
                original_value=old['value'],staged_value=row['value'],
                evidence_basis='Fixed existing actual parent Definition value/kernel evidence; no new Matrix proof field'))
    check('all490_definition_types_and_canonical_values_in_seven_contexts',len(comparisons)==490
        and all(row['type_equal'] and row['value_equal'] and set(row['axioms'])<=p.STD for row in comparisons))
    check('all35_Matrix_values_exact_and_parent_proof_differences_explicit',
        all(row['native_pretty_value_equal'] for row in comparisons if row['declaration'].startswith(NS+'.'))
        and all(row['declaration'] in proof_bearing_parents for row in differences),
        dict(raw_parent_proof_value_differences=len(differences),new_Matrix_proof_fields=0))
    targets=[]
    plan=p.load(OUT/'target-plan.json')
    for i,target in enumerate(plan['targets']):
        name=target['theorem_name'];o=original[name];sol=reports['types-'+str(i)+'-solution'][name];ref=reports['types-'+str(i)+'-reference'][name]
        wrapper=reports['types-'+str(i)+'-solution']['solution']
        targets.append(dict(theorem=name,actual_original_type=o['type'],solution_type=sol['type'],
            reference_type=ref['type'],wrapper_type=wrapper['type'],original_axioms=o['axioms'],
            solution_axioms=sol['axioms'],wrapper_axioms=wrapper['axioms'],reference_axioms=ref['axioms']))
    check('three_full_native_checked_reference_wrapper_types_equal',all(row['actual_original_type']==
        row['solution_type']==row['reference_type']==row['wrapper_type'] for row in targets))
    check('all_complete_target_and_wrapper_proofs_only_standard_three',all(set(row['original_axioms'])==
        set(row['solution_axioms'])==set(row['wrapper_axioms'])==p.STD for row in targets))
    check('reference_statement_only_stubs_explicit_sorryAx',all('sorryAx' in row['reference_axioms'] for row in targets))
    proof_records=[e.rows(OUT/('proofs-'+str(i)+'.log')) for i in range(3)]
    check('all561_complete_helper_Matrix_wrapper_axiom_records_closed',all(len(records)==187
        and all(set(row['axioms'])<=p.STD for row in records) for records in proof_records))
    control=p.load(OUT/'stage-control-provenance.json')
    check('14_actual_control_parsers_headers_and_source_span_replays',len(control['records'])==6
        and control['actual_parser_and_header_invocations']==8 and control['actual_staged_control_invocations']==6
        and all(row['no_new_mathematical_hypotheses'] and row['quoted_Name_data_are_not_claimed_as_resolved_term_refs'] for row in control['records']))
    expected=[]
    for i in range(3):
        records=e.rows(OUT/('stage-control-'+str(i)+'-expected.log'))
        whole=[row for row in records if row.get('kind')=='actual_whole_type_kernel_comparison']
        closed=[row for row in records if 'declaration' in row and 'axioms' in row]
        check('Solution'+str(i)+'_17_actual_whole_type_kernel_checks_and22_closed_expected_proofs',
            len(whole)==17 and all(row['type_kernel_equal'] for row in whole)
            and len(closed)==22 and all(set(row['axioms'])<=p.STD for row in closed))
        expected.extend(whole)
    boundary=e.rows(OUT/'stage-control-2-boundary.log')
    check('26_genuine_native_boundary_proofs_replayed',len(boundary)==26
        and all(set(row['axioms'])<=p.STD for row in boundary))
    diagnostics={}
    for label,count in [('author-endpoint',12),('author-source',22)]:
        text=(OUT/('stage-control-2-'+label+'.log')).read_text(encoding='utf-8-sig')
        extracted=re.findall(r'depends on axioms: \[([^\]]*)\]',text,re.S)
        diagnostics[label]=extracted
        check('actual_'+label+'_original_printed_axioms_replayed',len(extracted)==count
            and all('sorryAx' not in row and all(name.split('.{')[0].strip() in p.STD
                for name in row.split(',') if name.strip()) for row in extracted))
    resolved=e.rows(OUT/'resolution-audit.log')
    check('actual_all_33_native_parent_Matrix_Solution_Ref_alias_objects_resolve_own_cache',
        len(resolved)==33 and all(Path(row['olean']).resolve()==
            (PROJECT/'b/lib/lean'/(row['module'].replace('.','/')+'.olean')).resolve() for row in resolved),resolved)
    request=p.load(OUT/'problems-request.json');definition=p.load(OUT/'definitions-request.json')
    check('exact_public_API_payload_shape_and_original_domains',set(request)=={'env','private','problems'}
        and request['env']==p.REV and request['private'] is False and len(request['problems'])==3
        and len(definition)==1 and definition[0]['definition'].encode()==(OUT/'staged'/s.DEF_PATH).read_bytes()
        and all('even n>=2' in row['natural_language_statement'] for row in request['problems'])
        and all(row['formal_statement'].endswith(':= by sorry') for row in request['problems']))
    copy=[]
    for relative in [s.DEF_PATH]+[row['local_'+kind] for row in plan['targets'] for kind in ['solution','reference']]:
        src=OUT/'staged'/relative;dest=ROOT/relative
        assert src.read_bytes()==(PROJECT/relative).read_bytes()
        assert not dest.exists() or p.sha(dest)==p.sha(src)
        copy.append(dict(staged_task_relative=src.relative_to(TASK).as_posix(),root_relative_destination=relative,
            bytes=src.stat().st_size,sha256=p.sha(src),destination_exists_at_author_freeze=dest.exists()))
    check('seven_exact_copyplan_files_no_differing_Root_destination',len(copy)==7)
    p.dump(OUT/'root-copy-plan.json',dict(source_sha256=p.SOURCE_SHA,required_existing_Definitions=state['parent_definitions'],
        files=copy,overwrite_allowed=False,author_scope='task-local author only; Root installs',
        scope_build_entrypoints_for_parent=state['exact_future_scoped_build_entrypoints']))
    artifacts=[p.binding(path) for path in sorted((PROJECT/'b').rglob('*')) if path.is_file()]
    check('own_actual_compiler_artifacts_hash_bound',len(artifacts)>=34)
    limits=['Only original Matrix facts on Even n>=2 and the actual selected rational quartic are proved here.',
        'Integer b,a specify the output; rational inverse coefficients are not claimed integral or height bounded.',
        'Five pure Matrix definitions have ten actual full type/value kernel checks and ten whole-function rfl proofs. Existing proof-bearing parent definitions keep their fixed previously audited full value evidence, with every new actual dependency edge explicit.',
        'Reference statements intentionally contain sorryAx and are excluded from proof evidence. Every complete Solution proof and replayed closed boundary uses only standard axioms.',
        'Historical preparation records retain Lean_executed=false; this new author report describes subsequent real calls. One failed reference and two Python preparation failures remain excluded from success evidence with original bytes retained.',
        'No Root install, independent platform transplantation review, external publication or acceptance is claimed. Formal coefficient transport, integer height, small forms and irrationality remain separate.']
    p.write(OUT/'AUTHOR_README.md','# Actual Matrix platform author\n\n'+ '\n\n'.join(limits)+'\n')
    stable=[path for path in OUT.rglob('*') if path.is_file() and '__pycache__' not in path.parts
        and path.name not in ['author-audit.json','source-manifest.json','SHA256SUMS.txt']
        and 'independent' not in path.relative_to(OUT).parts]
    for directory,dirs,names in os.walk(PROJECT):
        dirs[:]=[name for name in dirs if name not in ['.lake','b','__pycache__']]
        stable.extend(Path(directory)/name for name in names)
    stable=sorted(set(stable));files=[dict(p.binding(path),batch_relative=Path(os.path.relpath(path,OUT)).as_posix()) for path in stable]
    failures=[row for row in receipt['rows'] if row['exit_code']!=0]
    p.dump(OUT/'source-manifest.json',dict(source_sha256=p.SOURCE_SHA,files=files,
        fresh_compiler_cache_bindings=artifacts,retained_failed_actual_runs=failures,
        independent_transplantation_review_claimed=False))
    report=dict(verdict='PASS',role='Matrix platform author; independent transplantation review required',
        source_sha256=p.SOURCE_SHA,native_author_sha256=p.AUTHOR_SHA,native_independent_sha256=p.INDEPENDENT_SHA,
        checks=checks,targets=targets,definition_comparisons=comparisons,
        whole_definition_kernel_comparisons=kernel,whole_function_rfl_records=rfl,
        raw_parent_proof_value_differences=differences,complete_proof_records=proof_records,
        whole_independent_type_kernel_comparisons=expected,boundary_records=boundary,
        original_printed_axiom_diagnostics=diagnostics,stable_files=files,
        actual_invocations=len(receipt['rows']),final_actual_success_invocations=len(latest),
        final_success_Lean_invocations=len(latest)-1,final_success_runtime_invocations=1,
        retained_failed_attempts_excluded=failures,limitations=limits,
        Root_API_credentials_scope_writes=False,root_installed_by_author=False,
        independent_transplantation_review_claimed=False,platform_published=False,platform_accepted=False,
        irrationality_proved=False,integer_inverse_coefficients_proved=False,
        actual_five_output_transport_proved=False)
    p.dump(OUT/'author-audit.json',report)
    frozen=stable+[OUT/'source-manifest.json',OUT/'author-audit.json']
    p.write(OUT/'SHA256SUMS.txt',''.join(p.sha(path)+'  '+Path(os.path.relpath(path,OUT)).as_posix()+'\n' for path in sorted(frozen)))
    for line in (OUT/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
        digest,relative=line.split('  ',1);assert p.sha(OUT/relative)==digest
    print(json.dumps(dict(author_verdict='PASS',checks=len(checks),stable_files=len(files),artifacts=len(artifacts),
        actual_attempts=len(receipt['rows']),final_actual_successes=len(latest),failed_actual_Lean_attempts=len(failures),
        author_sha256=p.sha(OUT/'author-audit.json'),copyplan_sha256=p.sha(OUT/'root-copy-plan.json'),
        manifest_sha256=p.sha(OUT/'source-manifest.json'),SHA256SUMS_sha256=p.sha(OUT/'SHA256SUMS.txt'))))


if __name__=='__main__':main()
