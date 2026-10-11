"""Evidence-only Matrix independent gate. Never invokes Lean, installs, or publishes."""
from pathlib import Path
import hashlib,json,os,re,sys
import prepare as p
import execute_oracles as e
import author_stage as s

PLATFORM_AUTHOR_SHA='c908b981d4fbb5b9c84ec137e829e1a1ac06b382640ef447811208b23bc09f8e'

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
    assert not (OUT/'independent-integration-review.json').exists()
    state=e.gate();c=s.context();prov=p.load(OUT/'integration-provenance.json')
    receipt=p.load(OUT/'compile-receipt.json');latest={row['label']:row for row in receipt['rows']}
    check('all_final_85_actual_calls_zero',len(latest)==85 and all(row['exit_code']==0 for row in latest.values()),
        dict(unique_successes=len(latest),actual_attempts=len(receipt['rows']),
            historical_failed_attempts=sum(row['exit_code']!=0 for row in receipt['rows'])))
    for row in receipt['rows']:
        for key in ['log','stdout','stderr','exit_file','selected_paths']:
            binding=row[key];path=TASK/binding['task_relative']
            assert path.stat().st_size==binding['bytes'] and p.sha(path)==binding['sha256']
        for key in ['retained_input_bindings','retained_output_bindings']:
            if key not in row:
                for b in row[key.removeprefix('retained_')]:
                    q=TASK/b['task_relative'];assert q.stat().st_size==b['bytes'] and p.sha(q)==b['sha256']
                continue
            assert len(row[key])==len(row[key.removeprefix('retained_')])
            for old,snapshot in zip(row[key.removeprefix('retained_')],row[key]):
                bound=snapshot['snapshot_binding'];path=TASK/bound['task_relative']
                assert old['task_relative']==snapshot['original_task_relative']
                assert path.stat().st_size==old['bytes']==bound['bytes'] and p.sha(path)==old['sha256']==bound['sha256']
    check('every_actual_log_exit_input_output_and_historical_snapshot_fixed',True)
    check('all_actual_failed_attempts_retained_and_entire_run_excluded',all(row['failure_retained'] for row in receipt['rows'] if row['exit_code']!=0))
    check('pure_Root_schema_probe_diagnostic_retained_without_Lean_failure',(OUT/'root-schema-01-diagnostic.json').exists())
    paths=[p.load(TASK/row['selected_paths']['task_relative']) for row in receipt['rows']]
    check('own_short_cache_package_only_search_paths_no_Root_proof_fallback',
        not receipt['cache_objects_borrowed'] and not receipt['Root_proof_fallback_permitted']
        and all(all(Path(raw).resolve().is_relative_to(PROJECT.resolve()) or
            Path(raw).resolve().is_relative_to((ROOT/'.lake/packages').resolve())
            for raw in doc['LEAN_PATH']['filtered']+doc['LEAN_SRC_PATH']['filtered']) for doc in paths))
    check('96_original_pure_preparation_files_preserved',
        len(p.load(OUT/'preparation-verification.json')['files'])==96)
    mh=p.load(OUT/'mathlib-head-verification.json')
    check('actual_shared_Mathlib_package_HEAD_matches_fixed_revision',mh['exit_code']==0 and mh['stdout'].strip()==p.REV and mh['Root_writes'] is False and mh['Lean_executed'] is False)
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
                diagnostic_canonical_pretty_value_equal=same or name in proof_bearing_parents and canonical,
                native_pretty_value_equal=same,canonical_staged_value_equal=canonical,
                axioms=row['axioms']))
            if not same:differences.append(dict(declaration=name,context=context,
                original_value=old['value'],staged_value=row['value'],
                evidence_basis='Pretty-print diagnostic only; all complete native/staged values are separately verified with genuine Meta and closed whole-function rfl proofs'))
    check('490_definition_type_and_pretty_print_diagnostics_in_seven_contexts',len(comparisons)==490
        and all(row['type_equal'] and row['diagnostic_canonical_pretty_value_equal'] and set(row['axioms'])<=p.STD for row in comparisons))
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
    full_kernel=[];full_rfl=[]
    for environment in ['native','staged']:
        values=e.rows(OUT/('full-values-'+environment+'.log'))
        ke=[x for x in values if x.get('kind')=='independent_complete_definition_kernel']
        rf=[x for x in values if x.get('kind')=='independent_complete_function_rfl']
        check(environment+'_all70_actual_complete_definition_types_values_including_proof_fields',len(ke)==70
            and {x['declaration'] for x in ke}==set(c['definition_names'])
            and all(x['type_kernel_equal'] and x['full_value_kernel_equal']
              and x['original_type_expression_repr'] and x['alias_type_expression_repr']
              and x['original_complete_value_expression_repr'] and x['alias_complete_value_expression_repr']
              and set(x['axioms'])<=p.STD for x in ke))
        check(environment+'_all70_closed_whole_function_rfl',len(rf)==70
            and all(x['full_type_expression_repr'] and set(x['axioms'])<=p.STD for x in rf))
        full_kernel.extend(dict(x,environment=environment) for x in ke)
        full_rfl.extend(dict(x,environment=environment) for x in rf)
    full_prov=p.load(OUT/'full-parent-value-provenance.json')
    check('all70_aliases_bound_to_own_actual_source_declaration_name_and_open_spans',full_prov['actual_definitions']==70
          and len(full_prov['actual_parser_bound_declarations'])==70
          and all(x['complete_proof_fields_retained'] for x in full_prov['actual_parser_bound_declarations']))
    native_expected=e.rows(OUT/'native-expected-kernel.log')
    native_meta=[x for x in native_expected if x.get('kind')=='actual_whole_type_kernel_comparison']
    native_closed=[x for x in native_expected if 'declaration'in x and 'axioms'in x]
    check('native17_actual_full_expected_type_Meta_and22_closed_expected_proofs',len(native_meta)==17
          and all(x['type_kernel_equal'] and x['actual_full_type_expression'] and x['expected_full_type_expression'] for x in native_meta)
          and len(native_closed)==22 and all(set(x['axioms'])<=p.STD for x in native_closed))
    native_source=e.rows(OUT/'native-control-NativeMatrixIndependentSourceControl.log')
    native_boundary=e.rows(OUT/'native-control-NativeMatrixIndependentBoundaryControl.log')
    check('fresh_native22_full_source_records_and26_original_independent_boundary_proofs',len(native_source)==22
          and all(x['full_type_expression_repr'] and set(x['axioms'])<=p.STD for x in native_source)
          and len(native_boundary)==26 and all(set(x['axioms'])<=p.STD for x in native_boundary))
    allresolved=e.rows(OUT/'own-object-resolution.log')
    module_records=[x for x in allresolved if 'module'in x]
    runtime=[x for x in allresolved if x.get('kind')=='actual_environment']
    check('37_native_control_parent_Matrix_Solution_Reference_alias_objects_actual_findOLean_owncache',len(module_records)==37
          and len({x['module'] for x in module_records})==37
          and all(Path(x['object']).resolve()==(PROJECT/'b/lib/lean'/(x['module'].replace('.','/')+'.olean')).resolve()
                  for x in module_records),module_records)
    names=[x['name'] for x in p.load(PROJECT/'lake-manifest.json')['packages']]
    pk=ROOT/'.lake/packages'
    expected_allowed=dict(LEAN_PATH={(PROJECT/'b/lib/lean').resolve()}|{(pk/n/'.lake/build/lib/lean').resolve() for n in names if (pk/n/'.lake/build/lib/lean').is_dir()},
      LEAN_SRC_PATH={PROJECT.resolve()}|{(pk/n).resolve() for n in names if (pk/n).is_dir()})
    rp=p.load(TASK/latest['own-object-resolution']['selected_paths']['task_relative'])
    check('actual_resolver_runtime_and_exact_allowed_path_sets',len(runtime)==1
          and runtime[0]['Lean_version']=='4.33.1'
          and [Path(x).resolve() for x in runtime[0]['LEAN_PATH'].split(os.pathsep)]==[Path(x).resolve() for x in rp['LEAN_PATH']['filtered']]
          and all({Path(y).resolve() for y in d[k]['allowed_exact_set']}==expected_allowed[k]
            and all(Path(x).resolve() in expected_allowed[k] for x in d[k]['filtered']) for d in paths for k in ['LEAN_PATH','LEAN_SRC_PATH']))
    root_gate=p.execution_gate();root=p.load(TASK/root_gate['Root_freeze']['task_relative'])
    check('Root_exact5_controls7_installed3831_build0_and_old_two_check_errors',root['actual_scoped_build_jobs']==3831
          and root['actual_scoped_build_exit']==0 and root['actual_workspace_check_exit']==1
          and len(root['Root_controls'])==5 and len(root['installed_modules'])==7
          and len(root['preserved_other_task_check_errors'])==2 and root['all_Root_compiler_handles_terminal'])
    check('independent_all13_native_plus18_staged_distinct_sources_actual_fresh_builds',
          sum(x['label'].startswith('build-native-') for x in latest.values())==13
          and sum(x['label'].startswith('build-parent-') for x in latest.values())==11
          and all(latest[label]['exit_code']==0 for label in ['build-definition']+['build-'+str(i)+'-'+k for i in range(3) for k in ['solution','reference']]))
    check('all_real_execution_sessions_terminal_before_final_freeze',p.load(OUT/'execution-completion.json')['all_handles_terminal'])
    check('all_frozen_author1543_and_native517_rehashed_without_borrowed_objects',len(p.load(OUT.parent/'author-audit.json')['stable_files'])==1543 and len(p.load(p.INDEPENDENT/'independent-review.json')['stable_files'])==517)

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
            bytes=src.stat().st_size,sha256=p.sha(src),destination_exists_at_independent_freeze=dest.exists()))
    check('seven_exact_copyplan_files_no_differing_Root_destination',len(copy)==7)
    p.dump(OUT/'root-copy-plan.json',dict(source_sha256=p.SOURCE_SHA,required_existing_Definitions=state['parent_definitions'],
        files=copy,overwrite_allowed=False,author_scope='task-local independent reviewer; installed Root bytes verified read-only',
        scope_build_entrypoints_for_parent=state['exact_future_scoped_build_entrypoints']))
    artifacts=[p.binding(path) for path in sorted((PROJECT/'b').rglob('*')) if path.is_file()]
    check('own_actual_compiler_artifacts_hash_bound',len(artifacts)>=34)
    limits=['Independent transplantation: 13 native and 18 additional staged sources were personally compiled in the initially empty mt1 proof cache. Only fixed Mathlib package caches are shared.',
        'All 70 complete original source definition values, including proof fields, have 140 genuine whole-type/value Meta comparisons and 140 closed whole-function rfl proofs in separate native/staged environments.',
        'Only original Matrix facts on Even n>=2 and the actual selected rational quartic are proved here.',
        'Integer b,a specify the output; rational inverse coefficients are not claimed integral or height bounded.',
        'Five pure Matrix definitions additionally have ten actual whole-value Meta comparisons and ten closed rfl proofs. The 490 pretty-print comparisons and every raw difference are diagnostics; complete value equality comes from actual kernel/rfl execution.',
        'Reference statements intentionally contain sorryAx and are excluded from proof evidence. Every complete Solution proof and replayed closed boundary uses only standard axioms.',
        'Historical pure preparation remains Lean_executed=false. This new independent report binds subsequent real executions; every failed actual run is excluded in its entirety, including any partial output or sorryAx records. A read-only Root schema probe diagnostic is separate from Lean/mathematical failures.',
        'Parent Root installed the seven identical modules and independently completed the scoped 3831-job build. The workspace check retains exactly two pre-existing unassigned Tao files from another task. No API, credential, Root, scope, publication or acceptance action was performed by this reviewer. Formal five-output coefficient transport, integer height, small forms and irrationality remain separate.']
    p.write(OUT/'INDEPENDENT_README.md','# Actual Matrix platform independent review\n\n'+ '\n\n'.join(limits)+'\n')
    stable=[path for path in OUT.rglob('*') if path.is_file() and '__pycache__' not in path.parts
        and path.name not in ['independent-integration-review.json','source-manifest.json','SHA256SUMS.txt']
        and 'independent' not in path.relative_to(OUT).parts]
    for directory,dirs,names in os.walk(PROJECT):
        dirs[:]=[name for name in dirs if name not in ['.lake','b','__pycache__']]
        stable.extend(Path(directory)/name for name in names)
    stable.extend(TASK/x['task_relative'] if 'task_relative'in x else ROOT/x['root_relative'] for x in root['Root_controls'])
    stable.extend(ROOT/x['root_relative'] if 'root_relative'in x else TASK/x['task_relative'] for x in root['installed_modules'])
    stable.append(TASK/root_gate['Root_freeze']['task_relative'])
    stable.append(OUT.parent/'author-audit.json')
    stable.append(OUT.parent/'root-copy-plan.json')
    stable.append(p.INDEPENDENT/'independent-review.json')
    stable.append(p.AUTHOR/'author-audit.json')
    for report in [p.load(OUT.parent/'author-audit.json'),p.load(p.INDEPENDENT/'independent-review.json'),p.load(p.AUTHOR/'author-audit.json')]:
        for x in report['stable_files']:
            q=ROOT/x['root_relative'] if 'root_relative'in x else TASK/x['task_relative']
            assert q.stat().st_size==x['bytes'] and p.sha(q)==x['sha256']
            stable.append(q)
    stable.extend(TASK/x['task_relative'] for x in artifacts)

    stable=sorted(set(stable));files=[dict((p.binding(path) if path.is_relative_to(TASK) else p.source_binding(path)),batch_relative=Path(os.path.relpath(path,OUT)).as_posix()) for path in stable]
    failures=[row for row in receipt['rows'] if row['exit_code']!=0]
    p.dump(OUT/'source-manifest.json',dict(source_sha256=p.SOURCE_SHA,files=files,
        fresh_compiler_cache_bindings=artifacts,retained_failed_actual_runs=failures,
        independent_transplantation_review_claimed=True))
    report=dict(verdict='PASS',role='Matrix platform independent reviewer; all own fresh source, parser, kernel and resolver execution',
        source_sha256=p.SOURCE_SHA,author_sha256=PLATFORM_AUTHOR_SHA,native_author_sha256=p.AUTHOR_SHA,native_independent_sha256=p.INDEPENDENT_SHA,
        checks=checks,targets=targets,definition_comparisons=comparisons,
        complete_parent_definition_kernel_comparisons=full_kernel,complete_parent_function_rfl_records=full_rfl,
        complete_parent_source_value_provenance=full_prov,native_whole_expected_type_kernel_comparisons=native_meta,
        actual_native_source_records=native_source,actual_native_boundary_records=native_boundary,
        actual37_module_resolver_records=module_records,actual_resolver_runtime=runtime,
        Root_controls=root['Root_controls'],Root_build=root,
        findings=[dict(topic='cache',severity='informational',detail='Initially absent mt1; all 31 native/staged sources compiled personally. Fixed Mathlib package caches only; actual37 findOLean results point to own cache.'),
          dict(topic='source_and_proof_fields',severity='informational',detail='All70 complete source-body definitions including proof fields were compared by actual Meta/rfl in separate native and staged contexts; 169 helper proofs plus17 source proofs and wrapper per Solution are closed.'),
          dict(topic='pretty_printing',severity='informational',detail='Raw parent proof-field pretty-print differences are retained diagnostics, never used as equality evidence. Full140 Meta and140 whole-function rfl checks establish complete values.'),
          dict(topic='Root',severity='informational',detail='3831-job build0 and Root5 evidence verified; check1 exactly two old unassigned Tao files in another task. Reviewer made no Root/API/scope/credential writes.'),
          dict(topic='scope',severity='informational',detail='Original Even n>=2, actual rational inverse, actual output and HasSum/norm summability are preserved; no integer inverse, height bound, five-output transport or irrationality claim.')],
        whole_definition_kernel_comparisons=kernel,whole_function_rfl_records=rfl,
        raw_parent_proof_value_differences=differences,complete_proof_records=proof_records,
        whole_independent_type_kernel_comparisons=expected,boundary_records=boundary,
        original_printed_axiom_diagnostics=diagnostics,stable_files=files,
        actual_invocations=len(receipt['rows']),final_actual_success_invocations=len(latest),
        fresh_native_source_builds=13,additional_staged_source_builds=18,fresh_distinct_native_staged_source_builds=31,
        cache_objects_borrowed=False,Root_or_author_proof_fallback_permitted=False,
        native_oracle_graph_records=415,all_project_source_definitions=70,source_only_parser_aliases_include_all_proof_fields=True,
        independent_role_disclosure='This reviewer performed the earlier native Matrix independent review but did not author the Matrix platform sources, solution transformations or their frozen author report. All new platform objects and source replays were independently built in absent mt1; historical objects are read-only provenance, never execution inputs.',
        real_execution_completion=p.load(OUT/'execution-completion.json'),all_handles_terminal=True,remaining_Lean_bindings=0,
        final_success_Lean_invocations=len(latest)-1,final_success_runtime_invocations=1,
        retained_failed_attempts_excluded=failures,limitations=limits,
        Root_API_credentials_scope_writes=False,root_installed_by_author=False,root_installed_by_parent=True,
        independent_transplantation_review_claimed=True,platform_published=False,platform_accepted=False,
        irrationality_proved=False,integer_inverse_coefficients_proved=False,
        actual_five_output_transport_proved=False)
    check('every_finding_has_explicit_informational_severity',len(report['findings'])==5 and all(x['severity']=='informational' and x['detail'] for x in report['findings']))
    p.dump(OUT/'independent-integration-review.json',report)
    frozen=stable+[OUT/'source-manifest.json',OUT/'independent-integration-review.json']
    p.write(OUT/'SHA256SUMS.txt',''.join(p.sha(path)+'  '+Path(os.path.relpath(path,OUT)).as_posix()+'\n' for path in sorted(frozen)))
    for line in (OUT/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
        digest,relative=line.split('  ',1);assert p.sha(OUT/relative)==digest
    print(json.dumps(dict(independent_verdict='PASS',checks=len(checks),stable_files=len(files),artifacts=len(artifacts),
        actual_attempts=len(receipt['rows']),final_actual_successes=len(latest),failed_actual_Lean_attempts=len(failures),
        report_sha256=p.sha(OUT/'independent-integration-review.json'),copyplan_sha256=p.sha(OUT/'root-copy-plan.json'),
        manifest_sha256=p.sha(OUT/'source-manifest.json'),SHA256SUMS_sha256=p.sha(OUT/'SHA256SUMS.txt'))))


if __name__=='__main__':main()
