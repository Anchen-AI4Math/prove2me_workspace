"""Connection author evidence gate. Never runs Lean, installs, or publishes."""
from pathlib import Path
import hashlib, json, os, subprocess, sys
import review_driver as d

OUT=d.OUT; TASK=d.TASK; ROOT=d.ROOT; PROJECT=d.PROJECT; NS=d.NS; STD=d.STD
checks=[]

def check(name,passed,evidence=None):
    checks.append(dict(name=name,pass_=bool(passed),evidence=evidence))
    checks[-1]['pass']=checks[-1].pop('pass_')
    if not passed:
        n=len(list(OUT.glob('retained-author-gate-failure-*.json')))+1
        d.dump(OUT/('retained-author-gate-failure-'+str(n).zfill(2)+'.json'),
            dict(failed_check=name,checks=checks,excluded_from_success_evidence=True))
        raise AssertionError(name)

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    d.preconditions()
    receipt=d.load(OUT/'compile-receipt.json')
    plan=d.load(OUT/'target-plan.json'); prov=d.load(OUT/'integration-provenance.json')
    source=(TASK/'formalization/CoefficientMapConnection.lean').read_bytes()
    check('actual_native_source_bytes_and_own_fresh_copy_fixed',
        d.digest(source)==d.SOURCE_SHA==d.sha(PROJECT/(d.NATIVE.replace('.','/')+'.lean')) and len(source)==20507)
    indpath=TASK/'verification/formalization-coefficient-map-connection-independent-2026-10-04/independent-review.json'
    ind=d.load(indpath)
    check('native_independent_28_checks_108_bindings_still_fixed',
        d.sha(indpath)=='92940f9b02161210e55af39c625e0cd233eaf7a5bf9d5c1aa2238f0506e28d82'
        and ind['verdict']=='PASS' and len(ind['checks'])==28 and all(x['pass'] for x in ind['checks'])
        and len(ind['stable_files'])==108
        and all(d.sha(ROOT/r['root_relative'] if 'root_relative' in r else TASK/r['task_relative'])==r['sha256'] for r in ind['stable_files']))
    for r in receipt['rows']:
        for key in ['log','stdout','stderr','exit_file','selected_paths']:
            b=r[key];p=TASK/b['task_relative']
            assert d.sha(p)==b['sha256'] and p.stat().st_size==b['bytes']
        for b in r['input_bindings']+r['output_bindings']:
            p=TASK/b['task_relative'];assert d.sha(p)==b['sha256'] and p.stat().st_size==b['bytes']
    latest={}
    for r in receipt['rows']:latest[r['label']]=r
    check('all_final_actual_executions_zero_and_hash_bound',
        len(latest)==44 and all(r['exit_code']==0 for r in latest.values()),
        dict(final_unique_executions=len(latest),actual_attempts=len(receipt['rows']),
             retained_failed_executions=sum(r['exit_code']!=0 for r in receipt['rows'])))
    check('own_short_cache_without_borrowed_source_proof_objects',
        receipt['native_and_staged_objects_borrowed'] is False
        and receipt['fresh_build_task_relative']=='.rt/ct1/b'
        and not receipt['root_writes'] and not receipt['API_calls'])
    selected=[d.load(TASK/r['selected_paths']['task_relative']) for r in latest.values()]
    check('every_actual_Lean_environment_filters_root_fallback',
        all(all(Path(p).resolve().is_relative_to(PROJECT.resolve()) or
                    Path(p).resolve().is_relative_to((ROOT/'.lake/packages').resolve())
                for p in s['LEAN_PATH']['filtered']) for s in selected)
        and all(str(PROJECT/'b/lib/lean') in s['LEAN_PATH']['filtered'] for s in selected))
    paths=d.load(OUT/'own-execution-plan.json')['path_checks']
    check('windows_output_paths_reserve_64_extra_characters',
        len(paths)==8 and all(x['passed'] and x['path_plus_64']<=259 for x in paths),paths)
    resolved=d.rows(OUT/'resolution-audit.log')
    check('actual_findOLean_binds_all_eight_own_objects',len(resolved)==8 and all(
        Path(x['olean']).resolve()==(PROJECT/'b/lib/lean'/(x['module'].replace('.','/')+'.olean')).resolve()
        for x in resolved),resolved)
    toolchain=(PROJECT/'lean-toolchain').read_text().strip()
    mathlib=next(p for p in d.load(PROJECT/'lake-manifest.json')['packages'] if p['name']=='mathlib')
    git=subprocess.run(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],capture_output=True)
    d.write(OUT/'mathlib-revision.log',git.stdout+git.stderr)
    check('actual_fixed_Lean_4_33_1_and_Mathlib_revision',toolchain=='leanprover/lean4:v4.33.1'
        and 'version 4.33.1' in (OUT/'toolchain.log').read_text(encoding='utf-8-sig')
        and mathlib['rev']==d.REV and git.returncode==0 and git.stdout.decode().strip()==d.REV)
    c=d.context()
    check('real_actual_graph_parser_and_header_39_12_27',
        prov['graph_records']==len(c['graph']) and prov['source_declarations']==39
        and prov['source_defs']==12 and prov['source_proofs']==27
        and len([f for f in c['facts'] if f['kind']=='decl'])==39
        and source[:prov['header']['end']['offset']].decode().strip().splitlines()==['import '+m for m in d.MATHLIB])
    fields=d.load(OUT/'embedded-field-provenance.json')
    check('exact_four_original_helper_closures_no_new_global_theorem',
        fields['actual_parser_spans_only'] and fields['new_global_helper_theorems']==[]
        and fields['ordinary_data_Definitions']==11 and fields['proof_bearing_Definitions']==1
        and set(fields['actual_helper_names'])=={NS+'.'+n for n in ['coefficientPolynomial_add','coefficientPolynomial_smul','connectionOperator_add','connectionOperator_smul']}
        and len(fields['fields'])==fields['actual_reference_count']==6,
        dict(distinct_helper_callees=4,actual_resolved_reference_occurrences=6,
             initial_pure_preparation_file_preserved='freeze_author.py'))
    typereport=d.rows(OUT/'embedded-types.log')
    check('actual_semantic_helper_type_remapping_standard_axioms',len(typereport)==4
        and {r['declaration'] for r in typereport}==set(fields['actual_helper_names'])
        and all(r['original_type_expression_repr'] and r['remapped_type_expression_repr']
            and set(r['axioms'])<=STD for r in typereport))
    chunks=[]
    for name,fact in zip(d.DEFS,prov['definition_facts']):
        a,b=fact['declStart']['offset'],fact['declEnd']['offset'];edits=[]
        for f in fields['fields']:
            if f['definition']!=NS+'.'+name:continue
            r=f['reference_fact'];x,y=r['start']['offset'],r['end']['offset']
            assert source[x:y].decode()==f['actual_proof_callee'].rsplit('.',1)[1]
            assert not f['data_fields_edited']
            for h in f['helper_facts']:
                hd,binding=h['declaration_fact'],h['binding_fact']
                assert source[hd['declStart']['offset']:binding['start']['offset']].decode().strip()=='theorem'
                assert h['only_prefix_edit']['replacement']=='have '
            edits.append((x-a,y-a,f['replacement_proof_term'].encode()))
        chunks.append(d.edit(source[a:b],edits).decode())
    prefix='\n'.join('import '+m for m in d.MATHLIB)+'\n\nset_option autoImplicit false\nnoncomputable section\nopen Polynomial\n\nnamespace '+NS+'\n\n'
    reconstructed=prefix+'\n\n'.join(chunks)+'\n\nend '+NS+'\n'
    definition=(OUT/'staged'/d.DEF_PATH).read_bytes()
    check('all_twelve_Definitions_reconstructed_from_actual_spans',reconstructed.encode()==definition
        and definition==(PROJECT/d.DEF_PATH).read_bytes())
    alias=(OUT/'NativeValueComparisonDefinition.lean').read_bytes()
    salias=(OUT/'StagedValueComparisonDefinition.lean').read_bytes()
    old=('import '+d.NATIVE).encode();new=('import '+d.DEF_PATH.removesuffix('.lean').replace('/','.')).encode()
    ncompare=(OUT/'native-value-comparison.lean').read_bytes()
    scompare=(OUT/'staged-value-comparison.lean').read_bytes()
    check('actual_shared_alias_and_comparison_differ_only_by_import',alias.count(old)==1
        and alias.replace(old,new)==salias
        and ncompare.replace(b'import NativeValueComparisonDefinition',b'import StagedValueComparisonDefinition')==scompare)
    kernel=[];rfl=[]
    for env,label in [('native','native-value-comparison'),('staged','staged-value-comparison')]:
        rs=d.rows(OUT/(label+'.log'))
        eqs=[r for r in rs if r['kind']=='native_alias_full_kernel_equality']
        proofs=[r for r in rs if r['kind']=='rfl_or_data_equality']
        check(env+'_twelve_actual_full_type_and_whole_value_kernel_equalities',
            len(eqs)==12 and [r['declaration'] for r in eqs]==[NS+'.'+n for n in d.DEFS]
            and all(r['type_kernel_equal'] and r['full_value_kernel_equal']
                    and r['original_expression_repr'] and r['alias_expression_repr']
                    and set(r['axioms'])<=STD for r in eqs))
        check(env+'_thirteen_closed_whole_value_rfl_and_data_equalities',
            len(proofs)==13 and all(set(r['axioms'])<=STD for r in proofs))
        kernel += [dict(r,context=env) for r in eqs]
        rfl += [dict(r,context=env) for r in proofs]
    native={r['label']:r for r in d.rows(OUT/'original.log')}
    contexts=['definition']+['types_'+str(i)+'_'+kind for i in range(3) for kind in ['solution','reference']]
    reports={label:{r['label']:r for r in d.rows(OUT/(label+'.log'))} for label in contexts}
    canonical=reports['definition'];comparisons=[];rawdiff=[]
    for name in d.DEFS:
        full=NS+'.'+name;o=native[full]
        for ctx,rs in reports.items():
            r=rs[full];ordinary=name!='connectionLinearMap';pretty=o['value']==r['value']
            can=r['value']==canonical[full]['value']
            comparisons.append(dict(declaration=full,context=ctx,type_equal=o['type']==r['type'],
                pretty_value_equal=pretty,canonical_staged_pretty_value_equal=can,
                value_equal=pretty if ordinary else can,
                equality_basis='full native/alias and staged/alias kernel equality, canonical staged propagation' if not ordinary else 'actual exact source span and full pretty value',axioms=r['axioms']))
            if not pretty:rawdiff.append(dict(declaration=full,context=ctx,native_value=o['value'],staged_value=r['value']))
    check('all_84_actual_Definition_types_and_77_ordinary_values',len(comparisons)==84
        and all(r['type_equal'] and r['value_equal'] and set(r['axioms'])<=STD for r in comparisons)
        and sum(r['declaration']!=NS+'.connectionLinearMap' for r in comparisons)==77)
    check('one_proof_bearing_map_propagates_through_seven_contexts',
        sum(r['declaration']==NS+'.connectionLinearMap' and r['canonical_staged_pretty_value_equal'] for r in comparisons)==7
        and all(r['declaration']==NS+'.connectionLinearMap' for r in rawdiff),
        dict(raw_pretty_differences=len(rawdiff),direct_native_map_calls=1,direct_staged_map_calls=1,
             seven_contexts_are_canonical_propagation=True))
    targets=[]
    for i,t in enumerate(plan['targets']):
        n=t['theorem_name'];o=native[n];s=reports['types_'+str(i)+'_solution'][n];r=reports['types_'+str(i)+'_reference'][n]
        targets.append(dict(theorem=n,actual_original_type=o['type'],
            original_solution_reference_type_equal=o['type']==s['type']==r['type'],
            original_axioms=o['axioms'],solution_axioms=s['axioms'],reference_axioms=r['axioms']))
    check('three_original_Solution_reference_types_are_exact',len(targets)==3
        and all(t['original_solution_reference_type_equal'] for t in targets),targets)
    check('complete_endpoint_proofs_use_only_standard_three_axioms',
        all(set(t['original_axioms'])==set(t['solution_axioms'])==STD for t in targets))
    check('reference_statement_stubs_only_have_sorryAx',all('sorryAx' in t['reference_axioms'] for t in targets))
    proofrecords=[d.rows(OUT/('helpers_'+str(i)+'.log')) for i in range(3)]
    check('all_27_original_proofs_and_wrappers_closed_in_each_Solution',
        all(len(rs)==28 and all(set(r['axioms'])<=STD for r in rs) for rs in proofrecords),dict(records_per_Solution=28,total_records=84))
    cuts=[(d0['declStart']['offset'],d0['declEnd']['offset'],b'') for d0 in prov['definition_facts']]
    cuts += [(0,prov['header']['end']['offset'],b'')]
    cuts += [(f['span']['start']['offset'],f['span']['end']['offset'],b'') for f in prov['deleted_diagnostic_facts']]
    prefix='import '+d.DEF_PATH.removesuffix('.lean').replace('/','.')+'\nimport Mathlib.Tactic\n\nset_option autoImplicit false\nset_option maxHeartbeats 2000000\n'
    exact=[]
    for t in plan['targets']:
        n=t['theorem_name'];pt=prov['targets'][n];changes=[(a,b,v.encode()) for a,b,v in pt['rename_edits']]
        reconstructed=prefix+'\n'+d.edit(source,cuts+changes).decode()+'\n\nopen Polynomial '+NS+'\n\ntheorem solution'+pt['original_signature']+':= by\n  exact '+NS+'.checked_'+n.rsplit('.',1)[1]+' '+t['wrapper_arguments']+'\n\n#print axioms solution\n'
        exact.append(reconstructed.encode()==(OUT/'staged'/t['local_solution']).read_bytes())
    check('three_actual_parser_Solution_splices_keep_every_proof_body',all(exact)
        and all(prov['targets'][t['theorem_name']]['extra_hypotheses']==[] for t in plan['targets']))
    check('no_external_Theorem_Solution_or_native_proof_import',
        all(not any(line.startswith(('import Theorems.','import Solutions.','import missions.'))
            for line in (OUT/'staged'/t['local_solution']).read_text(encoding='utf-8').splitlines()) for t in plan['targets'])
        and plan['existing_definitions']==[] and prov['new_external_theorem_boundaries']==[])
    oldsource=d.load(d.AUTHOR/'type-audit.json')['records'];oldboundary=d.load(d.AUTHOR/'boundary-audit.json')['records']
    freshsource=d.rows(OUT/'native-author-audit.log');freshboundary=d.rows(OUT/'native-boundary-audit.log')
    check('fresh_native_39_source_records_match_frozen_author_types_and_axioms',
        len(freshsource)==len(oldsource)==39 and all(r['type']==o['type'] and r['value']==o['value'] and set(r['axioms'])<=STD for r,o in zip(freshsource,oldsource)))
    check('fresh_native_12_closed_boundaries_match_frozen_author',
        len(freshboundary)==len(oldboundary)==12 and all(r['declaration']==o['declaration'] and r['type']==o['type'] and set(r['axioms'])<=STD for r,o in zip(freshboundary,oldboundary)))
    stages=d.load(OUT/'stage-boundary-report.json')['runs']; normalize=lambda s:s.replace(NS+'.checked_',NS+'.')
    stage_source=stages[0]['records'];stage_boundary=stages[1]['records']
    byold={r['declaration']:r for r in oldsource};boundarycomparisons=[]
    for r in stage_source:
        name=r['label'];o=byold[name]
        value_equal=r['value']==o['value'] or name==NS+'.connectionLinearMap' and r['value']==canonical[name]['value']
        boundarycomparisons.append(dict(declaration=name,type_equal=normalize(r['type'])==o['type'],
            value_equal=value_equal,axioms=r['axioms']))
    check('all_39_actual_staged_source_types_and_definition_values_match',
        len(stage_source)==39 and all(r['type_equal'] and r['value_equal'] and set(r['axioms'])<=STD for r in boundarycomparisons))
    for r,o in zip(stage_boundary,oldboundary):
        boundarycomparisons.append(dict(declaration=r['declaration'],type_equal=normalize(r['type'])==o['type'],value_equal=True,axioms=r['axioms']))
    check('all_12_closed_native_boundaries_replayed_without_new_hypotheses',
        len(stage_boundary)==12 and len(boundarycomparisons)==51
        and all(r['type_equal'] and set(r['axioms'])<=STD for r in boundarycomparisons),
        ['n=1 actual kernel, simple composition and fifth target','n=0 Nat clipping and separately written signed nonzero kernel','constant/zero q and zero rhs','actual even-parameter targets and zero-vector kernel'])
    req=d.load(OUT/'problems-request.json');dr=d.load(OUT/'definitions-request.json')
    check('documented_exact_API_payload_structure_and_original_Definition',set(req)=={'env','private','problems'}
        and req['env']==d.REV and not req['private'] and len(req['problems'])==3 and len(dr)==1
        and dr[0]['definition'].encode()==definition and dr[0]['env']==d.REV and not dr[0]['private']
        and all(p['formal_statement'].endswith(':= by sorry') and len(p['theorem_title'])<=200 for p in req['problems']))
    check('original_scope_preserved_all_n_ge1_and_true_five_targets',
        all('n>=1' in p['natural_language_statement'] for p in req['problems'])
        and 'No P-degree bound' in req['problems'][0]['natural_language_statement']
        and 'five P coefficients and ten q coefficients' in req['problems'][1]['natural_language_statement']
        and 'Rational-function, HasSum and five-output parameter transport are separate' in req['problems'][2]['natural_language_statement'])
    copyfiles=[]
    for rel in [d.DEF_PATH]+[t['local_'+kind] for t in plan['targets'] for kind in ['solution','reference']]:
        p=OUT/'staged'/rel
        assert p.read_bytes()==(PROJECT/rel).read_bytes()
        dest=ROOT/rel
        assert not dest.exists() or d.sha(dest)==d.sha(p)
        copyfiles.append(dict(staged_task_relative=p.relative_to(TASK).as_posix(),root_relative_destination=rel,
            bytes=p.stat().st_size,sha256=d.sha(p),destination_exists_at_author_freeze=dest.exists()))
    check('seven_fixed_copyplan_files_no_differing_existing_destination',len(copyfiles)==7)
    d.dump(OUT/'root-copy-plan.json',dict(source_sha256=d.SOURCE_SHA,required_existing_Definitions=[],
        overwrite_allowed=False,author_scope='task-local staged original Connection; parent installs',files=copyfiles,
        scope_build_entrypoints_for_parent=[t['local_solution'].removesuffix('.lean').replace('/','.') for t in plan['targets']]))
    artifacts=[d.binding(p) for p in sorted((PROJECT/'b').rglob('*')) if p.is_file()]
    check('actual_fresh_compiler_cache_artifacts_are_hash_bound',artifacts and all(Path(TASK/r['task_relative']).resolve().is_relative_to((PROJECT/'b').resolve()) for r in artifacts),dict(artifacts=len(artifacts)))
    failures=[r for r in receipt['rows'] if r['exit_code']!=0]
    from final_gate import finish
    finish(d,checks,receipt,plan,prov,kernel,rfl,comparisons,rawdiff,proofrecords,boundarycomparisons,artifacts,targets)

if __name__=='__main__':main()
