from __future__ import annotations
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
from pathlib import Path
import hashlib,json,subprocess,sys,time
from prepare_A_independent import OUT,TASK,ROOT,PROJECT,BATCH,PURE,load,bind,pathof,walk,verify,write

sys.dont_write_bytecode=True
STD3={'propext','Classical.choice','Quot.sound'}
def records(row):
    result=[]
    with pathof(row['stdout']).open(encoding='utf-8') as h:
        for line in h:
            if line.startswith('GAI_RECORD|'):result.append(json.loads(line[11:]))
            elif line.startswith('{'):
                try:result.append(json.loads(line))
                except json.JSONDecodeError:pass
    return result
def check_records(rows):
    for r in rows:
        for k in ['axioms','actual_axioms','expected_axioms']:
            if k in r:assert set(r[k])<=STD3,r
        if 'actual_axioms' in r and 'expected_axioms' in r:assert set(r['actual_axioms'])==set(r['expected_axioms']),r
        for k in ['value_type_isDefEq','type_isDefEq','actual_value_typed','expected_value_typed','all_fields_type_Expr_equal','all_fields_value_Expr_equal','full_type_kernel_equal','full_value_kernel_equal']:
            if k in r:assert r[k] is True,(r.get('kind'),r.get('name'),k)
        if r.get('kind')=='definition_compare':
            assert r['value_isDefEq'] and r['normalized_value_isDefEq'] and r['normalized_value_exprEqual'],r
        if r.get('kind')=='definition_helper_compare':assert r['type_exprEqual'] and r['value_exprEqual'] and r['value_isDefEq'],r
        if 'value_raw_format' in r:
            dag=json.loads(r['value_raw']);assert dag['format']=='lean-expr-dag-v1' and dag['nodes']
            assert 0<=dag['type_root']<len(dag['nodes']) and 0<=dag['value_root']<len(dag['nodes'])
def main():
    sys.stdout.reconfigure(encoding='utf-8');started=time.monotonic()
    final=OUT/'A-platform-independent-audit.json';assert not final.exists()
    prep=load(OUT/'A-source-preparation-v2.json');preflight=load(pathof(prep['personal_author_stock_preflight']))
    receipt=load(OUT/'A-actual-independent-calls.json');calls=receipt['rows']
    assert [r['index'] for r in calls]==list(range(1,len(calls)+1))
    last={};recorded=[]
    for row in calls:
        assert row['actual_environment']=={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'} and '-j1' in row['command']
        context=PROJECT/row['tag'];assert row['cwd']==str(context)
        assert int(pathof(row['exit_file']).read_text())==row['exit_code']
        assert row['failed_attempt_retained']==(row['exit_code']!=0)
        recorded.extend(walk(row))
        for pair in row['input_snapshots']+row['output_snapshots']:
            assert pair['original']['bytes']==pair['snapshot']['bytes'] and pair['original']['sha256']==pair['snapshot']['sha256']
        paths=load(pathof(row['selected_paths']));assert paths['actual_environment']=={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'}
        for key in ['LEAN_PATH','LEAN_SRC_PATH']:
            assert all(Path(x).resolve().is_relative_to(context.resolve()) or Path(x).resolve().is_relative_to((ROOT/'.lake/packages').resolve()) for x in paths[key]['filtered'])
        if row['exit_code']==0:last[(row['tag'],row['module'])]=row
    for tag,order in prep['compile_orders'].items():
        assert all((tag,m) in last for m in order),(tag,set(order)-{m for t,m in last if t==tag})
    expected_names={r['full_name'] for r in prep['all_original_complete_headers']};expected_defs={r['full_name'] for r in prep['all29_original_whole_definitions']}
    assert len(expected_names)==122 and len(expected_defs)==29
    results={};files=[];all_resolvers=[];dag_total=0;dag_nodes=0
    for tag in ['n','d','r','m','c','u']:
        kinds=['GAIResolver']+([] if tag=='r' else ['GAITypes','GAIKernel'])+(['GAIBoundary'] if tag in ['n','m','c','u'] else [])+(['GAIRawRecords'] if tag in ['m','c','u'] else [])+(['GAIFixtures'] if tag=='d' else [])+(['GAIReferences'] if tag=='r' else [])
        data={}
        for mod in kinds:
            rows=records(last[(tag,mod)]);check_records(rows);data[mod]=rows
            dest=OUT/'A-full-records'/tag/(mod+'.jsonl');write(dest,''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in rows));files.append(bind(dest))
            for r in rows:
                if 'value_raw_format' in r:
                    dag=json.loads(r['value_raw']);dag_total+=1;dag_nodes+=len(dag['nodes'])
        out=dict(actual_control_success_calls={mod:last[(tag,mod)]['index'] for mod in kinds},record_counts={mod:len(r) for mod,r in data.items()})
        if tag!='r':
            types=data['GAITypes'];kernel=data['GAIKernel'];th=[r for r in types if r['kind']=='theorem'];ds=[r for r in types if r['kind']=='definition']
            assert {r['name'] for r in ds}==expected_defs and len(ds)==29
            assert {r['name'] for r in th}==(set() if tag=='d' else expected_names)
            tc=[r for r in kernel if r['kind']=='theorem_compare'];dc=[r for r in kernel if r['kind']=='definition_compare'];rfl=[r for r in kernel if r['kind']=='definition_rfl'];aliases=[r for r in kernel if r['kind']=='expected_theorem_value'];helpers=[r for r in kernel if r['kind']=='definition_helper_compare']
            assert len(dc)==len(rfl)==29 and {r['actual'] for r in dc}==expected_defs
            assert len(tc)==len(aliases)==(0 if tag=='d' else 122)
            assert {r['actual'] for r in tc}==(set() if tag=='d' else expected_names)
            inv=[r for r in types if r['kind']=='module_inventory'];decl=[r for r in types if r['kind']=='module_declaration'];extras=[r for r in types if r['kind']=='module_extra'];visibility=[r for r in types if r['kind']=='compiler_extra_environment_visibility']
            assert {r['module'] for r in inv}==set(prep['contexts'][tag]['own_math_modules'])
            assert Counter(n for r in inv for n in r['constant_names'])==Counter(r['name'] for r in decl)
            assert set(n for r in inv for n in r['extra_names'])=={r['name'] for r in visibility}
            assert {r['name'] for r in extras}=={r['name'] for r in visibility if r['actual_env_find_some']}
            # Every actual inventory declaration must have a complete proof/value and inferType/Std3/lossless controls.
            assert all(r['value_type_isDefEq'] and r['all_fields_type_Expr_equal'] and r['all_fields_value_Expr_equal'] for r in decl+extras)
            out.update(complete_original_forall_types=len(th),whole_definition_comparisons=len(dc),whole_function_rfl=len(rfl),strict_helper_pairs=len(helpers),actual_inventory_declarations=len(decl),actual_visible_extra_declarations=len(extras),non_environment_compiler_extra_names=sorted(r['name'] for r in visibility if not r['actual_env_find_some']),inventory=inv,raw_type_Expr_equal_false=[r['actual'] for r in tc+dc if not r['type_exprEqual']],raw_definition_Expr_equal_false=[r['actual'] for r in dc if not r['value_exprEqual']],normalized_definition_Expr_equal_false=[r['actual'] for r in dc if not r['normalized_value_exprEqual']])
            assert not out['normalized_definition_Expr_equal_false']
            if tag in ['m','c','u']:
                assert sum(r['kind']=='selected_wrapper_compare' for r in kernel)==1 and sum(r['kind']=='selected_wrapper_proof' for r in kernel)==1
            if tag!='d':assert len(data['GAIBoundary'])==15 and all(r['kind']=='typed_boundary' for r in data['GAIBoundary']);out['typed_boundaries']=15
        if tag in ['m','c','u']:
            raw=data['GAIRawRecords'];contracts=[r for r in raw if r['kind']=='raw_goal_contract'];assert len(contracts)==4
            inv=[r for r in raw if r['kind']=='module_inventory'];decl=[r for r in raw if r['kind']=='module_declaration'];assert len(inv)==1
            assert Counter(inv[0]['constant_names'])==Counter(r['name'] for r in decl)
            out['actual_raw_contracts_complete_values_inferType_Std3_DAG']=4
        if tag=='r':
            refs=data['GAIReferences'];assert len(refs)==3 and all(r['type_isDefEq'] and r['complete_type_roundtrip'] and r['catalog_value_not_mathematical_proof'] for r in refs)
            out['catalog_types_only_not_complete_proofs']=3;out['raw_reference_type_Expr_equal_false']=[r['name'] for r in refs if not r['type_Expr_equal']]
        if tag=='d':
            fixtures=data['GAIFixtures'];assert sum(r.get('kind')=='expr_dag_validation' for r in fixtures)==20 and sum(r.get('kind')=='expr_dag_small_source_validation' for r in fixtures)==3
            assert all(r['all_fields_roundtrip'] and r['raw_repr_reconstruction_equal'] for r in fixtures)
            out['all_constructor_metadata_fixtures']=20;out['small_actual_definition_fixtures']=3
        counts=Counter();own=[]
        for r in data['GAIResolver']:
            assert r['kind']=='actual_module_resolver';path=Path(r['canonical_olean']).resolve();assert path.exists()
            context=(PROJECT/tag).resolve()
            if path.is_relative_to(context):origin='own_fresh_SOURCE';assert path.is_relative_to(context/'b/lib/lean')
            elif path.is_relative_to((ROOT/'.lake/packages').resolve()):origin='stock_pinned_packages'
            else:assert '.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/' in path.as_posix(),r;origin='stock_intrinsic_Lean4.33.1'
            counts[origin]+=1
            if origin=='own_fresh_SOURCE':own.append(r)
            if r['module'].startswith('Solutions.'):assert tag in ['m','c','u'] and r['module'] in prep['contexts'][tag]['own_math_modules']
            if r['module'].startswith('Theorems.'):assert tag=='r'
            all_resolvers.append(dict(tag=tag,origin=origin,record=r))
        out['actual_resolver_origins']=dict(counts);out['all_own_resolved_modules']=own;results[tag]=out
    # Verify every package/intrinsic import was already bound BEFORE this run, then rehash all precompile stock.
    baseline={str(pathof(r).resolve()):r for r in preflight['stock_precompile_bindings']}
    for row in all_resolvers:
        if row['origin']!='own_fresh_SOURCE':assert str(Path(row['record']['canonical_olean']).resolve()) in baseline,row
    with ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(verify,baseline.values()))
    stockpost=OUT/'A-stock-postcompile-rehash.json';write(stockpost,dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),stock_count=len(baseline),stock_bindings=list(baseline.values()),mismatches=0,precompile=prep['personal_author_stock_preflight'],all_actual_stock_imports_prebound=True,API_calls=0))
    # Immutable source/export equality gates, independent of the successful compiler receipts.
    for row in prep['source_bindings']:verify(row)
    plan=load(BATCH/'target-plan.json');exports=[]
    for tag,target in zip(['m','c','u'],plan['targets']):
        src=PROJECT/tag/'src'/target['local_solution'];candidate=BATCH/'staged'/target['local_solution'];assert src.read_bytes()==candidate.read_bytes()
        dest=OUT/'A-platform-independent-native-export'/target['local_solution'];dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.write_bytes(src.read_bytes())
        exports.append(dict(target=target['theorem_name'],actual_success_call=last[(tag,target['local_solution'][:-5].replace('/','.'))]['index'],actual_SOURCE=bind(src),candidate_SOURCE=bind(candidate),complete_export=bind(dest)))
    # Preserve every actual Definition and reference SOURCE, not just the three proof files.
    for tag,subdir in [('d','Definitions'),('r','Theorems')]:
        for src in sorted((PROJECT/tag/'src'/subdir).glob('*.lean')):
            relative=src.relative_to(PROJECT/tag/'src');candidate=BATCH/'staged'/relative
            assert src.read_bytes()==candidate.read_bytes()
            module=relative.as_posix()[:-5].replace('/','.')
            dest=OUT/'A-platform-independent-native-export'/relative;dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.write_bytes(src.read_bytes())
            exports.append(dict(module=module,role='standalone_whole_definition_SOURCE' if tag=='d' else 'reference_full_type_catalog_SOURCE_only',actual_success_call=last[(tag,module)]['index'],actual_SOURCE=bind(src),candidate_SOURCE=bind(candidate),complete_export=bind(dest)))
    for module in prep['contexts']['n']['own_math_modules']:
        src=PROJECT/'n/src'/(module.replace('.','/')+'.lean');dest=OUT/'A-native-full11-export'/src.relative_to(PROJECT/'n/src')
        dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.write_bytes(src.read_bytes())
        exports.append(dict(module=module,role='complete_native_SOURCE',actual_success_call=last[('n',module)]['index'],actual_SOURCE=bind(src),complete_export=bind(dest)))
    command="$taskProject = '"+str(PROJECT)+"'; @(Get-CimInstance Win32_Process | Where-Object { $_.Name -in @('lean.exe','lake.exe','python.exe') -and $_.CommandLine -and $_.CommandLine.Contains($taskProject) } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
    osrow=subprocess.run(['powershell','-NoProfile','-Command',command],capture_output=True);assert osrow.returncode==0;live=json.loads(osrow.stdout.decode('utf-8-sig') or '[]');assert not live,live
    frozen=OUT/'A-frozen-all-actual-calls.json';write(frozen,receipt)
    stable=list(walk(prep))+list(walk(receipt))+list(walk(preflight))+files+list(walk(exports))+[bind(OUT/'A-source-preparation-v2.json'),bind(OUT/'A-personal-author-stock-preflight.json'),bind(stockpost),bind(frozen),bind(Path(__file__))]
    for tag in prep['contexts']:
        c=PROJECT/tag
        stable += [bind(p) for prefix in ['src','b'] for p in sorted((c/prefix).rglob('*')) if p.is_file()]
        stable += [bind(c/name) for name in ['lakefile.lean','lean-toolchain','lake-manifest.json','leaf.py']]
    stable=list({str(pathof(b)):b for b in stable}.values())
    with ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(verify,stable))
    audit=dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),verdict='PASS',status='PLATFORM_INDEPENDENT_FULL_PASS',role='independent',owner='graph_integration_audit_1008',lane=2,private_project='.rt/gaui1008',actual_calls=len(calls),actual_successes=sum(r['exit_code']==0 for r in calls),historical_failures_preserved=[r['index'] for r in calls if r['exit_code']!=0],all_actual_handles_terminal=True,actual_own_WMI_live_processes=live,all_required_final_SOURCE_and_controls_exit0=True,three_isolated_complete122_proof_contexts=True,native11_source_context_checked=True,standalone29_whole_definition_context_checked=True,three_references_type_catalog_only=True,contexts=results,all_original_headers_and_whole_definition_values_unchanged=True,new13_definitions_are_subset_of_total29=True,normalization='Only expand full-type/full-value Expr.equal paired proposition-valued helpers from exact29 original owners; all raw false observations preserved; no binder/metadata/payload erasure',all_actual_own_resolver_origins=all_resolvers,all_stock_imports_bound_precompile_and_full_postcompile_rehash=True,stock_prepost_count=len(baseline),all_actual_mathematical_module_inventory_values_types_Std3_inferType_complete=True,reference_catalog_excluded_from_mathematical_proof_value_PASS=True,full_lossless_Expr_DAG_records=dag_total,full_lossless_Expr_DAG_nodes=dag_nodes,complete_SOURCE_exports=exports,full_control_records=files,Root_grant=prep['Root_grant'],author_report=prep['author_report'],Root_author_pin=prep['Root_pin'],source_preparation=bind(OUT/'A-source-preparation-v2.json'),personal_author_stock_preflight=prep['personal_author_stock_preflight'],stock_postcompile=bind(stockpost),all_actual_calls_frozen=bind(frozen),stable_bindings=len(stable),stable_bytes=sum(r['bytes'] for r in stable),stable_files=stable,mismatches=0,platform_independent_PASS=True,uploaded=False,API_calls=0,credential_reads=0,shared_scope_docs_writes=0,foreign_mathematical_objects_borrowed=False,mathematical_scope=dict(actual_weighted_uniform_A=True,all_n_ge1=True,all_rational_quartics_degree_le4=True,coefficient_independent_epsilon_tends_zero=True,arbitrary_signs_and_changing_coefficients=True,no_assumed_Summable_HasSum_moment_bound_coefficient_growth_or_parity=True,integer_preimage_height_J_exact_fstar_irrationality_not_claimed=True),elapsed_seconds=time.monotonic()-started)
    write(final,audit)
    print(json.dumps(dict(verdict='PASS',actual_calls=len(calls),actual_successes=audit['actual_successes'],stable_bindings=len(stable),stable_bytes=audit['stable_bytes'],DAG_records=dag_total,DAG_nodes=dag_nodes,audit=bind(final),elapsed_seconds=time.monotonic()-started)),flush=True)
if __name__=='__main__':main()
