from __future__ import annotations
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
from pathlib import Path
import json,os,subprocess,sys,time

sys.dont_write_bytecode=True
from prepare_A_independent import OUT,TASK,ROOT,BATCH,load,bind,pathof,walk,verify,write
from freeze_A_independent_v2 import records,check_records

CONTEXT=TASK/'.rt/gaui1008/u2'
SCOPE='LIMIT_SCOPE_TO_UNIFORM_ENDPOINT_AND_STANDALONE13_DEFINITION_AFTER_COMPLETE_STOCK_PREFREEZE'

def identity(path):
    # Resolver already supplied actual physical realPath; only Windows path case is normalized here.
    # No Lean expression normalization, binder removal or metadata removal occurs in this function.
    return os.path.normcase(os.path.abspath(str(path)))

def main():
    started=time.monotonic();sys.stdout.reconfigure(encoding='utf-8')
    final=OUT/'A-uniform-focused-independent-audit.json';assert not final.exists()
    preparation=OUT/'A-uniform-focused-source-preparation.json';prep=load(preparation)
    assert prep['scope']==SCOPE and prep['all_foreign_math_objects_copied']==0 and prep['project_initially_absent']
    stockpath=pathof(prep['complete_actual_stock_prefreeze']);stock=load(stockpath)
    assert stock['stock_count']==44052 and stock['stock_bytes']==7721113867 and stock['mismatches']==0
    assert stock['supplement_binds_future_calls_not_first67']
    callsfile=OUT/'A-uniform-focused-actual-calls.json';receipt=load(callsfile);calls=receipt['rows']
    assert len(calls)==11 and [r['index'] for r in calls]==list(range(1,12))
    assert [r['module'] for r in calls]==prep['compile_order']
    last={};recorded=[]
    stock_time=datetime.fromisoformat(stock['checked_at_utc']).timestamp()
    preparation_time=datetime.fromisoformat(prep['created_at_utc']).timestamp()
    assert stock_time<=preparation_time
    for row in calls:
        assert row['cwd']==str(CONTEXT) and row['actual_environment']=={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'} and '-j1' in row['command']
        assert row['exit_code']==0 and int(pathof(row['exit_file']).read_text(encoding='utf-8'))==0 and not row['failed_attempt_retained']
        for pair in row['input_snapshots']+row['output_snapshots']:
            assert pair['original']['bytes']==pair['snapshot']['bytes'] and pair['original']['sha256']==pair['snapshot']['sha256']
        paths=load(pathof(row['selected_paths']));assert paths['actual_environment']=={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'}
        for key in ['LEAN_PATH','LEAN_SRC_PATH']:
            for raw in paths[key]['filtered']:
                p=Path(raw).resolve();assert p.is_relative_to(CONTEXT.resolve()) or p.is_relative_to((ROOT/'.lake/packages').resolve())
        last[row['module']]=row;recorded.extend(walk(row))
        actual_folder=pathof(row['stdout']).parent
        intent=load(actual_folder/'intent.json')
        assert intent['index']==row['index'] and intent['module']==row['module'] and intent['command']==row['command']
        assert intent['started_epoch']>=preparation_time>=stock_time
        recorded += [bind(actual_folder/'intent.json'),bind(actual_folder/'terminal-receipt.json')]
    expected_names={r['full_name'] for r in prep['all_original_complete_headers']};expected_defs={r['full_name'] for r in prep['all29_original_whole_definitions']}
    assert len(expected_names)==122 and len(expected_defs)==29
    data={};files=[];dag_total=0;dag_nodes=0
    for module in ['GAITypes','GAIKernel','GAIBoundary','GAIRawRecords','GAIResolver']:
        rows=records(last[module]);check_records(rows);data[module]=rows
        destination=OUT/'A-uniform-focused-full-records'/(module+'.jsonl')
        write(destination,''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in rows));files.append(bind(destination))
        for r in rows:
            if 'value_raw_format' in r:
                dag=json.loads(r['value_raw']);dag_total+=1;dag_nodes+=len(dag['nodes'])
    types=data['GAITypes'];kernel=data['GAIKernel'];theorems=[r for r in types if r['kind']=='theorem'];definitions=[r for r in types if r['kind']=='definition']
    assert len(theorems)==122 and {r['name'] for r in theorems}==expected_names
    assert len(definitions)==29 and {r['name'] for r in definitions}==expected_defs
    theorem_compare=[r for r in kernel if r['kind']=='theorem_compare'];definition_compare=[r for r in kernel if r['kind']=='definition_compare']
    rfl=[r for r in kernel if r['kind']=='definition_rfl'];aliases=[r for r in kernel if r['kind']=='expected_theorem_value'];helpers=[r for r in kernel if r['kind']=='definition_helper_compare']
    assert len(theorem_compare)==len(aliases)==122 and {r['actual'] for r in theorem_compare}==expected_names
    assert len(definition_compare)==len(rfl)==29 and {r['actual'] for r in definition_compare}==expected_defs
    assert all(r['normalized_value_exprEqual'] and r['normalized_value_isDefEq'] for r in definition_compare)
    assert len(helpers)==34 and all(r['type_exprEqual'] and r['value_exprEqual'] and r['value_isDefEq'] for r in helpers)
    assert sum(r['kind']=='selected_wrapper_compare' for r in kernel)==1 and sum(r['kind']=='selected_wrapper_proof' for r in kernel)==1
    inventory=[r for r in types if r['kind']=='module_inventory'];declarations=[r for r in types if r['kind']=='module_declaration']
    extras=[r for r in types if r['kind']=='module_extra'];visibility=[r for r in types if r['kind']=='compiler_extra_environment_visibility']
    assert {r['module'] for r in inventory}==set(prep['own_math_modules'])
    assert Counter(n for r in inventory for n in r['constant_names'])==Counter(r['name'] for r in declarations)
    assert set(n for r in inventory for n in r['extra_names'])=={r['name'] for r in visibility}
    assert {r['name'] for r in extras}=={r['name'] for r in visibility if r['actual_env_find_some']}
    assert all(r['value_type_isDefEq'] and r['all_fields_type_Expr_equal'] and r['all_fields_value_Expr_equal'] for r in declarations+extras)
    boundaries=data['GAIBoundary'];assert len(boundaries)==15 and all(r['kind']=='typed_boundary' for r in boundaries)
    raw=data['GAIRawRecords'];contracts=[r for r in raw if r['kind']=='raw_goal_contract'];assert len(contracts)==4
    raw_inventory=[r for r in raw if r['kind']=='module_inventory'];raw_declarations=[r for r in raw if r['kind']=='module_declaration']
    raw_extras=[r for r in raw if r['kind']=='module_extra'];raw_visibility=[r for r in raw if r['kind']=='compiler_extra_environment_visibility']
    assert len(raw_inventory)==1 and Counter(raw_inventory[0]['constant_names'])==Counter(r['name'] for r in raw_declarations)
    assert set(raw_inventory[0]['extra_names'])=={r['name'] for r in raw_visibility}
    assert {r['name'] for r in raw_extras}=={r['name'] for r in raw_visibility if r['actual_env_find_some']}
    # Actual physical resolver classification and complete stock PRE/POST matching for this U2 run.
    baseline={identity(pathof(r)):r for r in stock['stock_bindings']};assert len(baseline)==stock['stock_count']
    origins=Counter();resolver=[]
    for row in data['GAIResolver']:
        assert row['kind']=='actual_module_resolver'
        path=Path(row['canonical_olean']).resolve();assert path.exists()
        if path.is_relative_to(CONTEXT.resolve()):
            origin='own_fresh_U2_SOURCE';assert path.is_relative_to(CONTEXT.resolve()/'b/lib/lean')
            assert row['module'] in prep['own_math_modules']
        elif path.is_relative_to((ROOT/'.lake/packages').resolve()):origin='stock_pinned_packages'
        else:
            assert '.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/' in path.as_posix();origin='stock_intrinsic_Lean4.33.1'
        if origin!='own_fresh_U2_SOURCE':
            for companion in [path,path.with_suffix('.ilean'),Path(str(path)+'.private'),Path(str(path)+'.server')]:
                assert identity(companion) in baseline,(row,companion)
        origins[origin]+=1;resolver.append(dict(origin=origin,record=row))
    assert origins['own_fresh_U2_SOURCE']==4 and sum(origins.values())==11017
    print('U2 complete control records parsed; rehashing true 44,052 precompile stock artifacts.',flush=True)
    with ThreadPoolExecutor(max_workers=2) as pool:list(pool.map(verify,baseline.values()))
    stockpost=OUT/'A-uniform-focused-stock-postcompile-rehash.json'
    write(stockpost,dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),stock_count=len(baseline),stock_bytes=stock['stock_bytes'],stock_bindings=list(baseline.values()),mismatches=0,precompile=prep['complete_actual_stock_prefreeze'],all_actual_U2_stock_imports_and4companions_prebound=True,first67_prepost_gap_not_rewritten=True,Lean_calls=0,API_calls=0))
    for row in prep['source_bindings']:verify(row)
    plan=load(BATCH/'target-plan.json');target=next(row for row in plan['targets'] if row['key']=='uniform');exports=[]
    for relative in [target['local_solution']]+[f'Definitions/{p.name}' for p in sorted((CONTEXT/'src/Definitions').glob('*.lean'))]:
        source=CONTEXT/'src'/relative;candidate=BATCH/'staged'/relative;assert source.read_bytes()==candidate.read_bytes()
        destination=OUT/'A-uniform-focused-native-export'/relative;destination.parent.mkdir(parents=True,exist_ok=True)
        assert not destination.exists();destination.write_bytes(source.read_bytes())
        module=relative[:-5].replace('/','.')
        exports.append(dict(module=module,role='complete122_proof_SOURCE_with_uniform_wrapper' if relative==target['local_solution'] else 'standalone_whole_definition_SOURCE',actual_success_call=last[module]['index'],actual_SOURCE=bind(source),candidate_SOURCE=bind(candidate),complete_export=bind(destination)))
    priorpath=OUT/'A-actual-independent-calls.json';prior=load(priorpath)
    assert len(prior['rows'])==67 and all(row['exit_code']==0 for row in prior['rows'])
    prior_summary=dict(first67_actual_calls=67,first67_actual_successes=67,first67_mathematical_complete_compiler_controls_PASS=True,
        first67_full_prepost_stock_PASS=False,first67_native_baseline_not_complete_for_platform_full_Mathlib_imports=True,
        missing_stock_modules=5299,additional_stock_companions=21196,no_backdated_precompile_evidence=True,
        moment_and_changing_other2_complete_repeated_prepost_scope_not_claimed=True,
        retained_actual_calls=bind(priorpath),original_preflight=bind(OUT/'A-personal-author-stock-preflight.json'),
        gap_diagnosis=bind(OUT/'A-stock-precompile-gap-diagnosis.json'),
        retained_pure_freeze_failures=[bind(OUT/'A-freeze-attempt1-source.py'),bind(OUT/'A-freeze-attempt1-terminal-error.txt'),bind(OUT/'A-freeze-attempt1-tool-result.json'),bind(OUT/'freeze_A_independent_v2.py')])
    command="$taskContext = '"+str(CONTEXT)+"'; @(Get-CimInstance Win32_Process | Where-Object { $_.Name -in @('lean.exe','lake.exe','python.exe') -and $_.CommandLine -and $_.CommandLine.Contains($taskContext) } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
    process=subprocess.run(['powershell','-NoProfile','-Command',command],capture_output=True);assert process.returncode==0
    live=json.loads(process.stdout.decode('utf-8-sig') or '[]');assert not live,live
    frozen=OUT/'A-uniform-focused-frozen-all-actual-calls.json';write(frozen,receipt)
    stable=list(walk(prep))+recorded+list(walk(stock))+files+list(walk(exports))+list(walk(prior_summary))
    stable += [bind(preparation),bind(callsfile),bind(stockpath),bind(stockpost),bind(frozen),bind(Path(__file__)),bind(OUT/'prepare_A_uniform_focused.py'),bind(OUT/'run_A_uniform_focused.py'),bind(OUT/'prepare_A_independent.py'),bind(OUT/'prepare_A_stock_supplement.py')]
    stable += [bind(p) for prefix in ['src','b'] for p in sorted((CONTEXT/prefix).rglob('*')) if p.is_file()]
    stable += [bind(CONTEXT/name) for name in ['lakefile.lean','lean-toolchain','lake-manifest.json','leaf.py']]
    # The earlier calls and records remain frozen evidence, but do not expand this final theorem scope.
    stable += list(walk(prior))+[bind(p) for p in sorted((OUT/'A-full-records').glob('*/*.jsonl'))]
    stable += [bind(p) for folder in sorted((OUT/'A-actual-runs').iterdir()) if folder.is_dir() for p in [folder/'intent.json',folder/'terminal-receipt.json'] if p.exists()]
    stable=list({identity(pathof(b)):b for b in stable}.values())
    remaining=[row for row in stable if identity(pathof(row)) not in baseline]
    print(f'U2 all stock matched; rehashing remaining {len(remaining)} non-stock bindings; all {len(stable)} bindings verified across the two stages.',flush=True)
    with ThreadPoolExecutor(max_workers=2) as pool:list(pool.map(verify,remaining))
    report=dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),verdict='PASS',status='PLATFORM_UNIFORM_FOCUSED_INDEPENDENT_FULL_PASS',role='independent',owner='graph_integration_audit_1008',lane=2,
        scope=SCOPE,private_project='.rt/gaui1008/u2',actual_calls=11,actual_successes=11,historical_actual_Lean_failures_in_U2=[],
        all_actual_handles_terminal=True,actual_own_U2_WMI_live_processes=live,all_required_final_SOURCE_and_controls_exit0=True,
        platform_independent_PASS=True,platform_independent_PASS_targets=[target['theorem_name']],standalone_new13_definition_independent_PASS=True,
        other_two_targets_platform_complete_prepost_PASS_not_claimed=True,prior67_context_scope=prior_summary,
        complete_original_forall_types=122,whole_definition_comparisons=29,whole_function_rfl=29,new13_definitions_are_subset_of_total29=True,strict_helper_pairs=len(helpers),
        actual_inventory_declarations=len(declarations),actual_visible_extra_declarations=len(extras),
        non_environment_compiler_extra_names=sorted(r['name'] for r in visibility if not r['actual_env_find_some']),
        inventory=inventory,typed_boundaries=15,actual_raw_contracts_complete_values_inferType_Std3_DAG=4,
        raw_type_Expr_equal_false=[r['actual'] for r in theorem_compare+definition_compare if not r['type_exprEqual']],
        raw_definition_Expr_equal_false=[r['actual'] for r in definition_compare if not r['value_exprEqual']],
        normalized_definition_Expr_equal_false=[r['actual'] for r in definition_compare if not r['normalized_value_exprEqual']],
        normalization='Expand only full-type/full-value Expr.equal paired proposition helpers from exact29 original function owners; all raw false observations retained; no binder/metadata/payload erasure',
        record_counts={module:len(rows) for module,rows in data.items()},actual_control_success_calls={module:last[module]['index'] for module in data},
        all_actual_math_closure_resolver_records=resolver,actual_resolver_origins=dict(origins),all_actual_U2_stock_imports_prebound_and_full_postcompile_rehash=True,
        baseline_and_SOURCE_before_every_actual_call_proven_by_retained_intent_timestamps=True,
        stock_prepost_count=len(baseline),stock_prepost_bytes=stock['stock_bytes'],all_actual_mathematical_inventory_values_types_Std3_inferType_complete=True,
        full_lossless_Expr_DAG_records=dag_total,full_lossless_Expr_DAG_nodes=dag_nodes,complete_SOURCE_exports=exports,full_control_records=files,
        Root_grant=prep['Root_grant'],author_report=prep['author_report'],Root_author_pin=prep['Root_pin'],source_preparation=bind(preparation),
        complete_actual_stock_prefreeze=prep['complete_actual_stock_prefreeze'],stock_postcompile=bind(stockpost),all_actual_calls_frozen=bind(frozen),
        stable_bindings=len(stable),stable_bytes=sum(row['bytes'] for row in stable),stable_files=stable,mismatches=0,
        full_stable_verification_stages=dict(stock_complete_stream_rehash=len(baseline),other_complete_stream_rehash=len(remaining),no_binding_omitted=True),
        uploaded=False,API_calls=0,credential_reads=0,shared_scope_docs_writes=0,foreign_mathematical_objects_borrowed=False,
        mathematical_scope=dict(actual_weighted_uniform_A=True,all_n_ge1=True,all_rational_quartics_degree_le4=True,coefficient_independent_epsilon_tends_zero=True,arbitrary_signs_and_changing_coefficients=True,
            no_assumed_Summable_HasSum_moment_bound_coefficient_growth_or_parity=True,integer_preimage_height_J_exact_fstar_irrationality_not_claimed=True,
            unrestricted_exponentially_small_forms_not_stronger_than_irrationality=True,structured_selected_inverse_image_height_margin_is_genuine_sufficient_condition=True),
        elapsed_seconds=time.monotonic()-started)
    write(final,report)
    print(json.dumps(dict(verdict='PASS',scope=SCOPE,actual_calls=11,stable_bindings=len(stable),stable_bytes=report['stable_bytes'],DAG_records=dag_total,DAG_nodes=dag_nodes,audit=bind(final),elapsed_seconds=time.monotonic()-started)),flush=True)

if __name__=='__main__':main()
