"""Freeze complete actual independent evidence; no compiler or API invocation."""
from __future__ import annotations
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
from pathlib import Path
import hashlib,json,re,subprocess,sys,time

sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1];ROOT=TASK.parents[1];PROJECT=TASK/'.rt/aui1'
STD3={'propext','Classical.choice','Quot.sound'}

def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def stream(p):
    h=hashlib.sha256();size=0
    with p.open('rb') as f:
        while b:=f.read(1024*1024):h.update(b);size+=len(b)
    return size,h.hexdigest()
def bind(p):
    size,digest=stream(p)
    if p.is_relative_to(TASK):return {'task_relative':p.relative_to(TASK).as_posix(),'bytes':size,'sha256':digest}
    if p.is_relative_to(ROOT):return {'root_relative':p.relative_to(ROOT).as_posix(),'bytes':size,'sha256':digest}
    return {'absolute_path':str(p),'bytes':size,'sha256':digest}
def path_of(row):
    if 'task_relative' in row:return TASK/row['task_relative']
    if 'root_relative' in row:return ROOT/row['root_relative']
    return Path(row['absolute_path'])
def walk(obj):
    if isinstance(obj,dict):
        if 'bytes' in obj and 'sha256' in obj and any(k in obj for k in ('task_relative','root_relative','absolute_path')):yield obj
        else:
            for v in obj.values():yield from walk(v)
    elif isinstance(obj,list):
        for v in obj:yield from walk(v)
def verify(row):
    size,digest=stream(path_of(row));assert size==row['bytes'] and digest==row['sha256'],(row,size,digest)
def new(p,obj):
    assert not p.exists(),'Do not replace frozen audit: '+str(p)
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def records(row):
    result=[]
    with path_of(row['stdout']).open(encoding='utf-8') as f:
        for line in f:
            if line.startswith('AU_RECORD|'):result.append(json.loads(line[10:]))
    return result
def check_value(r):
    for k in ['axioms','actual_axioms','expected_axioms']:
        if k in r:assert set(r[k])<=STD3,(k,r)
    for k in ['value_type_isDefEq','type_isDefEq','actual_value_typed','expected_value_typed']:
        if k in r:assert r[k] is True,(k,r)
    if 'value_raw_format' in r:
        assert r['value_raw_format']=='lossless lean-expr-dag-v1; full type_root and value_root'
        payload=json.loads(r['value_raw']);assert payload['format']=='lean-expr-dag-v1'
        assert payload['nodes']
        assert 0<=payload['type_root']<len(payload['nodes']) and 0<=payload['value_root']<len(payload['nodes'])
        for k in ['all_fields_type_Expr_equal','all_fields_value_Expr_equal','full_type_kernel_equal','full_value_kernel_equal']:
            assert r[k] is True,(k,r)
        return len(payload['nodes'])
    return 0
def headers(text):
    return {m.group(1):text[m.start():text.index(':=',m.end())].rstrip() for m in re.finditer(r'(?m)^theorem (\w+)\b',text)}
def definitions(text):
    return {m.group(1):m.group(0).strip() for m in re.finditer(r'(?ms)^def (\w+)\b.*?(?=\n\n)',text)}

def main():
    sys.stdout.reconfigure(encoding='utf-8');start=time.monotonic()
    prep=load(OUT/'source-preparation.json');personal=load(OUT/'personal-author-and-import-rehash.json')
    receipt=load(OUT/'actual-independent-calls.json');calls=receipt['rows']
    assert all(isinstance(r['exit_code'],int) for r in calls)
    assert [r['index'] for r in calls]==list(range(1,len(calls)+1))
    assert calls[0]['label']=='runtime' and calls[0]['exit_code']==0
    assert 'Lean (version 4.33.1,' in path_of(calls[0]['stdout']).read_text(encoding='utf-8')
    recorded=list(walk(receipt))+list(walk(prep))
    with ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(verify,recorded))
    for r in calls:
        assert int(path_of(r['exit_file']).read_text())==r['exit_code']
        assert r['cwd']==str(PROJECT) and '-j1' in r['command']
        assert r['actual_environment']=={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'}
        selected=load(path_of(r['selected_paths']))
        for k in ['LEAN_PATH','LEAN_SRC_PATH']:
            for raw in selected[k]['filtered']:
                p=Path(raw).resolve()
                assert p.is_relative_to(PROJECT.resolve()) or p.is_relative_to((ROOT/'.lake/packages').resolve())
    latest={r['module']:r for r in calls if r['exit_code']==0 and r['module']}
    mathmods=[r['module'] for r in prep['original_source_gates']]
    controls=['AUExprDag','AUExprDagValidation','AURecords','AUKernelV2','AUBoundary','AUAllOriginalTypesV2','AURawGoalContractsV2','AUResolver']
    assert set(mathmods+controls)<=set(latest),set(mathmods+controls)-set(latest)
    mathematical_gates=[]
    for row in prep['original_source_gates']:
        src=PROJECT/'src'/(row['module'].replace('.','/')+'.lean')
        verify(row['original']);verify(row['compiled_author_export'])
        assert stream(src)==(row['compiled_author_export']['bytes'],row['compiled_author_export']['sha256'])
        old=path_of(row['original']).read_text(encoding='utf-8');fresh=src.read_text(encoding='utf-8')
        assert headers(old)==headers(fresh) and definitions(old)==definitions(fresh)
        stripped=re.sub(r'/-.*?-/', '', fresh, flags=re.S);stripped=re.sub(r'--[^\n]*','',stripped)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|partial)\b',stripped)
        mathematical_gates.append({'module':row['module'],'actual_call':latest[row['module']]['index'],
                                   'all_original_complete_headers_exact':True,'all_original_whole_definitions_exact':True,'own_source':bind(src)})
    allrecs={m:records(latest[m]) for m in controls if m not in ('AUExprDag','AUExprDagValidation')}
    nodes=0;dag_records=0
    for rs in allrecs.values():
        for r in rs:
            n=check_value(r);nodes+=n;dag_records+=bool(n)
    types=allrecs['AURecords'];kernel=allrecs['AUKernelV2'];alltypes=allrecs['AUAllOriginalTypesV2']
    theorem=[r for r in types if r['kind']=='theorem'];defs=[r for r in types if r['kind']=='definition']
    expected_names={r['name'] for r in prep['all_original_complete_headers'] if r['new_chain']}
    defnames={r['name'] for r in prep['all_whole_definitions']}
    assert len(theorem)==70 and {r['name'] for r in theorem}==expected_names
    assert len(defs)==29 and {r['name'] for r in defs}==defnames
    dc=[r for r in kernel if r['kind']=='definition_compare'];rfl=[r for r in kernel if r['kind']=='definition_rfl']
    tc=[r for r in kernel if r['kind']=='theorem_compare'];ev=[r for r in kernel if r['kind']=='expected_theorem_value']
    helpers=[r for r in kernel if r['kind']=='definition_helper_compare']
    assert len(dc)==len(rfl)==29 and {r['actual'] for r in dc}==defnames
    assert len(tc)==len(ev)==70 and {r['actual'] for r in tc}==expected_names
    for r in dc:assert r['value_isDefEq'] and r['normalized_value_isDefEq'],r
    for r in helpers:assert r['type_exprEqual'] and r['value_exprEqual'] and r['value_isDefEq'],r
    fulltypes=[r for r in alltypes if r['kind']=='all_original_complete_type_compare']
    fullvalues=[r for r in alltypes if r['kind']=='all_original_expected_full_proof']
    assert len(fulltypes)==len(fullvalues)==122
    assert {r['actual'] for r in fulltypes}=={r['name'] for r in prep['all_original_complete_headers']}
    inventory=[r for r in types if r['kind']=='module_inventory']
    declarations=[r for r in types if r['kind']=='module_declaration']
    extras=[r for r in types if r['kind']=='module_extra']
    visibility=[r for r in types if r['kind']=='compiler_extra_environment_visibility']
    assert len(inventory)==11 and {r['module'] for r in inventory}==set(mathmods)
    assert Counter(r['name'] for r in declarations)==Counter(n for r in inventory for n in r['constant_names'])
    assert Counter(r['name'] for r in visibility)==Counter(n for r in inventory for n in r['extra_names'])
    assert {r['name'] for r in extras}=={r['name'] for r in visibility if r['actual_env_find_some']}
    assert len(declarations)==291
    unseen=[r for r in visibility if not r['actual_env_find_some']]
    author=load(path_of(personal['author_report']))
    assert {r['name'] for r in unseen}==set(author['inventoried_extras_without_environment_declarations'])
    assert len(unseen)==37
    boundaries=allrecs['AUBoundary'];rawcontracts=allrecs['AURawGoalContractsV2']
    assert len(boundaries)==15 and all(r['kind']=='typed_boundary' for r in boundaries)
    assert len(rawcontracts)==4 and all(r['kind']=='independent_raw_goal_contract' for r in rawcontracts)
    fixture=[]
    with path_of(latest['AUExprDagValidation']['stdout']).open(encoding='utf-8') as f:
        for line in f:
            if line.startswith('{'):fixture.append(json.loads(line))
    assert len([r for r in fixture if r['kind']=='expr_dag_validation'])==20
    assert len([r for r in fixture if r['kind']=='expr_dag_small_source_validation'])==3
    assert all(r['all_fields_roundtrip'] and r['raw_repr_reconstruction_equal'] for r in fixture)
    resolver=allrecs['AUResolver'];classification=Counter();own=[]
    assert len({r['module'] for r in resolver})==len(resolver)
    reused_actual=[]
    frozen={str(path_of(r).resolve()).lower():r for r in personal['reusable_artifact_bindings']}
    for r in resolver:
        p=Path(r['canonical_olean']).resolve()
        assert p.exists()
        if p.is_relative_to(PROJECT.resolve()):
            kind='own_fresh_SOURCE_objects';own.append(r)
            assert r['module'] in mathmods
            assert p==(PROJECT/'b/lib/lean'/(r['module'].replace('.','/')+'.olean')).resolve()
        elif p.is_relative_to((ROOT/'.lake/packages').resolve()):kind='pinned_packages'
        else:
            assert '.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/' in p.as_posix(),r
            kind='intrinsic_Lean_4.33.1'
        classification[kind]+=1
        if kind!='own_fresh_SOURCE_objects':
            assert str(p).lower() in frozen,(p,'Actual object absent from pre-reuse personal freeze')
            reused_actual.append(frozen[str(p).lower()])
    assert len(own)==11 and {r['module'] for r in own}==set(mathmods)
    # Full package/intrinsic bytes checked again after all own SOURCE and controls.
    with ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(verify,personal['reusable_artifact_bindings']))
    command="$project = '"+str(PROJECT)+"'; @(Get-CimInstance Win32_Process | Where-Object { $_.Name -in @('lean.exe','lake.exe','python.exe') -and $_.CommandLine -and $_.CommandLine.Contains($project) } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
    check=subprocess.run(['powershell','-NoProfile','-Command',command],capture_output=True)
    assert check.returncode==0,check.stderr
    live=json.loads(check.stdout.decode('utf-8-sig') or '[]');assert not live,live
    record_files=[]
    for mod,rs in allrecs.items():
        target=OUT/'full-independent-records'/(mod+'.jsonl');target.parent.mkdir(exist_ok=True)
        assert not target.exists()
        with target.open('w',encoding='utf-8') as f:
            for r in rs:f.write(json.dumps(r,ensure_ascii=False,separators=(',',':'))+'\n')
        record_files.append(bind(target))
    new(OUT/'frozen-all-actual-calls.json',receipt)
    new(OUT/'lossless-DAG-fixtures.json',fixture)
    stable=list(recorded)+personal['reusable_artifact_bindings']+record_files
    # Never traverse the package junction while collecting own objects.
    own_files=[p for folder in ['src','controls','b'] for p in (PROJECT/folder).rglob('*') if p.is_file()]
    own_files.extend(p for p in PROJECT.iterdir() if p.is_file())
    own_files.extend(p for p in (PROJECT/'.lake').glob('lakefile.*') if p.is_file())
    stable.extend(bind(p) for p in sorted(own_files))
    stable.extend(bind(p) for p in [Path(__file__),OUT/'prepare_independent.py',OUT/'run_independent.py',OUT/'source-preparation.json',OUT/'personal-author-and-import-rehash.json',OUT/'Root-native-independent-lane1-grant.json',OUT/'frozen-all-actual-calls.json',OUT/'lossless-DAG-fixtures.json',OUT/'independent-wrapper-repair-v2.json',OUT/'independent-raw-limit-control-repair-v2.json',OUT/'independent-mathematical-review.json'])
    unique={str(path_of(r).resolve()).lower():r for r in stable}
    stable=list(unique.values())
    with ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(verify,stable))
    checks={
        'all_original_122_complete_forall_types_fresh_kernel_equal':True,
        'all_new_70_complete_forall_types_fresh_kernel_equal':True,
        'all_29_whole_definition_types_values_rfl_fresh':True,
        'all_291_actual_own_kernel_declarations_complete_types_values_inferType_Std3':True,
        'all_visible_compiler_helpers_inventoried_and_full_values_checked':True,
        'all_37_non_environment_compiler_extras_explicitly_retained_and_matched':True,
        'full_proof_fields_metadata_binders_universes_preserved_by_lossless_DAG':True,
        'all_20_constructor_and3_small_actual_source_fixtures_fresh_pass':True,
        'all_15_original_boundaries_and4_independent_expanded_goal_contracts_fresh_pass':True,
        'every_actual_own_import_is_fresh_aui1_own_SOURCE_object':True,
        'no_foreign_mathematical_objects_or_Root_fallback':True,
        'all_actual_import_package_intrinsic_bytes_pre_and_post_reuse_match':True,
        'all_failed_attempts_retained_and_handles_terminal_own_OS_zero':True,
        'all_required_final_actual_calls_exit0':True,
        'full_recorded_and_stable_bindings_stream_rehashed':True,
        'original_n_ge1_quartic_arbitrary_family_domains_unchanged_no_assumed_Summable_or_bounds':True}
    result={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'verdict':'PASS','status':'NATIVE_ACTUAL_WEIGHTED_UNIFORM_ANALYTIC_INDEPENDENT_PASS',
        'scope':'Actual coefficient-independent weighted Z9.A upper bound; no integer preimage/height/J/irrationality claim',
        'role':'independent','project':'.rt/aui1','lane':1,'actual_calls':len(calls),'success_calls':sum(r['exit_code']==0 for r in calls),
        'historical_failed_calls_preserved':[r['index'] for r in calls if r['exit_code']!=0],
        'all_actual_handles_terminal':True,'actual_own_OS_processes':live,'own_OS_command':command,
        'mathematical_source_gates':mathematical_gates,'all_original_complete_types':122,'new_chain_complete_types':70,
        'whole_definition_values_and_rfl':29,'strict_proposition_helper_pairs':len(helpers),'actual_own_declarations':len(declarations),
        'visible_extras':len(extras),'non_environment_compiler_extras':unseen,'typed_boundaries':15,'independently_written_raw_goal_contracts':4,
        'DAG_records':dag_records,'DAG_nodes':nodes,'constructor_fixtures':20,'small_source_fixtures':3,
        'actual_resolver_records':len(resolver),'actual_resolver_classifications':dict(classification),'all_11_own_actual_resolvers':own,
        'raw_Expr_equal_false_new_theorem_types':[r['actual'] for r in tc if not r['type_exprEqual']],
        'raw_Expr_equal_false_all_original_types':[r['actual'] for r in fulltypes if not r['type_exprEqual']],
        'raw_Expr_equal_false_definition_values':[r['actual'] for r in dc if not r['value_exprEqual']],
        'normalized_Expr_equal_false_definition_values':[r['actual'] for r in dc if not r['normalized_value_exprEqual']],
        'normalization_policy':'Only paired full-expression-equal proposition-valued own compiler helpers expanded; no binder/metadata/proof payload deletion',
        'checks':checks,'stable_files':stable,'stable_file_count':len(stable),'stable_bytes':sum(r['bytes'] for r in stable),
        'author_report':personal['author_report'],'Root_author_pin':personal['root_author_pin'],'full_independent_record_files':record_files,
        'actual_final_control_calls':{m:latest[m]['index'] for m in controls},
        'reusable_import_freeze_is_current_post_author_but_pre_independent_compilation':True,
        'foreign_math_objects':0,'API_calls':0,'credentials_accessed':False,'platform_uploaded':False,'elapsed_seconds':time.monotonic()-start}
    new(OUT/'independent-audit.json',result)
    print(json.dumps({'verdict':'PASS','actual_calls':len(calls),'complete_original_types':122,'new_types':70,'whole_defs':29,'actual_own_declarations':len(declarations),'stable_files':len(stable),'audit_sha256':bind(OUT/'independent-audit.json')['sha256'],'elapsed_seconds':time.monotonic()-start}))

if __name__=='__main__':main()
