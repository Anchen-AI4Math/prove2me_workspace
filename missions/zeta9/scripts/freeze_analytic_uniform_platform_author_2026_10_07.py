"""Freeze full actual platform author checks; never imply independent PASS/upload."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

TASK=Path(__file__).resolve().parents[1]
WORKSPACE=TASK.parents[1]
OUT=TASK/'formalization/platform/analytic-uniform-weighted'
PROJECT=TASK/'.rt/aupa1'
STD3={'propext','Classical.choice','Quot.sound'}


def load(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))


def binding(p):
    data=p.read_bytes(); base=TASK if p.is_relative_to(TASK) else WORKSPACE
    return {'task_relative' if base==TASK else 'root_relative':p.relative_to(base).as_posix(),
            'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}


def path_of(b):
    return (TASK if 'task_relative' in b else WORKSPACE)/b.get('task_relative',b.get('root_relative'))


def verify(b):
    assert binding(path_of(b))==b,b


def dump(p,v):
    assert not p.exists(),p
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')


def records(row):
    return [json.loads(line[10:]) for line in path_of(row['stdout']).read_text(encoding='utf-8').splitlines() if line.startswith('AF_RECORD|')]


def typed(rs):
    for r in rs:
        for k in ('axioms','actual_axioms','expected_axioms'):
            if k in r: assert set(r[k])<=STD3,r
        if 'actual_axioms' in r and 'expected_axioms' in r:
            assert set(r['actual_axioms'])==set(r['expected_axioms']),r
        for k in ('value_type_isDefEq','type_isDefEq','actual_value_typed','expected_value_typed',
                  'all_fields_type_Expr_equal','all_fields_value_Expr_equal','full_type_kernel_equal','full_value_kernel_equal'):
            if k in r: assert r[k] is True,r
        if 'value_raw_format' in r:
            dag=json.loads(r['value_raw'])
            assert dag['format']=='lean-expr-dag-v1' and dag['nodes']
            assert 0<=dag['type_root']<len(dag['nodes']) and 0<=dag['value_root']<len(dag['nodes'])


def prefixes(text):
    return {m.group(1):text[m.start():text.index(':=',m.end())+2] for m in re.finditer(r'(?m)^theorem (\w+)',text)}


def defs(text):
    return {m.group(1):m.group(0).strip() for m in re.finditer(r'(?ms)^def (\w+)\b.*?(?=\n\n)',text)}


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (OUT/'platform-author-complete-audit.json').exists()
    policy=load(OUT/'platform-native-inputs-v1.json')
    assert binding(OUT/'platform-native-inputs-v1.json')['sha256']=='a8749c3008e5d0b3fa3bb0d4cb1f91c1f304dafe56c1f34767506f3825207081'
    receipt_path=OUT/'platform-author-compile-receipt.json'; receipt=load(receipt_path); calls=receipt['rows']
    assert [r['index'] for r in calls]==list(range(1,len(calls)+1))
    bindcount=0
    for row in calls:
        assert row['actual_environment']=={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'}
        assert row['cwd']==str(PROJECT) and '-j1' in row['command']
        for k in ('stdout','stderr','combined','exit_file','selected_paths'):
            verify(row[k]); bindcount+=1
        assert int(path_of(row['exit_file']).read_text())==row['exit_code']
        for k in ('input_bindings','output_bindings'):
            for b in row[k]: verify(b); bindcount+=1
        for k in ('retained_inputs','retained_outputs'):
            for pair in row[k]:
                verify(pair['original_binding']); verify(pair['snapshot_binding']); bindcount+=2
                assert pair['original_binding']['bytes']==pair['snapshot_binding']['bytes']
                assert pair['original_binding']['sha256']==pair['snapshot_binding']['sha256']
        selected=load(path_of(row['selected_paths']))
        for key in ('LEAN_PATH','LEAN_SRC_PATH'):
            assert all(Path(x).resolve().is_relative_to(PROJECT.resolve()) or Path(x).resolve().is_relative_to((WORKSPACE/'.lake/packages').resolve()) for x in selected[key]['filtered'])
    last={}
    for r in calls:
        if r['exit_code']==0 and r['module']:last[r['module']]=r
    assert set(policy['source_compile_order'])<=set(last)
    repair_path=OUT/'private-helper-controls-v2-preparation.json';repair=load(repair_path)
    assert repair['normalized_full_Expr_equal_now_required']
    for row in repair['repairs']:
        verify(row['original_control']);verify(row['private_V2_SOURCE'])
        assert row['module'] in last
    prep=load(OUT/'source-preparation-v1.json'); plan=load(OUT/'target-plan.json')
    expected_names={r['full_name'] for r in prep['all_original_complete_theorem_prefixes']}
    expected_defs={r['full_name'] for r in prep['all_29_original_whole_definition_bodies']}
    assert len(expected_names)==122 and len(expected_defs)==29
    exports=[]
    for row in policy['sources']:
        if row['module'].startswith('AUPKernel_'):continue
        actual=last[row['module']]; source=Path(actual['command'][-1]); candidate=path_of(row['candidate'])
        verify(row['candidate']); assert prefixes(source.read_text(encoding='utf-8'))==prefixes(candidate.read_text(encoding='utf-8'))
        assert defs(source.read_text(encoding='utf-8'))==defs(candidate.read_text(encoding='utf-8'))
        target=OUT/'platform-author-native-export/src'/(row['module'].replace('.','/')+'.lean')
        target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():assert target.read_bytes()==source.read_bytes()
        else:target.write_bytes(source.read_bytes())
        exports.append({'module':row['module'],'actual_success_call':actual['index'],'actual_SOURCE':binding(source),'complete_export':binding(target)})
    for row in repair['repairs']:
        actual=last[row['module']];source=Path(actual['command'][-1]);candidate=path_of(row['original_control'])
        assert prefixes(source.read_text(encoding='utf-8'))==prefixes(candidate.read_text(encoding='utf-8'))
        assert defs(source.read_text(encoding='utf-8'))==defs(candidate.read_text(encoding='utf-8'))
        target=OUT/'platform-author-native-export/src'/(row['module']+'.lean')
        target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists();target.write_bytes(source.read_bytes())
        exports.append({'module':row['module'],'actual_success_call':actual['index'],'actual_SOURCE':binding(source),'complete_export':binding(target),'private_control_repair':True})
    fixture_row=last['AUPlatformExprDagValidation']
    fixtures=[json.loads(s) for s in path_of(fixture_row['stdout']).read_text(encoding='utf-8').splitlines() if s.startswith('{')]
    assert sum(r['kind']=='expr_dag_validation' for r in fixtures)==20
    assert sum(r['kind']=='expr_dag_small_source_validation' for r in fixtures)==3
    assert all(r['all_fields_roundtrip'] and r['raw_repr_reconstruction_equal'] for r in fixtures)
    target_audits=[]; record_files=[]
    for target in plan['targets']:
        key=target['key']; rs={s:records(last['AUP'+s+'_'+key+('_V2' if s=='Kernel' else '')]) for s in ('Types','Kernel','Boundary','Resolver')}
        for name,values in rs.items():
            typed(values)
            dest=OUT/'platform-author-full-records'/key/(name+'.jsonl'); assert not dest.exists()
            dest.parent.mkdir(parents=True,exist_ok=True)
            dest.write_text(''.join(json.dumps(v,ensure_ascii=False)+'\n' for v in values),encoding='utf-8');record_files.append(binding(dest))
        th=[r for r in rs['Types'] if r['kind']=='theorem'];df=[r for r in rs['Types'] if r['kind']=='definition']
        assert len(th)==122 and {r['name'] for r in th}==expected_names
        assert len(df)==29 and {r['name'] for r in df}==expected_defs
        tc=[r for r in rs['Kernel'] if r['kind']=='theorem_compare'];dc=[r for r in rs['Kernel'] if r['kind']=='definition_compare']
        rfl=[r for r in rs['Kernel'] if r['kind']=='definition_rfl'];aliases=[r for r in rs['Kernel'] if r['kind']=='expected_theorem_value']
        helpers=[r for r in rs['Kernel'] if r['kind']=='definition_helper_compare']
        assert len(tc)==len(aliases)==122 and len(dc)==len(rfl)==29
        assert {r['actual'] for r in tc}==expected_names and {r['actual'] for r in dc}==expected_defs
        assert all(r['value_isDefEq'] and r['normalized_value_isDefEq'] and r['normalized_value_exprEqual'] for r in dc)
        assert all(r['type_exprEqual'] and r['value_exprEqual'] and r['value_isDefEq'] for r in helpers)
        assert sum(r['kind']=='selected_wrapper_compare' for r in rs['Kernel'])==1
        assert sum(r['kind']=='selected_wrapper_proof' for r in rs['Kernel'])==1
        assert len(rs['Boundary'])==15 and all(r['kind']=='typed_boundary' for r in rs['Boundary'])
        inventory=[r for r in rs['Types'] if r['kind']=='module_inventory'];declarations=[r for r in rs['Types'] if r['kind']=='module_declaration']
        extras=[r for r in rs['Types'] if r['kind']=='module_extra']
        solution_module=target['local_solution'][:-5].replace('/','.')
        own_modules={r['module'] for r in plan['canonical_dependencies']}|{'Definitions.Def_ZetaNine_AnalyticUniformWeighted',solution_module}
        assert len(inventory)==4 and {r['module'] for r in inventory}==own_modules
        assert Counter(n for r in inventory for n in r['constant_names'])==Counter(r['name'] for r in declarations)
        origins=Counter(); own=[]
        for r in rs['Resolver']:
            p=Path(r['canonical_olean']).resolve(); assert p.exists()
            assert r['kind']=='actual_module_resolver'
            assert not r['module'].startswith('Theorems.')
            if p.is_relative_to(PROJECT.resolve()):kind='own_fresh_SOURCE'
            elif p.is_relative_to((WORKSPACE/'.lake/packages').resolve()):kind='pinned_packages'
            else:
                assert '.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/' in p.as_posix(),r
                kind='intrinsic_Lean4.33.1'
            origins[kind]+=1
            if r['module'] in own_modules:
                assert p==(PROJECT/'b/lib/lean'/(r['module'].replace('.','/')+'.olean')).resolve()
                own.append(r)
            assert not r['module'].startswith('Solutions.') or r['module']==solution_module
        assert len(own)==4
        target_audits.append({'target':target['theorem_name'],'solution_success_call':last[solution_module]['index'],
            'actual_control_modules':{s:'AUP'+s+'_'+key+('_V2' if s=='Kernel' else '') for s in ('Types','Kernel','Boundary','Resolver')},
            'actual_control_success_calls':{s:last['AUP'+s+'_'+key+('_V2' if s=='Kernel' else '')]['index'] for s in ('Types','Kernel','Boundary','Resolver')},
            'complete_types':122,'whole_definitions_and_rfl':29,'typed_boundaries':15,'strict_paired_proposition_helpers':len(helpers),
            'actual_module_declarations':len(declarations),'actual_visible_extra_records':len(extras),
            'all_module_inventory':inventory,'extra_names_without_environment_declarations':sorted({n for r in inventory for n in r['extra_names']}-{r['name'] for r in extras}),
            'raw_type_Expr_equal_false_retained':[r['actual'] for r in tc+dc if not r['type_exprEqual']],
            'raw_definition_value_Expr_equal_false_retained':[r['actual'] for r in dc if not r['value_exprEqual']],
            'normalized_definition_value_Expr_equal_false_retained':[r['actual'] for r in dc if not r['normalized_value_exprEqual']],
            'actual_resolver_count':len(rs['Resolver']),'actual_origins':dict(origins),'all_4_own_math_resolvers':own,
            'record_counts':{s:len(v) for s,v in rs.items()},'all_actual_expected_axiom_sets_exact_and_within_Std3':True})
    command="$project = '"+str(PROJECT)+"'; @(Get-CimInstance Win32_Process | Where-Object { $_.Name -in @('lean.exe','lake.exe','python.exe') -and $_.CommandLine -and $_.CommandLine.Contains($project) } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
    result=subprocess.run(['powershell','-NoProfile','-Command',command],capture_output=True)
    assert result.returncode==0;live=json.loads(result.stdout.decode('utf-8-sig') or '[]');assert not live,live
    frozen=OUT/'platform-author-complete-calls-frozen.json';dump(frozen,receipt)
    fixture_file=OUT/'platform-author-full-records/DAG-fixtures.json';dump(fixture_file,fixtures)
    audit={'status':'PLATFORM_AUTHOR_FULL_PASS_INDEPENDENT_TRANSPLANT_REVIEW_PENDING','role':'author','lane':1,
        'platform_independent_PASS':False,'uploaded':False,'API_calls':0,'credential_reads':0,'shared_scope_writes':0,
        'private_project':PROJECT.relative_to(TASK).as_posix(),'actual_calls':len(calls),'actual_successes':sum(r['exit_code']==0 for r in calls),
        'historical_failures_preserved':[r['index'] for r in calls if r['exit_code']!=0],
        'all_required_final_SOURCE_and_controls_exit0':True,'all_actual_handles_terminal':True,'actual_own_WMI_live_processes':live,
        'full_recorded_binding_rehash_count':bindcount,'complete122_proofs_in_each_of3_separate_contexts':True,
        'new_functions':13,'baseline_whole_definitions':29,'targets':target_audits,'complete_actual_SOURCE_exports':exports,
        'full_control_records':record_files,'lossless20_fixtures_and3_small_source_checks':binding(fixture_file),
        'own_SOURCE_input_policy':binding(OUT/'platform-native-inputs-v1.json'),'Root_grant':policy['Root_grant'],
        'strict_cross_owner_numeric_helper_control_repair':binding(repair_path),
        'frozen_actual_calls':binding(frozen),'original_SOURCE_handoff':policy['frozen_source_handoff'],
        'all_original_complete_headers_and_definition_bodies_unchanged':True,'foreign_math_proof_objects_borrowed':False,
        'normalization':'Only unfold full-expression-identical paired proposition-valued compiler helpers; raw full values retained; no binder/mdata erasure',
        'irrationality_integer_preimage_height_J_exact_fstar_remain_open':True,'freeze_script':binding(Path(__file__))}
    dump(OUT/'platform-author-complete-audit.json',audit)
    print(json.dumps({'status':audit['status'],'audit':binding(OUT/'platform-author-complete-audit.json'),'actual_calls':len(calls),'bindings':bindcount}))


if __name__=='__main__':main()
