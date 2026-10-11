"""Freeze the resumed local platform author batch after actual controls pass."""
from pathlib import Path
import collections, hashlib, json, sys
sys.dont_write_bytecode=True
import prepare as p
import execute_oracles as e

def main():
    state=e.gate()
    receipt=p.load(p.OUT/'compile-receipt.json')
    prefix=dict(receipt,rows=receipt['rows'][:54])
    prefix_bytes=(json.dumps(prefix,ensure_ascii=False,indent=2)+'\n').encode()
    assert hashlib.sha256(prefix_bytes).hexdigest()=='a675959af33c787a84cae6b799dee1ad2b9d6ee479c6f0fe9cd377ef807e7af3'
    p.write(p.OUT/'original-54-compile-receipt-restored-bytes.json',prefix_bytes)
    stable={}
    def bind(row):
        path=p.bound_path(row)
        assert path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256'],str(path)
        identity=str(path.resolve())
        if identity in stable:
            previous=stable[identity]
            assert previous['sha256']==row['sha256'] and previous['bytes']==row['bytes'],str(path)
        else:stable[identity]=row
        return path
    def add(path):return bind(p.binding(path))
    frozen=p.load(p.OUT/'preparation-verification.json')
    assert len(frozen['files'])==80
    for row in frozen['files']:bind(row)
    native_author=p.load(p.AUTHOR/'author-audit.json')
    native_ind=p.load(p.INDEPENDENT/'independent-review.json')
    for report in [native_author,native_ind]:
        for row in report['stable_files']:bind(row)
    add(p.AUTHOR/'author-audit.json');add(p.INDEPENDENT/'independent-review.json')
    latest={r['label']:r for r in receipt['rows']}
    resolver=[]
    for row in receipt['rows']:
        for binding in row['input_bindings']+row['output_bindings']:
            bind(binding)
        for key in ['stdout','stderr','log','exit_file','selected_paths']:
            if row[key] is not None:bind(row[key])
        assert int(bind(row['exit_file']).read_text().strip())==row['exit_code']
        assert bind(row['log']).read_bytes()==bind(row['stdout']).read_bytes()+bind(row['stderr']).read_bytes()
        for category,retained in [('input_bindings','retained_input_bindings'),('output_bindings','retained_output_bindings')]:
            assert len(row[category])==len(row[retained])
            for original,snapshot in zip(row[category],row[retained]):
                assert original['task_relative']==snapshot['original_task_relative']
                assert bind(original).read_bytes()==bind(snapshot['snapshot_binding']).read_bytes()
        if row['selected_paths'] is not None:
            selected=p.load(bind(row['selected_paths']))
            normalized={}
            for key in ['LEAN_PATH','LEAN_SRC_PATH']:
                normalized[key]=[]
                for raw in selected[key]['filtered']:
                    resolved=(p.PROJECT/Path(raw)).resolve()
                    assert resolved.is_relative_to(p.PROJECT.resolve()) or resolved.is_relative_to((p.ROOT/'.lake/packages').resolve()),str(resolved)
                    normalized[key].append(str(resolved))
            resolver.append(dict(label=row['label'],attempt=row['attempt'],actual_exit=row['exit_code'],paths=normalized))
        assert row['failure_retained']==(row['exit_code']!=0)
        if 'actual_executor_binding' in row:bind(row['actual_executor_binding'])
    assert latest['resume-build-2-reference-v2']['exit_code']==0
    controls=p.load(p.OUT/'author-controls-plan-v2-2026-10-07.json')
    native_label='author-native-reachable-v1'
    native_row=latest[native_label]
    assert native_row['exit_code']==0
    native=e.rows(bind(native_row['stdout']))
    native_defs={r['declaration']:r for r in native if r['kind']=='definition_full_expression'}
    native_proofs={r['declaration']:r for r in native if r['kind']=='proof_full_type'}
    native_aux={r['declaration']:r for r in native if r['kind']=='generated_helper_full_type'}
    assert set(native_defs)==set(controls['native_definitions']) and len(native_defs)==11
    assert set(native_proofs)==set(controls['native_proofs']) and len(native_proofs)==34
    assert set(native_aux)==set(controls['generated_auxiliaries']) and len(native_aux)==1
    original_native=e.rows(p.OUT/'native-control-NativeNumeratorPFSourceControl.log')
    original_byname={r['declaration']:r for r in original_native}
    for name in controls['native_source_alias_spans']:
        n=name['declaration']
        for field in ['type_expression_repr','full_value_expression_repr']:
            assert native_defs[n][field]==original_byname[n][field]
    old_boundary={r['declaration']:r for r in e.rows(p.OUT/'native-control-NativeNumeratorPFAuthorBoundaryControl.log') if r['kind']=='proof_full_type'}
    comparisons=[];staged_records={};all_actual=native.copy()
    plan=p.load(p.OUT/'target-plan.json')
    definition=(p.OUT/'staged'/plan['local_definition']).read_text(encoding='utf-8-sig')
    request=p.load(p.OUT/'definitions-request.json')
    assert len(request)==1 and request[0]['definition']==definition
    problems=p.load(p.OUT/'problems-request.json')['problems']
    assert len(problems)==3
    for i,(target,control,problem) in enumerate(zip(plan['targets'],controls['staged_controls'],problems)):
        suffix=p.SUFFIXES[i]
        label='author-staged-'+suffix+'-v2'
        row=latest[label];assert row['exit_code']==0
        actual=e.rows(bind(row['stdout']));staged_records[suffix]=actual;all_actual+=actual
        bykind=collections.defaultdict(list)
        for record in actual:bykind[record['kind']].append(record)
        own_defs={r['declaration']:r for r in bykind['definition_full_expression']}
        own_proofs={r['declaration']:r for r in bykind['proof_full_type']}
        assert len(own_proofs)==35
        for name,expected in native_defs.items():
            assert name in own_defs
            for field in ['level_parameters','type_expression_repr','full_value_expression_repr']:
                assert own_defs[name][field]==expected[field],(suffix,name,field)
        for name,expected in native_proofs.items():
            staged_name=control['renamed_actual'] if name==target['theorem_name'] else name
            assert own_proofs[staged_name]['full_type_expression_repr']==expected['full_type_expression_repr'],(suffix,name)
        assert own_proofs['solution']['full_type_expression_repr']==native_proofs[target['theorem_name']]['full_type_expression_repr']
        aux={r['declaration']:r for r in bykind['generated_helper_full_type']}
        assert set(aux)==set(native_aux)
        for name,expected in native_aux.items():assert aux[name]['full_type_expression_repr']==expected['full_type_expression_repr']
        assert len(bykind['definition_whole_kernel_and_expr_equal'])==5
        for record in bykind['definition_whole_kernel_and_expr_equal']:
            assert all(record[key] for key in ['type_kernel_equal','full_value_kernel_equal','type_Expr_equal','full_value_Expr_equal'])
            expected=native_defs[record['declaration']]
            assert record['original_type_expression_repr']==record['alias_type_expression_repr']==expected['type_expression_repr']
            assert record['original_full_value_expression_repr']==record['alias_full_value_expression_repr']==expected['full_value_expression_repr']
        assert len(bykind['whole_function_rfl'])==5
        assert len(bykind['exact_forall_endpoint_proof'])==3
        assert len(bykind['explicit_endpoint_type_kernel'])==4 and all(r['whole_type_kernel_equal'] for r in bykind['explicit_endpoint_type_kernel'])
        assert len(bykind['closed_boundary_proof'])==9
        for record in bykind['closed_boundary_proof']:
            assert record['full_type_expression_repr']==old_boundary[record['declaration']]['full_type_expression_repr']
        inventory=bykind['private_helper_inventory'];assert len(inventory)==1
        covered={r['declaration'] for r in actual if r['kind'] in ['definition_full_expression','private_helper_full_type']}
        assert set(inventory[0]['names'])<=covered
        relative=target['local_solution'];source=(p.OUT/'staged'/relative).read_text(encoding='utf-8-sig')
        assert 'by sorry' not in source and 'sorryAx' not in source
        assert not any(line.startswith('import missions.') or line.startswith('import Solutions.') or line.startswith('import Theorems.') for line in source.splitlines())
        reference=(p.OUT/'staged'/target['local_reference']).read_text(encoding='utf-8-sig')
        assert reference==problem['preamble']+'\n'+problem['formal_statement']+'\n'
        comparisons.append(dict(solution=suffix,actual_control=label,definition_full_type_value_equal=11,
            native_named_proof_full_types_equal=34,solution_full_type_equal=1,generated_helpers_equal=1,
            full_definition_Expr_equal_and_kernel_equal=5,whole_function_rfl=5,
            exact_forall_proofs=3,actual_full_type_kernel_equal=4,closed_boundary_types_equal=9,
            internal_or_private_helpers=inventory[0]['names'],all_private_helpers_covered=True))
    axiom_records=[r for r in all_actual if 'axioms' in r]
    assert axiom_records and all(set(r['axioms'])<=p.STD for r in axiom_records)
    payloads=[]
    for relative in [plan['local_definition']]+[t['local_'+kind] for t in plan['targets'] for kind in ['solution','reference']]:
        a=p.OUT/'staged'/relative;b=p.PROJECT/relative
        assert a.read_bytes()==b.read_bytes();add(a);add(b);payloads.append(p.binding(a))
    for source in p.OUT.iterdir():
        if source.is_file() and source.suffix in ['.py','.lean','.json','.txt','.md','.inc','.log'] and source.name not in ['author-audit.json','AUTHOR_SHA256SUMS.txt']:
            add(source)
    for control in [controls['native_control']]+[r['label'] for r in controls['staged_controls']]:add(p.PROJECT/(control+'.lean'))
    add(p.PROJECT/'lean_call_v2_20261007.py');add(p.PROJECT/'lean_call_v3_20261007.py')
    checks=[dict(name=name,passed=True) for name in [
        'immutable preparation 80 bindings', 'immutable native author and independent reports and bindings',
        'original 54 receipt rows byte identical', 'all actual attempts retained with exact inputs outputs and exits',
        'all retained input/output snapshots equal originals', 'own-project and fixed-package actual resolver paths',
        'missing reference actual exit 0 and own object reused', 'actual source graph 545 and minimal reachable closure',
        'five pure new definitions and complete inlined 18 PF plus 16 parent proofs',
        'all eleven native definition full types and full values', 'all 34 native named proof full types and generated equation helper',
        'three staged proof environments definitions identical to actual native expressions',
        'three solutions exact full native types', 'all three unchanged exact forall endpoints in every staged environment',
        'all five new definitions actual Expr.equal and full isDefEq', 'all five whole-function rfl proofs per environment',
        'closed actual zero m0 X8 X9 two-pole weighted boundaries', 'all private and internal module helpers fully audited',
        'all actual axiom lists restricted to standard three', 'definition and problem requests exact staged bytes',
        'no complete Solution source placeholders or Root proof imports', 'all seven staged and pa1 payload bytes equal',
        'compiler failure and orchestration failures explicit and preserved', 'source-and-receipt author hash freeze']]
    failures=[r for r in receipt['rows'] if r['exit_code']!=0]
    failure_notes=dict(
        role='Explicit continuation history; failed calls are never counted as successful controls',
        orphan_prelaunch_failure=dict(command_source=p.binding(p.OUT/'run_author_controls_20261007.py'),
            actual_process_exit=1,Lean_started=False,
            evidence=p.binding(p.OUT/'resume-prelaunch-failure-and-orphan-2026-10-07.json')),
        compiler_failures=[dict(label=r['label'],attempt=r['attempt'],actual_Lean_exit=r['exit_code'],
            actual_inputs=r['input_bindings'],actual_stdout=r['stdout'],actual_stderr=r['stderr'],
            actual_exit_file=r['exit_file'],input_snapshots=r['retained_input_bindings']) for r in failures],
        reference_postcheck_failure=dict(actual_Lean_exit=0,actual_driver_exit=1,
            cause='Relative child LEAN_PATH entries were initially tested in the parent cwd; corrected pure check resolves them against the actual pa1 child cwd.',
            source=p.binding(p.OUT/'execute_author_v2_20261007.py'),
            recovery=p.binding(p.OUT/'reference-v2-contextual-resolver-validation-2026-10-07.json')),
        failed_polynomial_v1_error_reporting=dict(actual_Lean_exit=1,actual_driver_exit=1,
            cause='Lean unknownIdentifier on an unreachable extra weighted bridge; while printing the fully saved UTF-8 child output, default GBK stdout also raised UnicodeEncodeError.',
            source=p.binding(p.OUT/'execute_author_v3_20261007.py'),
            retained_full_child_log=latest['author-staged-polynomial-v1']['log'],
            repair='Separate V2 controls omit this unused extra boundary; V4 executor prints UTF-8. No endpoint or seven payload source was changed.'),
        pure_preparation_errors=dict(Lean_started=False,
            causes=['An initial temporary V2 preparer read UTF-8 Lean source with default GBK and stopped before writing any new control.',
                    'The subsequent attempt to start the not-yet-created V4 driver returned file-not-found before Lean.'],
            repair_source=p.binding(p.OUT/'prepare_author_controls_v2_20261007.py')))
    p.dump(p.OUT/'continuation-failures-2026-10-07.json',failure_notes)
    add(p.OUT/'continuation-failures-2026-10-07.json')
    report=dict(verdict='PASS',role='continued same platform AUTHOR batch; independent platform review still required',
        preparation_sha256=p.sha(p.OUT/'preparation-verification.json'),checks=checks,
        native_author_provenance='Prior frozen native author report reused; this continuation restores the same platform author batch. No new native authorship or fresh independent review is attributed to this resumed agent.',
        fresh_independent_review_claimed=False,same_author_batch_objects_reused=True,
        original_54_actual_successes_reused=True,original_43_not_rerun=True,
        actual_receipt_rows=len(receipt['rows']),actual_successful_rows=sum(r['exit_code']==0 for r in receipt['rows']),
        actual_failed_Lean_rows=len(failures),failed_runs_retained_and_excluded=failures,
        prelaunch_orphan_and_driver_failure=p.binding(p.OUT/'resume-prelaunch-failure-and-orphan-2026-10-07.json'),
        complete_continuation_failure_classification=p.binding(p.OUT/'continuation-failures-2026-10-07.json'),
        reference_postcheck_context_failure_and_actual_success=p.binding(p.OUT/'reference-v2-contextual-resolver-validation-2026-10-07.json'),
        excluded_unreachable_weighted_boundary=dict(names=controls['excluded_other_unreached_boundary'],
            reason=controls['unreached_weighted_boundary_reason'],original_native_proof_preserved=True),
        new_actual_successful_Lean_calls=len(receipt['rows'])-54-len(failures),
        comparisons=comparisons,actual_native_records=native,actual_staged_records=staged_records,
        actual_axiom_records=len(axiom_records),actual_resolver_records=resolver,
        standard_axioms=sorted(p.STD),raw_full_Expr_repr_used=True,lossless_DAG_fallback_used=False,
        seven_payloads=payloads,stable_files=sorted(stable.values(),key=lambda r:r.get('task_relative',r.get('root_relative',''))),
        Root_modules_installed=False,Root_scope_modified=False,API_executed=False,credentials_read=False,
        mission_destination='new public mission per user 2026-10-07; no writes to original mission',
        mathematical_boundary='Generic finite proper-numerator PF and actual jet injectivity only; this does not close irrationality or J/height/denominator asymptotics.')
    p.dump(p.OUT/'author-audit.json',report)
    p.write(p.OUT/'AUTHOR_SHA256SUMS.txt',''.join(r['sha256']+'  '+r.get('task_relative',r.get('root_relative',''))+'\n' for r in report['stable_files']))
    print(json.dumps(dict(verdict=report['verdict'],checks=len(checks),stable_files=len(stable),
        actual_rows=report['actual_receipt_rows'],actual_successes=report['actual_successful_rows'],actual_failures=len(failures),
        actual_axiom_records=len(axiom_records),author_audit_sha256=p.sha(p.OUT/'author-audit.json'))))

if __name__=='__main__':main()
