"""Append-only private audit adaptation after retained real control failures.

Copies only explicitly supplied serializer SOURCE. No Lean runs here, no shared
source edits, no frozen preparation changes, and no borrowed proof objects.
"""
import difflib
from pathlib import Path
import prepare as p


def main():
    p.native_gate()
    assert not (p.OUT/'audit-adaptation.json').exists()
    receipt=p.load(p.OUT/'compile-receipt.json')
    failed=next(r for r in reversed(receipt['rows']) if
        r['label']=='control-JetsFullTypeAudit' and r['exit_code']==1)
    assert failed['attempt']==2 and failed['stdout']['bytes']==1184199355
    extra=[]
    for module,expected in [
        ('IndependentExprDagV3','1322612913bdc66d360720f64f9c72fa6047234e0717024ebb01a6c1303044e7'),
        ('IndependentExprDagValidationV3','5c8ef7f4dc5c512497479b47ec4cd50280042febcc7ed45ed793360ad75ab693')]:
        supplied=p.TASK/'.rt/ni1'/(module+'.lean')
        assert p.sha(supplied)==expected
        target=p.PROJECT/(module+'.lean')
        obj=p.PROJECT/'b/lib/lean'/(module+'.olean')
        assert not target.exists() and not obj.exists()
        snapshot=p.OUT/'copied-serializer-source'/(module+'.lean')
        p.write(snapshot,supplied.read_bytes())
        p.write(target,supplied.read_bytes())
        assert p.sha(target)==expected
        assert len(str(obj.resolve()))+64<=259
        extra.append(dict(module=module,project_relative=module+'.lean',
            supplied_source=p.binding(supplied),immutable_copied_source=p.binding(snapshot),
            initial_project_copy=p.binding(target),object_initially_absent=True,
            object_path_plus64=len(str(obj.resolve()))+64))
    control=p.PROJECT/'JetsFullTypeAudit.lean'
    old=control.read_text(encoding='utf-8-sig')
    marker='\nopen Lean Meta\n'
    assert old.count(marker)==1
    initial_prefix,tail=old.split(marker)
    assert tail.count('run_meta do')==1
    new_prefix='import IndependentExprDagV3\n'+initial_prefix
    tail=tail.replace('set_option pp.proofs true\n',
        'set_option pp.proofs true\nset_option maxHeartbeats 0\nset_option maxRecDepth 20000\n')
    before='    IO.println (Json.mkObj [("kind",Json.str "actual_complete_source_expected_type"),'
    added='''    let sourceDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    let expectedDag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
    let (sourceType,sourceValue) ← ofExcept (IndependentLosslessExprDagV1.decode sourceDag)
    let (expectedType,expectedValue) ← ofExcept (IndependentLosslessExprDagV1.decode expectedDag)
    let sourceTypeEqual := Expr.equal a.type sourceType
    let sourceValueEqual := Expr.equal a.value sourceValue
    let expectedTypeEqual := Expr.equal b.type expectedType
    let expectedValueEqual := Expr.equal b.value expectedValue
    unless sourceTypeEqual && sourceValueEqual && expectedTypeEqual && expectedValueEqual do
      throwError "Lossless original theorem/expected theorem expression reconstruction failed: {actual}"
'''
    assert tail.count(before)==1
    tail=tail.replace(before,added+before)
    raw='''      ("full_source_type_expression_repr",Json.str (reprStr a.type)),
      ("full_expected_type_expression_repr",Json.str (reprStr b.type)),
      ("full_source_proof_expression_repr",Json.str (reprStr a.value)),'''
    dag='''      ("full_source_type_and_proof_expression_dag",sourceDag),
      ("full_expected_type_and_proof_expression_dag",expectedDag),
      ("source_type_reconstructed_Expr_equal",toJson sourceTypeEqual),
      ("source_proof_reconstructed_Expr_equal",toJson sourceValueEqual),
      ("expected_type_reconstructed_Expr_equal",toJson expectedTypeEqual),
      ("expected_proof_reconstructed_Expr_equal",toJson expectedValueEqual),'''
    assert tail.count(raw)==1
    tail=tail.replace(raw,dag)
    new=new_prefix+marker+tail
    assert p.statement_headers(old.encode())==p.statement_headers(new.encode())
    assert new.split(marker)[0].removeprefix('import IndependentExprDagV3\n')==initial_prefix
    retained=p.OUT/'retained-private-fulltype-before-DAG-adaptation.lean'
    p.write(retained,control.read_bytes())
    p.write(control,new)
    diff=p.OUT/'private-DAG-audit-adaptation.diff'
    p.write(diff,''.join(difflib.unified_diff(old.splitlines(keepends=True),
        new.splitlines(keepends=True),fromfile='retained-raw-audit-actually-failed',
        tofile='private-lossless-DAG-audit-with-kernel-comparison')))
    resolver=p.PROJECT/'resolver_dag.lean'
    original_resolver=(p.PROJECT/'resolver.lean').read_text(encoding='utf-8-sig')
    assert original_resolver.count('] do')==1
    p.write(resolver,original_resolver.replace('] do',', `IndependentExprDagV3, `IndependentExprDagValidationV3] do'))
    driver=p.OUT/'execute_dag.py'
    original=(p.OUT/'execute.py').read_text(encoding='utf-8-sig')
    original=original.replace('OUT, TASK, ROOT, PROJECT = p.OUT, p.TASK, p.ROOT, p.PROJECT',
        '''OUT, TASK, ROOT, PROJECT = p.OUT, p.TASK, p.ROOT, p.PROJECT

def streaming_sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while block:=f.read(8*1024*1024):h.update(block)
    return h.hexdigest()

p.sha=streaming_sha''')
    original=original.replace("    allowed={r['task_relative']:r for r in ledger['allowed_current_source_bindings']}",
        """    allowed={r['task_relative']:r for r in ledger['allowed_current_source_bindings']}
    adaptation=p.load(OUT/'audit-adaptation.json')
    assert adaptation['Root_explicit_audit_adaptation_authorization']
    assert adaptation['original26_expected_headers_and_proof_bodies_unchanged']
    for row in adaptation['extra_source_controls']:
        assert p.binding(PROJECT/row['project_relative'])==row['initial_project_copy']
        assert p.binding(TASK/row['immutable_copied_source']['task_relative'])==row['immutable_copied_source']""")
    original=original.replace("        actual=p.binding(path);assert allowed[actual['task_relative']]==actual",
        """        actual=p.binding(path)
        if path==PROJECT/'JetsFullTypeAudit.lean':
            assert actual==adaptation['adapted_control']
            retained=TASK/adaptation['retained_before']['task_relative']
            marker=b'\\nopen Lean Meta\\n'
            assert path.read_bytes().split(marker)[0].removeprefix(b'import IndependentExprDagV3\\n')==retained.read_bytes().split(marker)[0]
        else:assert allowed[actual['task_relative']]==actual""")
    original=original.replace("        if is_control:\n            marker=b'\\nopen Lean Meta\\n'",
        "        if is_control and path!=PROJECT/'JetsFullTypeAudit.lean':\n            marker=b'\\nopen Lean Meta\\n'")
    original=original.replace("        print((result.stdout+result.stderr).decode('utf-8',errors='replace'),flush=True)",
        "        print((result.stdout+result.stderr)[-8000:].decode('utf-8',errors='replace'),flush=True)")
    original=original.replace("    for row in state['controls']:\n        obj='b/lib/lean/'+row['module']+'.olean'",
        """    for row in p.load(OUT/'audit-adaptation.json')['extra_source_controls']:
        obj='b/lib/lean/'+row['module']+'.olean'
        run('control-'+row['module'],['-o',obj,row['project_relative']])
    for row in state['controls']:
        obj='b/lib/lean/'+row['module']+'.olean'""")
    original=original.replace("run('own-object-resolution',['resolver.lean'])","run('own-object-resolution',['resolver_dag.lean'])")
    original=original.replace('assert len(latest)==23','assert len(latest)==25')
    original=original.replace('assert len(resolved)==21','assert len(resolved)==23')
    p.write(driver,original)
    doc=dict(role='Private audit representation adaptation; mathematical source unchanged',
        Root_explicit_audit_adaptation_authorization=True,
        authorized_changes=['lossless Expr DAG from explicitly supplied serializer source',
            'maxHeartbeats 0 in private audit control','serial own-cache fresh serializer source compilation'],
        after_actual_failed_call=dict(label=failed['label'],attempt=failed['attempt'],
            exit_code=failed['exit_code'],stdout_bytes=failed['stdout']['bytes']),
        original26_expected_headers_and_proof_bodies_unchanged=True,
        structural_Expr_equal_not_a_replacement_for_kernel_isDefEq=True,
        initial_shared_candidate_and_original5_38_bindings_unchanged=True,
        retained_before=p.binding(retained),diff=p.binding(diff),
        adapted_control=p.binding(control),adapted_resolver=p.binding(resolver),
        adapted_driver=p.binding(driver),extra_source_controls=extra,
        additional_future_calls=2,expected_final_success_labels=25,
        expected_final_own_object_resolutions=23,objects_borrowed=False)
    p.dump(p.OUT/'audit-adaptation.json',doc)
    p.native_gate()
    print('PRIVATE_DAG_AUDIT_ADAPTATION_PREPARED',p.sha(driver),p.sha(control))


if __name__=='__main__':main()
