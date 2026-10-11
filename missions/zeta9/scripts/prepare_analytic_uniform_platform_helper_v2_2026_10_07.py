"""Append strict audit-only handling of numeric proof helpers shared among baseline defs."""
import hashlib,json,re
from pathlib import Path
TASK=Path(__file__).resolve().parents[1]
OUT=TASK/'formalization/platform/analytic-uniform-weighted'
PROJECT=TASK/'.rt/aupa1'

def binding(p):
    d=p.read_bytes();return {'task_relative':p.relative_to(TASK).as_posix(),'bytes':len(d),'sha256':hashlib.sha256(d).hexdigest()}

def main():
    prep=json.loads((OUT/'source-preparation-v1.json').read_text(encoding='utf-8'))
    names=[r['full_name'] for r in prep['all_29_original_whole_definition_bodies']]
    assert len(set(names))==29
    actual='#['+', '.join('`'+n for n in names)+']'
    expected='#['+', '.join('`AFOriginalDefs.'+n.split('.')[-1] for n in names)+']'
    rows=[]
    for key in ('moment','changing','uniform'):
        source=PROJECT/'src'/('AUPKernel_'+key+'.lean')
        text=source.read_text(encoding='utf-8')
        old='if n.getPrefix.getPrefix == actual.getPrefix && n.getString!.startsWith "_proof_" then'
        assert text.count(old)==1
        text=text.replace(old,'if '+actual+'.contains n.getPrefix && n.getString!.startsWith "_proof_" then')
        old='if m.getPrefix.getPrefix == expected.getPrefix && m.getString!.startsWith "_proof_" then'
        assert text.count(old)==1
        text=text.replace(old,'if '+expected+'.contains m.getPrefix && m.getString!.startsWith "_proof_" then')
        text=text.replace('unless valueDefEq && normalizedDefEq do throwError "Full definition kernel mismatch {actual}"',
                          'unless valueDefEq && normalizedDefEq && normalizedEqual do throwError "Full definition kernel/structural mismatch {actual}"')
        target=PROJECT/'private-controls/v2/src'/('AUPKernel_'+key+'_V2.lean')
        assert not target.exists();target.parent.mkdir(parents=True,exist_ok=True);target.write_text(text,encoding='utf-8')
        # The only edits are actual/expected proof-helper owner recognition and
        # the stronger requirement of full normalized Expr.equal.
        before=source.read_text(encoding='utf-8')
        assert text.split('namespace AFOriginalDefs',1)[1].split('end AFExpected',1)[0]==before.split('namespace AFOriginalDefs',1)[1].split('end AFExpected',1)[0]
        rows.append({'target_key':key,'original_control':binding(source),'private_V2_SOURCE':binding(target),'module':target.stem})
    report={'status':'PURE_CONTROL_REPAIR_PREPARATION','actual_Lean_calls':0,'original_math_SOURCE_and_29_definition_values_unchanged':True,
      'reason':'New13 definitions share one source file; Real numeral proof helpers are reused across their original namespaces. First actual raw difference is tailCoefficient._proof_1/2 versus AFOriginalDefs.phase/tailCoefficient helpers.',
      'eligible_actual_owners_exact29_baseline_functions':names,'eligible_expected_owners_exact29_replicas':True,
      'every_pair_still_requires_full_type_and_value_Expr_equal_isDefEq_inferType_Std3_and_Prop':True,
      'no_binder_metadata_or_proof_payload_erasure':True,'normalized_full_Expr_equal_now_required':True,
      'original_success_and_false_diagnostics_retained':True,'repairs':rows}
    p=OUT/'private-helper-controls-v2-preparation.json';assert not p.exists();p.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'preparation':binding(p),'new_control_modules':[r['module'] for r in rows]}))
if __name__=='__main__':main()
