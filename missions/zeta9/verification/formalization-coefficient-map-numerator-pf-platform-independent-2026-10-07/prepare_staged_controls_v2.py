"""New SOURCE from actual lossless constructor capture; original failed V1 is retained."""
import json, sys
import inspect_author as p
import semantic_spec_v2 as s

def strict_helpers():
    before='  let same ← isDefEq actualInfo.type nativeType\n  unless same do'
    after='  let same ← isDefEq actualInfo.type nativeType\n  let raw := Expr.equal actualInfo.type nativeType\n  unless same && raw do'
    assert s.HELPERS.count(before)==1
    result=s.HELPERS.replace(before,after)
    return result.replace('("whole_type_kernel_equal",toJson same),\n    ("native_full_type_raw_Expr"',
        '("whole_type_kernel_equal",toJson same),("whole_type_Expr_equal",toJson raw),\n    ("native_full_type_raw_Expr"')

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    receipt=p.load(p.OUT/'execution-receipt.json')
    encoded_run=next(r for r in receipt['rows'] if r['label']=='independent-lossless-encoder' and r['exit_code']==0)
    log=p.TASK/encoded_run['folder_task_relative']/'stdout.log'
    encoded={r['declaration']:r for line in log.read_text(encoding='utf-8').splitlines() if line.startswith('{') for r in [json.loads(line)]}
    selected=p.load(p.OUT/'own-native-graph-selection.json'); prep=p.load(p.OUT/'source-preparation.json')
    assert set(encoded)==set(selected['reached_names'])
    original_log=p.OUT/'actual-runs/c046-a01/stdout.log'
    original={r['declaration']:r for line in original_log.read_text(encoding='utf-8').splitlines() if line.startswith('{')
        for r in [json.loads(line)] if r['kind'] in ['independent_full_definition','independent_named_native_proof','independent_generated_equation_helper']}
    for name,r in encoded.items():
        assert r['full_type_raw_Expr']==original[name]['full_type_raw_Expr']
        if name in selected['definitions']:assert r['full_value_raw_Expr']==original[name]['full_value_raw_Expr']
    captures=p.OUT/'own-lossless-selected-Expr.json'; captures.write_text(json.dumps(encoded,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    helper=strict_helpers()
    def comparisons(target=None,mapped=None):
        text=''
        for name in selected['definitions']:
            r=encoded[name]
            text+='  emitDefinition `'+name+'\n'
            text+='  compareDefinitionSnapshot `'+name+' '+r['full_type_constructor_SOURCE']+' '+r['full_value_constructor_SOURCE']+'\n'
        for name in selected['proofs']+selected['generated']:
            actual=mapped if name==target else name
            text+='  emitProof `'+actual+' "independent_'+('staged' if target else 'native')+'_reached_proof"\n'
            text+='  compareProofSnapshot `'+actual+' '+encoded[name]['full_type_constructor_SOURCE']+'\n'
        return text
    rows=[]
    native_name='PFIndependentNativeRoundtripV1'
    native_source='import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions\n'+s.OPENS+helper+'\nrun_meta do\n'+comparisons()
    native_path=p.PROJECT/(native_name+'.lean'); assert not native_path.exists(); native_path.write_text(native_source,encoding='utf-8')
    (p.OUT/native_path.name).write_bytes(native_path.read_bytes())
    native_row=dict(module=native_name,project_relative=native_path.name,source=p.bind(native_path),snapshot=p.bind(p.OUT/native_path.name))
    for index,suffix in enumerate(s.SUFFIXES):
        module='Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_'+suffix
        target=s.TARGETS[index]; mapped=target.rsplit('.',1)[0]+'.checked_'+target.rsplit('.',1)[1]
        targets=[mapped if n==target else n for n in s.TARGETS]
        source='import '+module+'\n'+s.OPENS+s.assertions(targets)+helper+'\nrun_meta do\n'+comparisons(target,mapped)
        source+='  compareProofSnapshot `solution '+encoded[target]['full_type_constructor_SOURCE']+'\n'
        source+=s.assertion_meta(targets,index)
        modules=[r['module'] for r in prep['parent_definition_sources']]+['Definitions.Def_ZetaNine_CoefficientMapNumeratorPF',module]
        source+='  emitInternalHelpers ['+', '.join('`'+m for m in modules)+']\n'
        control='PFIndependentStaged_'+suffix+'_V2'
        path=p.PROJECT/(control+'.lean'); assert not path.exists(); path.write_text(source,encoding='utf-8')
        snapshot=p.OUT/path.name; snapshot.write_bytes(path.read_bytes())
        rows.append(dict(suffix=suffix,index=index,module=control,project_relative=path.name,
            source=p.bind(path),snapshot=p.bind(snapshot),exact_solution_module=module,
            selected_target=target,mapped_target=mapped,actual_internal_helper_modules=modules))
    engine=dict(status='PURE_LOSSLESS_EXPLICIT_CONSTRUCTOR_SOURCE_PREPARED',native_roundtrip=native_row,controls=rows,
        captures=p.bind(captures),original_raw_capture=p.bind(original_log),encoder_stdout=p.bind(log),
        encoded_raw_capture_unchanged=True,original_failed_c047_V1_preserved=True,
        complete_constructor_SOURCE_roundtrips_per_context=57,
        all_roundtrips_require_Expr_equal_and_kernel_isDefEq=True,independent_PASS_claimed=False)
    (p.OUT/'staged-control-preparation-v2.json').write_text(json.dumps(engine,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Explicit constructor SOURCE preserves every raw selected Expr; native57 roundtrips precede three stage58 comparisons.')

if __name__=='__main__':main()
