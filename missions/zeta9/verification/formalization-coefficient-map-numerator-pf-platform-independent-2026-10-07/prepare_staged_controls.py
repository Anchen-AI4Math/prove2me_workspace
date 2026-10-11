"""Lossless native Expr snapshots, independently recaptured in each exact solution."""
import json, sys
import inspect_author as p
import semantic_spec_v2 as s

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    receipt=p.load(p.OUT/'execution-receipt.json')
    native=next(r for r in receipt['rows'] if r['label']=='independent-native-semantic' and r['exit_code']==0)
    log=p.TASK/native['folder_task_relative']/'stdout.log'
    records=[json.loads(line) for line in log.read_text(encoding='utf-8').splitlines() if line.startswith('{')]
    selected=p.load(p.OUT/'own-native-graph-selection.json')
    prep=p.load(p.OUT/'source-preparation.json')
    definitions={r['declaration']:r for r in records if r['kind']=='independent_full_definition'}
    proofs={r['declaration']:r for r in records if r['kind'] in ['independent_named_native_proof','independent_generated_equation_helper']}
    assert set(selected['definitions'])<=definitions.keys() and set(selected['proofs']+selected['generated'])==proofs.keys()
    rows=[]
    for index,suffix in enumerate(s.SUFFIXES):
        module='Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_'+suffix
        target=s.TARGETS[index]; mapped=target.rsplit('.',1)[0]+'.checked_'+target.rsplit('.',1)[1]
        targets=[mapped if n==target else n for n in s.TARGETS]
        source='import '+module+'\n'+s.OPENS+s.assertions(targets)+s.HELPERS+'\nrun_meta do\n'
        for name in selected['definitions']:
            r=definitions[name]
            source+='  emitDefinition `'+name+'\n'
            source+='  compareDefinitionSnapshot `'+name+' ('+r['full_type_raw_Expr']+') ('+r['full_value_raw_Expr']+')\n'
        for name in selected['proofs']+selected['generated']:
            r=proofs[name]; actual=mapped if name==target else name
            source+='  emitProof `'+actual+' "independent_staged_reached_proof"\n'
            source+='  compareProofSnapshot `'+actual+' ('+r['full_type_raw_Expr']+')\n'
        source+='  compareProofSnapshot `solution ('+proofs[target]['full_type_raw_Expr']+')\n'
        source+=s.assertion_meta(targets,index)
        modules=[r['module'] for r in prep['parent_definition_sources']]+['Definitions.Def_ZetaNine_CoefficientMapNumeratorPF',module]
        source+='  emitInternalHelpers ['+', '.join('`'+m for m in modules)+']\n'
        control='PFIndependentStaged_'+suffix+'_V1'
        path=p.PROJECT/(control+'.lean'); assert not path.exists(); path.write_text(source,encoding='utf-8')
        snapshot=p.OUT/(control+'.lean'); snapshot.write_bytes(path.read_bytes())
        rows.append(dict(suffix=suffix,index=index,module=control,project_relative=path.name,
            exact_solution_module=module,selected_target=target,mapped_target=mapped,
            source=p.bind(path),source_snapshot=p.bind(snapshot),
            full_definition_snapshot_pairs=11,full_reached_proof_snapshot_pairs=35,
            solution_native_full_type_pairs=1,independent_complete_forall=3,
            whole_definition_Expr_equal_isDefEq_pairs=5,whole_function_rfl=5,closed_boundaries=9,
            actual_internal_helper_modules=modules))
    plan=dict(status='PURE_LOSSLESS_STAGED_CONTROLS_FROM_OWN_SUCCESSFUL_NATIVE_CAPTURE',
        no_Lean_in_generation=True,native_actual_stdout=p.bind(log),native_actual_exit=0,
        semantic_spec=p.bind(p.OUT/'semantic_spec_v2.py'),selection=p.bind(p.OUT/'own-native-graph-selection.json'),
        controls=rows,independent_PASS_claimed=False)
    (p.OUT/'staged-control-preparation.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Prepared three isolated staged contexts from our own complete native Expr captures; no truncation.')

if __name__=='__main__':main()
