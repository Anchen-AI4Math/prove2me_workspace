from pathlib import Path
import json,re
from prepare_A_independent import OUT,TASK,PROJECT,BATCH,PURE,load,bind,write,qualify

def main():
    old=OUT/'A-source-preparation.json';p=load(old);assert not (OUT/'A-source-preparation-v2.json').exists()
    assert not (OUT/'A-actual-independent-calls.json').exists(),'Augment before any actual Lean call'
    design=load(PURE/'pure-independent-review-design.json');plan=load(BATCH/'target-plan.json')
    template=(BATCH/'platform-author-native-export/src/AUPTypes_moment.lean').read_text(encoding='utf-8')
    core=template[template.index('private def afEmit'):template.index('run_cmd liftTermElabM do')].replace('AF_RECORD|','GAI_RECORD|')
    for tag in ['m','c','u']:
        target=next(r for r in plan['targets'] if r['key']=={'m':'moment','c':'changing','u':'uniform'}[tag])
        prefix='import GAIExprDag\nimport GAIRawContracts\nimport Lean\nimport Lean.Util.CollectAxioms\nset_option autoImplicit false\nset_option maxHeartbeats 16000000\nset_option maxRecDepth 200000\nopen Lean Meta Elab Command\n'
        checks='run_cmd liftTermElabM do\n'
        names=next(r for r in design['raw4_by_target_source_only'] if r['target']==target['theorem_name'])['raw_contract_names'];assert len(names)==4
        for n in names:checks+='  afRecord "raw_goal_contract" ``GAIRawContract.'+n+'\n'
        checks+='''  let env ← getEnv
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if m == `GAIRawContracts then
      let data := env.header.moduleData[i]!
      afEmit <| Json.mkObj [("kind",toJson "module_inventory"),("module",toJson m.toString),
        ("constant_names",toJson (data.constNames.map Name.toString)),("extra_names",toJson (data.extraConstNames.map Name.toString))]
      for n in data.constNames do afRecord "module_declaration" n
      for n in data.extraConstNames do
        afEmit <| Json.mkObj [("kind",toJson "compiler_extra_environment_visibility"),("module",toJson m.toString),
          ("name",toJson n.toString),("actual_env_find_some",toJson (env.find? n).isSome)]
        if (env.find? n).isSome then afRecord "module_extra" n
'''
        path=PROJECT/tag/'src/GAIRawRecords.lean';write(path,prefix+core+checks);b=bind(path)
        p['source_bindings'].append(b);p['contexts'][tag]['all_source_bindings'].append(b)
        order=p['compile_orders'][tag];order.insert(order.index('GAIResolver'),'GAIRawRecords')
    names={r['full_name'].rsplit('.',1)[-1]:r['full_name'] for r in design['all29_original_whole_definitions']}
    ref=PROJECT/'r/src/GAIReferences.lean';original=ref.read_text(encoding='utf-8');write(OUT/'A-original-reference-catalog-source.lean',original)
    new=original[:original.index('run_cmd liftTermElabM do')]
    new+='set_option maxHeartbeats 16000000\nnoncomputable section\nopen scoped BigOperators Topology\nopen Set Finset Filter Polynomial\n'
    for target in plan['targets']:
        h=target['original_prefix'];name=target['theorem_name'].rsplit('.',1)[-1];assert h.startswith('theorem '+name) and h.endswith(':=')
        new+='theorem reference_'+target['key']+qualify(h[len('theorem '+name):-2],names)+' := by\n  apply '+target['theorem_name']+'\n  all_goals assumption\n\n'
    new+='run_cmd liftTermElabM do\n'
    for target in plan['targets']:
        name=target['theorem_name'];alias='reference_'+target['key']
        new+='''  let ci ← getConstInfo ``'''+name+'''
  let expected ← getConstInfo ``'''+alias+'''
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type expected.type)
  let (a,b) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  let rawEqual := Expr.equal ci.type expected.type
  let defEqual ← isDefEq ci.type expected.type
  unless Expr.equal ci.type a && Expr.equal expected.type b && defEqual do throwError "Reference full type mismatch"
  liftM <| IO.println ("GAI_RECORD|" ++ (Json.mkObj [("kind",toJson "reference_type_catalog_only"),("name",toJson "'''+name+'''"),
    ("type_raw",toJson (reprStr ci.type)),("expected_type_raw",toJson (reprStr expected.type)),("type_Expr_equal",toJson rawEqual),
    ("type_isDefEq",toJson defEqual),("complete_type_roundtrip",toJson true),("catalog_value_not_mathematical_proof",toJson true)]).compress)
'''
    ref.write_text(new,encoding='utf-8');p['source_bindings']=[bind(ref) if b.get('task_relative')==ref.relative_to(TASK).as_posix() else b for b in p['source_bindings']]
    p['contexts']['r']['all_source_bindings']=[bind(ref) if b.get('task_relative')==ref.relative_to(TASK).as_posix() else b for b in p['contexts']['r']['all_source_bindings']]
    p['control_augmentation']=dict(original_frozen_preparation=bind(old),raw4_complete_value_inferType_DAG_Std3_inventory_each_target=True,reference3_complete_original_expected_types_regenerated=True,original_reference_SOURCE_retained=bind(OUT/'A-original-reference-catalog-source.lean'),Lean_calls=0,augment_script=bind(Path(__file__)))
    write(OUT/'A-source-preparation-v2.json',p)
    print(json.dumps(dict(status='SOURCE_CONTROLS_COMPLETE_READY',raw4_each_context=3,reference_type_comparisons=3,SOURCE_bindings=len(p['source_bindings']))))
if __name__=='__main__':main()
