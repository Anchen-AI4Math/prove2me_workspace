import inspect_prepare as p
from prepare_controls import save
plan=p.load(p.OUT/'control-preparation-v3.json')
text=(p.PROJECT/plan['semantic']['project_relative']).read_text(encoding='utf-8')
prefix=text.split('private def internalHelpers')[0]
assert 'run_meta do' not in prefix
prefix=prefix.replace('import OutputsIndependentAssertionsV2\n','import OutputsIndependentSemanticV3\n')
body='''private def everyOwnDeclarationAndGeneratedHelper (modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut declarations : List Name := []
  let mut generated : List Name := []
  for (name,info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[index.toNat]? | continue
    if modules.contains moduleName then
      let axioms ← standard name
      unless !(info.type.hasFVar || info.type.hasMVar) do throwError "Actual declaration has free metavariables: {name}"
      declarations := name :: declarations
      IO.println (Json.mkObj [("kind",Json.str "independent_all_actual_declaration_Std3"),
        ("declaration",Json.str name.toString),("module",Json.str moduleName.toString),
        ("axioms",toJson (axioms.toList.map Name.toString)),("closed_complete_type",toJson true)]).compress
      if name.isInternalDetail || (privateToUserName? name).isSome then
        generated := name :: generated
        if ← isProp info.type then
          helperProof name
        else
          full name "independent_all_generated_definition"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_generated_closure_inventory"),
    ("modules",toJson (modules.map Name.toString)),("all_declarations",toJson (declarations.map Name.toString)),
    ("all_generated_helpers",toJson (generated.map Name.toString)),
    ("predicate",Json.str "isInternalDetail or actual privateToUserName; covers eq_N, match_N, proof_N, omega_N, internal and numerical components")]).compress
run_meta do
'''
modules=plan['helper_modules']
body+='  everyOwnDeclarationAndGeneratedHelper ['+', '.join('`'+x for x in modules)+']\n'
row=save('OutputsIndependentGeneratedClosureV1',prefix+body)
p.dump(p.OUT/'generated-closure-preparation.json',dict(source=row,modules=modules,original_V3_semantic_predicate_preserved=True,all_native_and_assertion_declarations_Std3_required=True,complete_generated_helpers_including_public_matchers_required=True,independent_PASS_claimed=False))
print('Additional own complete module inventory and generated-closure control SOURCE prepared.')
