from pathlib import Path
import ast, re, json, sys
import inspect_prepare as p

# Copy pure generic SOURCE strings only. No former auditor/author proof objects.
origin=p.TASK/'verification/formalization-coefficient-map-parameter-summation-independent-2026-10-07/prepare_controls.py'
tree=ast.parse(origin.read_text(encoding='utf-8'))
templates={}
for node in tree.body:
    if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id in ['META','GENERATED'] for t in node.targets):
        templates[node.targets[0].id]=ast.literal_eval(node.value)
META=templates['META'].replace('import ParameterSummationIndependentAssertionsV1\n','import PhasePlatformAssertions\n').replace('import IndependentExprDagV3\n','import PhasePlatformExprDagV1\n')
GENERATED=templates['GENERATED']

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    prep=p.load(p.OUT/'source-preparation.json'); defs=prep['native_definitions']; thms=prep['native_theorems']
    contract=p.TASK/'.rt/aph1/APBoundary.lean'
    body=contract.read_text(encoding='utf-8').split('namespace APBoundary\n',1)[1].split('end APBoundary',1)[0]
    boundaries=re.findall(r'^theorem\s+(\w+)',body,re.M); assert len(boundaries)==15
    controls=[]
    for context in prep['contexts']:
        tag=context['tag']
        if tag not in ['definition','right','certified','global']:continue
        ctx=p.PROJECT/tag; isproof=tag!='definition'
        imports='import Definitions.Def_ZetaNine_AnalyticPhase\nimport Native.AnalyticPhaseUpperBound\n'
        if isproof: imports+='import '+next(r['module'] for r in context['math_sources'] if r['label']=='complete-solution')+'\n'
        assertions=imports+'set_option autoImplicit false\nset_option maxHeartbeats 8000000\nset_option maxRecDepth 20000\nnoncomputable section\nopen Set\nopen ZetaNine.AnalyticPhase\nnamespace PhasePlatformWhole\n'
        for row in defs: assertions+='theorem whole_'+row['name']+' : ZetaNine.AnalyticPhase.'+row['name']+' = PhasePlatformNativeOracle.'+row['name']+' := by rfl\n'
        assertions+='end PhasePlatformWhole\n'
        if isproof: assertions+='namespace PhasePlatformBoundary\n'+body+'end PhasePlatformBoundary\n'
        p.write(ctx/'PhasePlatformAssertions.lean',assertions)
        semantic=META+GENERATED+'run_meta do\n'
        if isproof:
            for row in thms:
                a='ZetaNine.AnalyticPhase.'+row['name']; e='PhasePlatformNativeOracle.'+row['name']
                semantic+='  full `'+a+' "actual_original_forall"\n  full `'+e+' "oracle_original_forall"\n  wholeType `'+a+' `'+e+'\n'
            target=['phase_strictAntiOn_right','phase_global_lt_certified','phase_global_upper_bound'][['right','certified','global'].index(tag)]
            semantic+='  full `solution "actual_complete_solution"\n  wholeType `solution `ZetaNine.AnalyticPhase.'+target+'\n'
        for row in defs:
            a='ZetaNine.AnalyticPhase.'+row['name']; e='PhasePlatformNativeOracle.'+row['name']
            semantic+='  full `'+a+' "actual_full_definition"\n  full `'+e+' "oracle_full_definition"\n  definitionKernel `'+a+' `'+e+'\n  full `PhasePlatformWhole.whole_'+row['name']+' "actual_whole_function_rfl"\n'
        if isproof:
            for name in boundaries:semantic+='  full `PhasePlatformBoundary.'+name+' "actual_typed_boundary"\n'
        modules=['Definitions.Def_ZetaNine_AnalyticPhase','Native.AnalyticPhase','Native.AnalyticPhaseUpperBound','PhasePlatformAssertions']
        if isproof: modules.append(next(r['module'] for r in context['math_sources'] if r['label']=='complete-solution'))
        semantic+='  completeActualModuleInventory ['+', '.join('`'+m for m in modules)+']\n'
        p.write(ctx/'PhasePlatformSemantic.lean',semantic)
        own=[r['module'] for r in context['math_sources']]+['PhasePlatformAssertions','PhasePlatformSemantic']
        resolver='import PhasePlatformSemantic\nimport PhasePlatformExprDagValidationV1\nimport Lean\nopen Lean Meta\nset_option maxHeartbeats 8000000\nrun_meta do\n  let env ← getEnv\n  for name in env.header.moduleNames do\n    let file ← findOLean name\n    let real ← IO.FS.realPath file\n    IO.println (Json.mkObj [("kind",Json.str "actual_import_origin"),("module",Json.str name.toString),("chosen",Json.str file.toString),("realPath",Json.str real.toString)]).compress\n'
        for module in own:
            expected=str((ctx/'b/lib/lean'/(module.replace('.','/')+'.olean')).resolve())
            resolver+='  let file ← findOLean `'+module+'\n  let real ← IO.FS.realPath file\n  let expected ← IO.FS.realPath (System.FilePath.mk '+json.dumps(expected)+')\n  unless real == expected do throwError "Own actual independent proof object mismatch: '+module+'"\n  IO.println (Json.mkObj [("kind",Json.str "actual_own_object_resolution"),("module",Json.str "'+module+'"),("realPath",Json.str real.toString),("expected",Json.str expected.toString),("own_exact",toJson true)]).compress\n'
        p.write(ctx/'PhasePlatformResolver.lean',resolver)
        rows=[dict(label='control-'+name,module='PhasePlatform'+name.title(),path='PhasePlatform'+name.title()+'.lean',binding=p.bind(ctx/('PhasePlatform'+name.title()+'.lean'))) for name in ['assertions','semantic','resolver']]
        controls.append(dict(tag=tag,proof_context=isproof,rows=rows,own_mathematical_modules=modules,own_resolver_expected=own,exact_forall_count=34 if isproof else 0,whole_definition_count=7,whole_function_rfl=7,typed_boundaries=15 if isproof else 0))
    p.dump(p.OUT/'control-preparation.json',dict(contexts=controls,boundary_names=boundaries,native_boundary_SOURCE_reuse=dict(binding=p.bind(contract),only_verified_SOURCE_body_copied=True,namespace_changed_to='PhasePlatformBoundary',native_Meta_code_not_reused=True,no_foreign_objects=True),generic_Meta_recorder_SOURCE_reuse=p.bind(origin),templates_obtained_by_literal_AST_no_import_execution=True,original_headers34_preserved=True,raw_namespace_alias_differences_must_be_retained=True,source_bindings=[p.bind(p.OUT/'prepare_controls.py')]+[r['binding'] for c in controls for r in c['rows']],independent_PASS_claimed=False))
    print('Independent own-context controls prepared: 4x7 whole types/values/rfl; 3x34 fullforalls+wrapper/15 typedbounds; full helper values/inferType/Std3/actual import origins.',flush=True)

if __name__=='__main__':main()
