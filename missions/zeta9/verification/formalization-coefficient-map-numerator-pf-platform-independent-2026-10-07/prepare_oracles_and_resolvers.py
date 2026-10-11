"""Exact payload parser oracles, contextual graphs, reference types and actual path controls."""
import json, re, sys
import inspect_author as p
import semantic_spec_v2 as s
from prepare_staged_controls_v2 import strict_helpers

RESOLVER='''import @IMPORT@
import Lean
open Lean Meta
run_meta do
  let env ← getEnv
  let expected : List (Name × String × Bool) := [@EXPECTED@]
  for (module, path, shouldBeImported) in expected do
    let actual ← findOLean module
    let actualReal ← realPathNormalized actual
    let expectedReal ← realPathNormalized (System.FilePath.mk path)
    unless actualReal == expectedReal do throwError "Actual findOLean did not use independently compiled SOURCE: {module}"
    let imported := env.header.moduleNames.contains module
    unless imported == shouldBeImported do throwError "Actual module-header membership differs: {module}"
    IO.println (Json.mkObj [("kind",Json.str "independent_actual_findOLean"),
      ("context",Json.str "@CONTEXT@"),("module",Json.str module.toString),
      ("actual_path",Json.str actual.toString),("actual_real_path",Json.str actualReal.toString),
      ("expected_real_path",Json.str expectedReal.toString),("path_equal",toJson true),
      ("module_header_imported",toJson imported),("expected_header_imported",toJson shouldBeImported)]).compress
  IO.println (Json.mkObj [("kind",Json.str "independent_full_actual_module_header"),
    ("context",Json.str "@CONTEXT@"),("modules",toJson (env.header.moduleNames.toList.map Name.toString))]).compress
'''

def save(module,text):
    path=p.PROJECT/(module+'.lean'); assert not path.exists(); path.write_text(text,encoding='utf-8')
    snapshot=p.OUT/path.name; snapshot.write_bytes(path.read_bytes())
    return dict(module=module,project_relative=path.name,source=p.bind(path),snapshot=p.bind(snapshot))

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    prep=p.load(p.OUT/'source-preparation.json'); captures=p.load(p.OUT/'own-lossless-selected-Expr.json')
    native_modules=[r['module'] for r in prep['native_sources']]
    parents=[r['module'] for r in prep['parent_definition_sources']]
    payloads=[r['module'] for r in prep['seven_payloads']]
    all_modules=list(dict.fromkeys(native_modules+parents+payloads)); assert len(all_modules)==27
    new_definition='Definitions.Def_ZetaNine_CoefficientMapNumeratorPF'
    contexts=[('native','missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions',set(native_modules))]
    contexts += [(suffix,'Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_'+suffix,
        set(parents+[new_definition,'Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_'+suffix])) for suffix in s.SUFFIXES]
    resolvers=[]
    for suffix,root,imported in contexts:
        expected=[]
        for module in all_modules:
            path=(p.PROJECT/'b/lib/lean'/ (module.replace('.','/')+'.olean')).as_posix()
            expected.append('(`'+module+', '+json.dumps(path)+', '+('true' if module in imported else 'false')+')')
        text=RESOLVER.replace('@IMPORT@',root).replace('@EXPECTED@',',\n    '.join(expected)).replace('@CONTEXT@',suffix)
        row=save('PFIndependentResolver_'+suffix+'_V1',text); row['context']=suffix; row['checks']=27
        resolvers.append(row)
    graphs=[]; graph_template=(p.PROJECT/'PFIndependentGraph.lean').read_text(encoding='utf-8')
    for suffix in s.SUFFIXES:
        root='Solutions.Sol_ZetaNine_CoefficientMapNumeratorPF_'+suffix
        modules=parents+[new_definition,root]
        text=graph_template.replace('import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions','import '+root)
        text=re.sub(r'  let participating : List Name := .*', '  let participating : List Name := ['+', '.join('`'+m for m in modules)+']',text)
        assert text.count('"native-decl-graph.jsonl"')==1
        text=text.replace('"native-decl-graph.jsonl"','"staged-decl-graph-'+suffix+'.jsonl"')
        row=save('PFIndependentGraph_'+suffix+'_V1',text); row.update(context=suffix,output='staged-decl-graph-'+suffix+'.jsonl')
        graphs.append(row)
    references=[]
    for index,suffix in enumerate(s.SUFFIXES):
        target=s.TARGETS[index]; root='Theorems.Thm_ZetaNine_CoefficientMapNumeratorPF_'+suffix
        text='import '+root+'\n'+s.OPENS+strict_helpers()+'\nrun_meta do\n'
        text+='  compareProofSnapshot `'+target+' '+captures[target]['full_type_constructor_SOURCE']+'\n'
        text+='  let .thmInfo info ← getConstInfo `'+target+' | throwError "Reference must be theorem"\n'
        text+='  requireClosed `'+target+' info.type info.value\n'
        text+='  let axioms ← Lean.collectAxioms `'+target+'\n'
        text+='  unless axioms.contains `sorryAx && axioms.toList.all (fun n => ([`propext, `Classical.choice, `Quot.sound, `sorryAx] : List Name).contains n) do\n'
        text+='    throwError "Reference stub axiom boundary differs"\n'
        text+='  IO.println (Json.mkObj [("kind",Json.str "independent_reference_stub_only"),("declaration",Json.str "'+target+'"),\n'
        text+='    ("full_type_raw_Expr",Json.str (reprStr info.type)),("closed",toJson true),\n'
        text+='    ("axioms",toJson (axioms.toList.map Name.toString)),("excluded_from_proof_PASS",toJson true)]).compress\n'
        text+='  let env ← getEnv\n'
        text+='  unless !(env.header.moduleNames.toList.any (fun n => n.toString.startsWith "Solutions." || n.toString.startsWith "missions.zeta9.formalization.")) do\n'
        text+='    throwError "Reference environment loaded native/solution proof module"\n'
        row=save('PFIndependentReference_'+suffix+'_V1',text); row.update(context=suffix,target=target)
        references.append(row)
    plan=dict(status='PURE_ORACLE_REFERENCE_AND_RESOLVER_PREPARATION',
        parser_payloads=prep['seven_payloads'],graphs=graphs,resolvers=resolvers,references=references,
        actual_findOLean_checks=108,reference_stubs_never_imported_by_solution_controls=True,
        graph_template=p.bind(p.PROJECT/'PFIndependentGraph.lean'),captures=p.bind(p.OUT/'own-lossless-selected-Expr.json'),
        no_Lean_in_preparation=True,independent_PASS_claimed=False)
    (p.OUT/'oracle-resolver-preparation.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Prepared own Stage2 all7, isolated Stage1 three contexts,108 actual resolver/header checks and3 type-only stub controls.')

if __name__=='__main__':main()
