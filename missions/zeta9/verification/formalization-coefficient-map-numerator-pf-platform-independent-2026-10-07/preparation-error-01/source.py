"""Prepare an absent independent SOURCE project. No Lean/Lake invocation."""
from pathlib import Path
import json, re, sys
import inspect_author as p

OUT, TASK, ROOT, PROJECT, AUTHOR = p.OUT, p.TASK, p.ROOT, p.PROJECT, p.AUTHOR

def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data if isinstance(data, bytes) else data.encode('utf-8'))

def dump(path, data):
    write(path, json.dumps(data,ensure_ascii=False,indent=2)+'\n')

WRAPPER = r'''from pathlib import Path
import json, os, subprocess, sys
PROJECT=Path(__file__).resolve().parent
ROOT=Path(r'D:\users\self_projects\prove2me_workspace')
env=dict(os.environ); selected={'actual_execution_CWD':str(PROJECT)}
names=[x['name'] for x in json.loads((PROJECT/'lake-manifest.json').read_text(encoding='utf-8'))['packages']]
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    own=PROJECT/'b/lib/lean' if key=='LEAN_PATH' else PROJECT
    packages=[ROOT/'.lake/packages'/n/('.lake/build/lib/lean' if key=='LEAN_PATH' else '') for n in names]
    exact=[own.resolve()]+[x.resolve() for x in packages if x.is_dir()]
    allowed={str(x).casefold() for x in exact}
    original=[x for x in env.get(key,'').split(os.pathsep) if x]
    filtered=[]
    for raw in original:
        candidate=Path(raw)
        resolved=(candidate if candidate.is_absolute() else PROJECT/candidate).resolve()
        if str(resolved).casefold() in allowed and str(resolved) not in filtered:
            filtered.append(str(resolved))
    own_text=str(own.resolve())
    if own_text not in filtered: filtered.insert(0,own_text)
    env[key]=os.pathsep.join(filtered)
    selected[key]=dict(original=original,filtered=filtered,allowed_exact_set=[str(x) for x in exact])
Path(env['PF_INDEPENDENT_PATH_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\n',encoding='utf-8')
result=subprocess.run(sys.argv[1:],env=env)
sys.exit(result.returncode)
'''

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not PROJECT.exists()
    inspected=p.load(OUT/'author-input-inspection.json')
    assert inspected['mismatches']==0 and inspected['independent_project_initially_absent']
    state=p.load(AUTHOR/'preparation-state.json')
    native=[]
    for row in state['native_sources']:
        original=ROOT/row['root_relative']; p.check([row])
        target=PROJECT/row['project_relative']
        snapshot=OUT/'immutable-native-sources'/row['project_relative']
        write(target,original.read_bytes()); write(snapshot,original.read_bytes())
        native.append(dict(module=row['module'],project_relative=row['project_relative'],
            source=row,project_copy=p.bind(target),snapshot=p.bind(snapshot),
            actual_import_lines=re.findall(r'^import\s+([^\n]+)',target.read_text(encoding='utf-8-sig'),re.M)))
    parents=[]
    for row in state['parent_definitions']:
        source=ROOT/row['root_relative']; p.check([row])
        relative=row['root_relative']; target=PROJECT/relative
        if target.exists(): assert target.read_bytes()==source.read_bytes()
        else: write(target,source.read_bytes())
        snapshot=OUT/'immutable-parent-definitions'/relative
        write(snapshot,source.read_bytes())
        parents.append(dict(module=relative.removesuffix('.lean').replace('/','.'),
            project_relative=relative,source=row,project_copy=p.bind(target),snapshot=p.bind(snapshot)))
    payloads=[]
    for row in p.load(AUTHOR/'author-audit.json')['seven_payloads']:
        original=TASK/row['task_relative']
        relative=original.relative_to(AUTHOR/'staged').as_posix()
        target=PROJECT/relative; snapshot=OUT/'immutable-seven-payloads'/relative
        write(target,original.read_bytes()); write(snapshot,original.read_bytes())
        payloads.append(dict(module=relative.removesuffix('.lean').replace('/','.'),
            project_relative=relative,author_binding=row,project_copy=p.bind(target),snapshot=p.bind(snapshot)))
    for name in ['lean-toolchain','lake-manifest.json']:
        write(PROJECT/name,(ROOT/name).read_bytes())
    write(PROJECT/'lakefile.lean','import Lake\nopen Lake DSL\npackage zeta9PFIndependentPlatform where\n  buildDir := "b"\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'+state['pinned_mathlib_rev']+'"\n')
    write(PROJECT/'lean_call.py',WRAPPER)
    graph_original=ROOT/'scripts/extract_decl_graph.lean'
    graph=graph_original.read_text(encoding='utf-8-sig')
    assert 'import SumSquares' in graph and 'let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m' in graph
    graph=graph.replace('import SumSquares','import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions')
    graph=graph.replace('  let projPrefix := `SumSquares\n  let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m',
        '  let participating : List Name := ['+', '.join('`'+r['module'] for r in native)+']\n  let isProj : Name → Bool := fun m => participating.contains m')
    graph=graph.replace('"decl_graph.jsonl"','"native-decl-graph.jsonl"')
    write(PROJECT/'PFIndependentGraph.lean',graph)
    parser=ROOT/'scripts/extract_sketch_info.lean'
    write(PROJECT/'PFIndependentParser.lean',parser.read_bytes())
    assert not (PROJECT/'b').exists() and not (PROJECT/'.lake').exists()
    assert not list(PROJECT.rglob('*.olean'))
    stable=[p.bind(x) for x in sorted(PROJECT.rglob('*')) if x.is_file()]
    stable += [p.bind(x) for folder in ['immutable-native-sources','immutable-parent-definitions','immutable-seven-payloads']
               for x in sorted((OUT/folder).rglob('*')) if x.is_file()]
    data=dict(status='PURE_SOURCE_PROJECT_PREPARED',Lean_Lake_invocations=0,
        role='Independent PF platform reviewer, no PF payload authorship',
        project_task_relative='.rt/pfi1',project_initially_absent=True,cache_initially_absent=True,
        native_sources=native,parent_definition_sources=parents,seven_payloads=payloads,
        native_compiler_calls_planned=16,parent_pure_source_calls_planned=4,
        shared_HarmonicStability_source_compiled_once_in_native_closure=True,
        original_seven_payload_bytes_modified=False,foreign_proof_objects_allowed=False,
        graph_template=dict(root_relative=graph_original.relative_to(ROOT).as_posix(),sha256=p.sha(graph_original)),
        parser_template=dict(root_relative=parser.relative_to(ROOT).as_posix(),sha256=p.sha(parser)),
        stable_files=stable,independent_PASS_claimed=False)
    dump(OUT/'source-preparation.json',data)
    print('Prepared absent pfi1:16 native SOURCE +4 distinct parent SOURCE +7 exact payloads; cache absent.')

if __name__=='__main__':main()
