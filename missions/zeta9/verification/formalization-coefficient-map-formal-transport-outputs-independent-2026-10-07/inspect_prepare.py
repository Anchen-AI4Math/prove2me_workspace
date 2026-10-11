"""Independent Outputs input inspection and fresh SOURCE-only preparation."""
from pathlib import Path
import hashlib,json,re,sys
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parent.parent;PROJECT=TASK/'.rt/oi7'
AUTHOR=TASK/'verification/formalization-coefficient-map-formal-transport-outputs-author-2026-10-07'
PREP=TASK/'verification/formalization-coefficient-map-formal-transport-outputs-preparation-2026-10-04'
AUTHOR_SHA='4e1d50c94ec296144696b8dc7c71dea74f682e9c0a69ed8e46aa4fe5e862f315'
SOURCE_SHA='8b2fc477c10a698f9b5bef004531861c392d93da0377a2874965c8ce470d2fa6'
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def resolve(r):return TASK/r['task_relative'] if r.get('task_relative') is not None else ROOT/r['root_relative']
def check(rows):
    for r in rows:
        p=resolve(r);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
def bind(p):return dict(task_relative=p.resolve().relative_to(TASK.resolve()).as_posix(),bytes=p.stat().st_size,sha256=sha(p))
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def copy(p,d):d.parent.mkdir(parents=True,exist_ok=True);assert not d.exists();d.write_bytes(p.read_bytes())

def main():
    sys.stdout.reconfigure(encoding='utf-8');assert not PROJECT.exists(),'oi7 must be absent; never reset a prior private project'
    ap=AUTHOR/'author-audit.json';assert sha(ap)==AUTHOR_SHA
    author=load(ap);assert author['verdict']=='PASS' and len(author['stable_files'])==636
    check(author['stable_files']);assert all(c['passed'] for c in author['checks'])
    source=AUTHOR/'OutputsVerifiedSource.lean';assert sha(source)==SOURCE_SHA
    shared=TASK/'formalization/CoefficientMapFormalTransportOutputs.lean';check([author['original_shared_source']])
    sources=load(PREP/'source-inputs.json')['sources'];assert len(sources)==21
    PROJECT.mkdir(parents=True);rows=[]
    for r in sources:
        origin=source if r['module'].endswith('.CoefficientMapFormalTransportOutputs') else Path(r['origin_absolute'])
        expected=SOURCE_SHA if origin==source else r['sha256'];assert sha(origin)==expected
        target=PROJECT/r['project_relative'];copy(origin,target)
        snap=OUT/'immutable-sources'/r['project_relative'];copy(origin,snap)
        rows.append(dict(module=r['module'],project_relative=r['project_relative'],
            origin=dict(absolute_path=str(origin),bytes=origin.stat().st_size,sha256=expected),
            project_copy=bind(target),snapshot=bind(snap)))
    module_set={r['module'] for r in rows}
    for r in rows:
        for line in re.findall(r'^import\s+([^\n]+)',(PROJECT/r['project_relative']).read_text(encoding='utf-8-sig'),re.M):
            for dep in line.split():
                assert not dep.startswith(('missions.','Definitions.')) or dep in module_set,(r['module'],dep)
    # Configuration SOURCE is copied from the fixed author project, never compiled objects.
    for name in ['lakefile.lean','lean-toolchain','lake-manifest.json']:
        original=TASK/'.rt/oa1'/name;copy(original,PROJECT/name)
    # Reuse only this reviewer's generic path/receipt recorder SOURCE, explicitly disclosed.
    previous=TASK/'verification/formalization-coefficient-map-numerator-pf-platform-independent-2026-10-07'
    wrapper_source=TASK/'.rt/pfi1/lean_call.py'
    wrapper=wrapper_source.read_text(encoding='utf-8').replace('PF_INDEPENDENT_PATH_RECEIPT','OUTPUTS_INDEPENDENT_PATH_RECEIPT')
    (PROJECT/'lean_call.py').write_text(wrapper,encoding='utf-8')
    engine=(previous/'run_phase1.py').read_text(encoding='utf-8').split('def schedule(rows):')[0]
    engine=engine.replace('import inspect_author as p','import inspect_prepare as p')
    engine=engine.replace("p.PREPARATION_SHA","p.PREPARATION_SHA")
    engine=engine.replace("    assert p.sha(AUTHOR/'preparation-verification.json')==p.PREPARATION_SHA\n",'')
    engine=engine.replace("prep['stable_files']","prep['stable_files']").replace("'.rt/pfi1'","'.rt/oi7'")
    engine=engine.replace('Independent NumeratorPF platform reviewer; no payload authorship','Independent Outputs native reviewer; no Outputs source authorship')
    engine=engine.replace('PF_INDEPENDENT_PATH_RECEIPT','OUTPUTS_INDEPENDENT_PATH_RECEIPT')
    engine=engine.replace("str(ROOT.resolve()).casefold() not in exact","str(ROOT.resolve()).casefold() not in exact")
    engine+=r'''
def build(label,module,source):
    obj='b/lib/lean/'+module.replace('.','/')+'.olean'
    (PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
    run(label,['-o',obj,source],[obj])
def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser();parser.add_argument('--parent-lane2-authorized',action='store_true',required=True);parser.parse_args()
    prep=gate();configure();run('runtime',['--version'])
    remaining={r['module']:r for r in prep['native_sources']};done=set()
    while remaining:
        ready=[]
        for module,row in remaining.items():
            imports=[d for line in re.findall(r'^import\s+([^\n]+)',(PROJECT/row['project_relative']).read_text(encoding='utf-8-sig'),re.M) for d in line.split()]
            if not any(dep in remaining for dep in imports):ready.append(module)
        assert ready,'Actual source import closure contains a cycle'
        for module in ready:
            row=remaining.pop(module);build('native-'+module.rsplit('.',1)[-1],module,row['project_relative']);done.add(module)
    for row in prep['serializer_sources']:build('serializer-'+row['module'],row['module'],row['project_relative'])
    dump(OUT/'native-source-terminal.json',dict(status='FRESH_21_NATIVE_SOURCE_AND_SERIALIZER_ACTUAL0',
        actual_SOURCE_modules=21,serializers=2,all_actual_handles_terminal=True,independent_PASS_claimed=False))
if __name__=='__main__':main()
'''
    # The earlier engine uses p.sha; bind/check aliases are provided above.
    (OUT/'run_sources.py').write_text(engine,encoding='utf-8')
    serializers=[]
    for name in ['IndependentExprDagV3','IndependentExprDagValidationV3']:
        original=PREP/'controls'/(name+'.lean');copy(original,PROJECT/(name+'.lean'));copy(original,OUT/(name+'.lean'))
        serializers.append(dict(module=name,project_relative=name+'.lean',source=bind(PROJECT/(name+'.lean')),
            original_SOURCE=bind(original),snapshot=bind(OUT/(name+'.lean'))))
    stable=[bind(p) for p in PROJECT.rglob('*') if p.is_file()]+[bind(OUT/'run_sources.py'),bind(OUT/'inspect_prepare.py')]
    plan=dict(status='PURE_INDEPENDENT_OUTPUTS_SOURCE_PREPARATION',role='Independent reviewer did not author Outputs proof',
        project_initially_absent=True,cache_initially_absent=True,own_project='.rt/oi7',native_sources=rows,
        serializer_sources=serializers,stable_files=stable,source_export=bind(source),original_shared_source=bind(shared),
        author_report=bind(ap),author636bindings_personally_rehashed=True,
        generic_recorder_SOURCE_reuse=dict(original=bind(previous/'run_phase1.py'),wrapper_original=bind(wrapper_source),
            only_SOURCE_read_no_PF_files_modified=True,no_PF_objects_or_mathematical_controls_reused=True),
        author_serializer_SOURCE_reuse_disclosed=True,foreign_proof_objects_allowed=False,
        controls_planned=dict(complete_original_forall=16,whole_related_definition_type_value=18,
            whole_function_rfl=18,typed_boundaries=9,Std3_with_generated_helpers=True,actual_own_findOLean=True),
        finite_scope='finite B; five outputs; LEFT Gamma n>=1 only; no HasSum parameter17, height/J/irrationality',
        Lean_invocations_in_preparation=0,independent_PASS_claimed=False)
    dump(OUT/'source-preparation.json',plan)
    grant=dict(explicit_parent_lane2_granted=True,maximum_global_Lean_lanes=2,single_serial_Lean_j1=True,
        foreign_proof_objects_allowed=False,source_preparation_sha256=sha(OUT/'source-preparation.json'),
        direct_parent_instruction='Root explicit new lane2 grant after personally rehashing PF2417; Outputs oi7 fresh SOURCE21; PY312 require_escalated -j1',
        parent_PF_rehash_SHA='ca051590c2e63bd0d88d36cd7d12b2e6a74a5b38569fca85063e26cf0d26107c',
        no_API_Root_installation_scope_helper_check_or_mission_operations=True)
    dump(OUT/'lane2-grant.json',grant)
    print(json.dumps(dict(status=plan['status'],project='.rt/oi7',native_sources=21,serializer_sources=2,
        author_bindings=636,complete_forall=16,whole_definitions=18,boundaries=9,
        source_preparation_sha256=sha(OUT/'source-preparation.json'),Lean_invocations=0),indent=2))
if __name__=='__main__':main()
