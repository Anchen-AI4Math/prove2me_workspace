from pathlib import Path
import hashlib, json, re, sys

OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parent.parent
PROJECT=TASK/'.rt/apfi1'
BATCH=TASK/'formalization/platform/analytic-phase'
AUTHOR=TASK/'verification/formalization-analytic-phase-upper-bound-2026-10-07'
INDEP=TASK/'verification/formalization-analytic-phase-upper-bound-independent-2026-10-07'
AUTHOR_SHA='a8f8cf52008b69f7b8e7e868a3c754ebc72c89f4f6f1aa89f9ca2bfdf1ff2647'
INDEP_SHA='f487b27f1668432926ad505e4f30a67e41c1abf75ad9690cc2c84369487067cc'
PLATFORM_AUTHOR_SHA='463c525179562e32fd3fabac328477908667e296138c6a14b94af7dde7afb211'
ROOT_GATE=TASK/'verification/formalization-project-handoff-2026-10-07/root-phase-independent-complete-binding-rehash.json'
SOURCE_SHAS=['2b53b56f103bc69322c35d18e120c248cc34402fe831b7be86651f584d3bf4bd','388c2be7c6401e0b0944e5ee9601ddd4f9359f85d05319ce191e6c6a4d0f1635']

def load(path): return json.loads(path.read_text(encoding='utf-8-sig'))
def sha(path):
    with path.open('rb') as handle: return hashlib.file_digest(handle,'sha256').hexdigest()
def bind(path):
    path=path.resolve(); result=dict(bytes=path.stat().st_size,sha256=sha(path))
    try: result['task_relative']=path.relative_to(TASK.resolve()).as_posix()
    except ValueError:
        try: result['root_relative']=path.relative_to(ROOT.resolve()).as_posix()
        except ValueError: result['absolute_path']=str(path)
    return result
def resolve(row):
    return TASK/row['task_relative'] if 'task_relative' in row else ROOT/row['root_relative'] if 'root_relative' in row else Path(row['absolute_path'])
def check(rows):
    for row in rows:
        path=resolve(row); assert path.stat().st_size==row['bytes'] and sha(path)==row['sha256'],str(path)
def dump(path,value):
    path.parent.mkdir(parents=True,exist_ok=True); path.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def write(path,text):
    path.parent.mkdir(parents=True,exist_ok=True); assert not path.exists(),str(path); path.write_text(text,encoding='utf-8')
def decls(text):
    result=[]; matches=list(re.finditer(r'^(def|theorem)\s+(\w+)',text,re.M))
    for i,match in enumerate(matches):
        end=matches[i+1].start() if i+1<len(matches) else text.rfind('end ZetaNine.AnalyticPhase')
        source=text[match.start():end].rstrip()+'\n'
        result.append(dict(kind=match.group(1),name=match.group(2),header=source.split(':=',1)[0].rstrip(),source=source))
    return result

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not PROJECT.exists(),'Fresh independent apfi1 must be absent; never reset'
    assert sha(BATCH/'author-audit.json')==PLATFORM_AUTHOR_SHA
    personal=load(OUT/'personal-author-complete-binding-rehash.json')
    assert personal['personally_stream_rehashed_all'] and personal['stable_bindings']==26180 and personal['mismatches']==0
    assert personal['author_report_sha256']==PLATFORM_AUTHOR_SHA
    native=load(AUTHOR/'author-audit.json'); assert sha(AUTHOR/'author-audit.json')==AUTHOR_SHA
    assert sha(INDEP/'independent-audit.json')==INDEP_SHA
    texts=[]; contracts=[]; origins=[]
    for row,expected in zip(native['sources'],SOURCE_SHAS):
        origin=resolve(row['exported_source']); original=resolve(row['shared']); assert sha(origin)==expected
        text=origin.read_text(encoding='utf-8-sig'); actual=decls(text); initial=decls(original.read_text(encoding='utf-8-sig'))
        assert [(r['kind'],r['name'],r['header']) for r in actual]==[(r['kind'],r['name'],r['header']) for r in initial]
        for a,b in zip(actual,initial):
            if a['kind']=='def': assert a['source']==b['source']
        texts.append(text); contracts+=actual; origins.append(dict(export=bind(origin),original=bind(original)))
    defs=[r for r in contracts if r['kind']=='def']; theorems=[r for r in contracts if r['kind']=='theorem']
    assert len(defs)==7 and len(theorems)==34
    plan=load(BATCH/'target-plan.json'); assert len(plan['payloads'])==7 and len(plan['targets'])==3
    payloads=[]; staged=OUT/'staged'
    for row in plan['payloads']:
        source=BATCH/'staged'/row['path']; check([row['binding']])
        published=BATCH/'publication-preparation-2026-10-07/exact-payloads'/row['path']
        assert source.read_bytes()==published.read_bytes()
        target=staged/row['path']; target.parent.mkdir(parents=True,exist_ok=True); assert not target.exists();target.write_bytes(source.read_bytes())
        payloads.append(dict(kind=row['kind'],path=row['path'],binding=bind(target),author_source=bind(source),publication_copy=bind(published)))
    canonical=plan['local_definition']; definition=(staged/canonical).read_text(encoding='utf-8')
    assert [r['source'] for r in decls(definition)]==[r['source'] for r in defs]
    for target in plan['targets']:
        solution=(staged/target['local_solution']).read_text(encoding='utf-8')
        proofdecls=decls(solution.split('\nend ZetaNine.AnalyticPhase\n',1)[0]+'\nend ZetaNine.AnalyticPhase\n')
        assert proofdecls==theorems,'Actual complete proof closures must equal native SOURCE, not theorem mirrors'
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',solution)
        assert 'import Theorems.' not in solution and solution.count('theorem solution')==1
    core=TASK/'.rt/api1/APIPhaseExprDagV1.lean'; fixture=TASK/'.rt/api1/APIPhaseExprDagValidationV1.lean'
    coretext=core.read_text(encoding='utf-8'); assert coretext.startswith('import Lean\n')
    fixturetext=fixture.read_text(encoding='utf-8').replace('import APIPhaseExprDagV1\n','import PhasePlatformExprDagV1\n').replace('import missions.zeta9.formalization.AnalyticPhaseUpperBound\n','import Definitions.Def_ZetaNine_AnalyticPhase\n')
    assert 'missions.' not in fixturetext
    configs=[(name,TASK/'.rt/aph1'/name) for name in ['lean-toolchain','lake-manifest.json']]
    wrapper_origin=TASK/'.rt/psi1/lean_call.py'
    wrapper=wrapper_origin.read_text(encoding='utf-8').replace('PARAMETER_SUMMATION_INDEPENDENT_PATH_RECEIPT','PHASE_PLATFORM_INDEPENDENT_PATH_RECEIPT')
    oracle=[]
    for text,name in zip(texts,['AnalyticPhase','AnalyticPhaseUpperBound']):
        oracle.append(dict(module='Native.'+name,path='Native/'+name+'.lean',source=text.replace('namespace ZetaNine.AnalyticPhase','namespace PhasePlatformNativeOracle').replace('end ZetaNine.AnalyticPhase','end PhasePlatformNativeOracle').replace('import missions.zeta9.formalization.AnalyticPhase\n','import Native.AnalyticPhase\n')))
    PROJECT.mkdir(); contexts=[]
    for tag in ['native','definition','reference','right','certified','global']:
        ctx=PROJECT/tag;ctx.mkdir();rows=[]
        write(ctx/'lakefile.toml','name = "phasePlatformIndependent_'+tag+'"\nbuildDir = "b"\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "0df444a360eaa60ab8c11dca51a86af692955474"\n[[lean_lib]]\nname = "Phase"\nroots = ["Definitions.Def_ZetaNine_AnalyticPhase"]\n')
        for name,origin in configs: (ctx/name).write_bytes(origin.read_bytes())
        write(ctx/'lean_call.py',wrapper)
        def add(module,rel,text,label):
            write(ctx/rel,text);rows.append(dict(module=module,path=rel,label=label,binding=bind(ctx/rel)))
        if tag=='native':
            for text,name in zip(texts,['AnalyticPhase','AnalyticPhaseUpperBound']):
                add('missions.zeta9.formalization.'+name,'missions/zeta9/formalization/'+name+'.lean',text,'native-'+name)
        else:
            # The exact business payload is copied byte-for-byte, including UTF8/newlines.
            (ctx/canonical).parent.mkdir(parents=True,exist_ok=True);(ctx/canonical).write_bytes((staged/canonical).read_bytes())
            rows.append(dict(module=canonical[:-5].replace('/','.'),path=canonical,label='actual-definition',binding=bind(ctx/canonical)))
            if tag=='reference':
                for target in plan['targets']:
                    rel=target['local_reference'];(ctx/rel).parent.mkdir(parents=True,exist_ok=True);(ctx/rel).write_bytes((staged/rel).read_bytes())
                    rows.append(dict(module=rel[:-5].replace('/','.'),path=rel,label='reference-type-only-'+target['theorem_name'].rsplit('.',1)[-1],binding=bind(ctx/rel)))
            else:
                for row in oracle: add(row['module'],row['path'],row['source'],'own-oracle-'+row['module'].rsplit('.',1)[-1])
                if tag!='definition':
                    rel=plan['targets'][['right','certified','global'].index(tag)]['local_solution']
                    (ctx/rel).parent.mkdir(parents=True,exist_ok=True);(ctx/rel).write_bytes((staged/rel).read_bytes())
                    rows.append(dict(module=rel[:-5].replace('/','.'),path=rel,label='complete-solution',binding=bind(ctx/rel)))
                for module,text in [('PhasePlatformExprDagV1',coretext),('PhasePlatformExprDagValidationV1',fixturetext)]:add(module,module+'.lean',text,'own-'+module)
        contexts.append(dict(tag=tag,task_relative=ctx.relative_to(TASK).as_posix(),initially_absent=True,math_sources=rows))
    assert not list(PROJECT.rglob('*.olean')) and not list(PROJECT.rglob('.lake'))
    dump(OUT/'target-plan.json',plan)
    stable=[bind(path) for path in PROJECT.rglob('*') if path.is_file()]+[bind(path) for path in staged.rglob('*.lean')]
    stable += [bind(OUT/'inspect_prepare.py'),bind(OUT/'personal_author_rehash.py'),bind(OUT/'personal-author-complete-binding-rehash.json'),bind(OUT/'Root-platform-independent-lane2-grant.json'),bind(BATCH/'author-audit.json'),bind(INDEP/'independent-audit.json'),bind(ROOT_GATE)]
    dump(OUT/'source-preparation.json',dict(role='Analytic Phase platform INDEPENDENT',platform_author_report=bind(BATCH/'author-audit.json'),personal_author_full_binding_gate=bind(OUT/'personal-author-complete-binding-rehash.json'),critical_sources=origins,native_definitions=defs,native_theorems=theorems,contexts=contexts,payloads=payloads,stable_files=stable,exact_original_34_forall_headers_preserved=True,exact_original_7_definition_source_preserved=True,fresh_contexts_before_build_no_objects=True,no_foreign_mathematical_objects_borrowed=True,full_math_SOURCE_reuse_disclosed=True,namespace_oracle_SOURCE_reuse_only=True,generic_DAG_SOURCE_only_reuse=dict(core=bind(core),fixtures=bind(fixture)),generic_path_wrapper_SOURCE=bind(wrapper_origin),toolchain_manifest_SOURCE=[bind(origin) for _,origin in configs],reference_catalog_is_not_proof=True,actual_API_calls=0,independent_PASS_claimed=False))
    print(json.dumps(dict(status='FRESH_PLATFORM_INDEPENDENT_SOURCE_ONLY_READY',contexts=6,payloads=7,original_forall=34,definitions=7,objects_before_build=0,preparation_SHA=sha(OUT/'source-preparation.json')),indent=2),flush=True)

if __name__=='__main__':main()
