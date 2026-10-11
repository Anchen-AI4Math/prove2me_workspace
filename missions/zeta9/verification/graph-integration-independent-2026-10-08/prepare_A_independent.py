from __future__ import annotations
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import hashlib,json,re,subprocess,sys,time

sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
BATCH=TASK/'formalization/platform/analytic-uniform-weighted'
PURE=TASK/'verification/formalization-analytic-uniform-weighted-platform-independent-2026-10-07'
PROJECT=TASK/'.rt/gaui1008'
GRANT=TASK/'verification/graph-integration-root-2026-10-08/A-platform-independent-lane2-grant.json'
ROOTPIN=TASK/'verification/graph-integration-root-2026-10-08/root-A-platform-author-full-binding-rehash.json'
REV='0df444a360eaa60ab8c11dca51a86af692955474'

def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def stream(p):
    with p.open('rb') as h:return p.stat().st_size,hashlib.file_digest(h,'sha256').hexdigest()
def bind(p):
    size,sha=stream(p);v=dict(bytes=size,sha256=sha)
    if p.is_relative_to(TASK):v['task_relative']=p.relative_to(TASK).as_posix()
    elif p.is_relative_to(ROOT):v['root_relative']=p.relative_to(ROOT).as_posix()
    else:v['absolute_path']=str(p)
    return v
def pathof(b):return TASK/b['task_relative'] if 'task_relative' in b else ROOT/b['root_relative'] if 'root_relative' in b else Path(b['absolute_path'])
def walk(j):
    if isinstance(j,dict):
        if {'bytes','sha256'}<=j.keys() and any(k in j for k in ['task_relative','root_relative','absolute_path']):yield j
        else:
            for v in j.values():yield from walk(v)
    elif isinstance(j,list):
        for v in j:yield from walk(v)
def verify(b):
    p=pathof(b);assert stream(p)==(b['bytes'],b['sha256']),str(p);return b
def write(p,s):
    assert not p.exists(),str(p);p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(s if isinstance(s,str) else json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def qualify(s,names):
    for short,long in sorted(names.items(),key=lambda kv:-len(kv[0])):s=re.sub(r'(?<![\w.])'+re.escape(short)+r'(?![\w.])',long,s)
    return s
def changed_template(text,imports,modules=None,definitions_only=False):
    old='import Solutions.Sol_ZetaNine_AnalyticUniformMomentBound_actualMoment_uniform_bound'
    assert old in text;text=text.replace(old,'\n'.join('import '+x for x in imports))
    text=text.replace('AUPlatformExprDag','GAIExprDag').replace('AFOriginalDefs','GAIOriginalDefs').replace('AFExpected','GAIExpected').replace('AF_RECORD|','GAI_RECORD|')
    if definitions_only:
        text=re.sub(r'(?m)^open ZetaNine\.(AnalyticFactorialBounds|AnalyticPSeriesTail|AnalyticRationalFactorial|AnalyticRationalLogBound|AnalyticRationalTail)\n','',text)
        text=re.sub(r'(?m)^  afRecord "theorem" .*\n','',text)
    if modules is not None:
        text=re.sub(r'if #\[.*?\]\.contains m then','if #['+', '.join('`'+m for m in modules)+'].contains m then',text,count=1)
    text=text.replace('if (env.find? n).isSome then afRecord "module_extra" n','''afEmit <| Json.mkObj [("kind",toJson "compiler_extra_environment_visibility"),("module",toJson m.toString),
          ("name",toJson n.toString),("actual_env_find_some",toJson (env.find? n).isSome)]
        if (env.find? n).isSome then afRecord "module_extra" n''')
    return text

def main():
    sys.stdout.reconfigure(encoding='utf-8');t=time.monotonic()
    grant=load(GRANT);assert grant['Root_explicit_grant'] and grant['owner']=='graph_integration_audit_1008' and grant['lane']==2
    assert grant['fresh_private_project']==PROJECT.relative_to(TASK).as_posix()
    assert not PROJECT.exists(),'Fresh independent project must be absent'
    authorpath=BATCH/'platform-author-complete-audit.json';author=load(authorpath)
    assert bind(authorpath)['sha256']==grant['author_report_sha256']
    assert bind(ROOTPIN)['sha256']==grant['Root_full_rehash']['sha256']
    assert author['actual_calls']==author['actual_successes']==24 and author['all_actual_handles_terminal']
    assert not author['actual_own_WMI_live_processes'] and not author['platform_independent_PASS'] and not author['uploaded']
    calls=load(pathof(author['frozen_actual_calls']));policy=load(pathof(author['own_SOURCE_input_policy']));handoff=load(pathof(author['original_SOURCE_handoff']))
    recorded=list(walk(author))+list(walk(calls))+list(walk(policy))+list(walk(handoff))+[bind(authorpath),bind(ROOTPIN),bind(GRANT)]
    unique={str(pathof(b)):b for b in recorded}
    with ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(verify,unique.values()))
    designpath=PURE/'pure-independent-review-design.json';assert bind(designpath)['sha256']=='ad043d2aa279201fc0ffb8b6def86d4a6a2d6e6577ee0dbe57347fefbf12221c'
    design=load(designpath)
    assert bind(PURE/'pure-source-handoff.json')['sha256']=='c2afcadec6672d04286a74fc93783a609126cfa7dabbbfccf955cedebe3cd966'
    for b in walk(load(PURE/'pure-source-handoff.json')):verify(b)
    for row in design['source_copy_personal_byte_hash_observations']:
        verify(row['author_export']);verify(row['source_copy']);assert pathof(row['author_export']).read_bytes()==pathof(row['source_copy']).read_bytes()
    headers=design['all_original_complete_headers'];whole=design['all29_original_whole_definitions']
    assert len(headers)==122 and len(whole)==29
    names={r['full_name'].rsplit('.',1)[-1]:r['full_name'] for r in whole};assert len(names)==29
    names.update({r['full_name'].rsplit('.',1)[-1]:r['full_name'] for r in headers})
    native=load(pathof(design['native_actual_A_independent_report']))
    packages=(ROOT/'.lake/packages').resolve()
    stock=[]
    for row in native['stable_files']:
        p=pathof(row).resolve()
        if p.is_relative_to(packages) or '.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/' in p.as_posix():stock.append(row)
    stock=list({str(pathof(r).resolve()):r for r in stock}.values());assert len(stock)>20000
    with ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(verify,stock))
    write(OUT/'A-personal-author-stock-preflight.json',dict(checked_at_utc=datetime.now(timezone.utc).isoformat(),author_report=bind(authorpath),Root_pin=bind(ROOTPIN),grant=bind(GRANT),recorded_binding_occurrences=len(recorded),unique_bindings=list(unique.values()),stock_precompile_bindings=stock,stock_count=len(stock),mismatches=0,Lean_calls=0,API_calls=0,credential_reads=0,elapsed_seconds=time.monotonic()-t))
    exports=BATCH/'platform-author-native-export/src'
    plan=load(BATCH/'target-plan.json');native_rows=design['source_copy_personal_byte_hash_observations'];native_modules=[r['module'] for r in native_rows]
    # Regenerate the entire expected declaration layer from independently pinned original SOURCE.
    defs='\n\n'.join(r['body'].split(':=',1)[0]+' := '+qualify(r['body'].split(':=',1)[1],names) for r in whole)
    expected=[]
    for row in headers:
        prefix=row['prefix'];assert prefix.endswith(':=');h=prefix[:-2].rstrip()
        name=row['full_name'].rsplit('.',1)[-1];rest=h[len('theorem '+name):]
        expected.append('theorem '+name+qualify(rest,names)+' := by\n  apply '+row['full_name']+'\n  all_goals assumption')
    kernel=(exports/'AUPKernel_moment_V2.lean').read_text(encoding='utf-8')
    kernel=kernel.replace('namespace AFOriginalDefs'+kernel.split('namespace AFOriginalDefs',1)[1].split('end AFOriginalDefs',1)[0]+'end AFOriginalDefs','namespace AFOriginalDefs\n'+defs+'\nend AFOriginalDefs')
    kernel=kernel.replace('namespace AFExpected'+kernel.split('namespace AFExpected',1)[1].split('end AFExpected',1)[0]+'end AFExpected','namespace AFExpected\n\n'+'\n\n'.join(expected)+'\n\nend AFExpected')
    types=(exports/'AUPTypes_moment.lean').read_text(encoding='utf-8')
    resolver=(exports/'AUPResolver_moment.lean').read_text(encoding='utf-8')
    boundary=(exports/'AUPBoundary_moment.lean').read_text(encoding='utf-8')
    orders={};bindings=[];contexts={}
    for tag in ['n','d','r','m','c','u']:
        context=PROJECT/tag;src=context/'src';src.mkdir(parents=True)
        (context/'lake-manifest.json').write_bytes((ROOT/'lake-manifest.json').read_bytes())
        (context/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
        manifest=load(context/'lake-manifest.json');assert next(r for r in manifest['packages'] if r['name']=='mathlib')['rev']==REV
        write(context/'lakefile.lean','''import Lake
open Lake DSL
package zeta9GraphAIndependent where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'''+REV+'''"
lean_lib GraphAIndependent where
  srcDir := "src"
  roots := #[]
''')
        write(context/'leaf.py','''from pathlib import Path
import json,os,subprocess,sys
PROJECT=Path(__file__).resolve().parent
PACKAGES=Path(r"D:\\users\\self_projects\\prove2me_workspace\\.lake\\packages").resolve()
env=dict(os.environ);selected={}
for key in ['LEAN_PATH','LEAN_SRC_PATH']:
    original=[x for x in env.get(key,'').split(os.pathsep) if x]
    allowed=[]
    for raw in original:
        p=(PROJECT/Path(raw)).resolve()
        if p.is_relative_to(PROJECT.resolve()) or p.is_relative_to(PACKAGES):allowed.append(str(p))
    own=str(PROJECT/('b/lib/lean' if key=='LEAN_PATH' else 'src'))
    if own not in allowed:allowed.insert(0,own)
    env[key]=os.pathsep.join(allowed);selected[key]=dict(original=original,filtered=allowed)
selected['actual_environment']={k:env.get(k) for k in ['LEAN_NUM_THREADS','LAKE_JOBS']}
Path(env['GAI_PATH_RECEIPT']).write_text(json.dumps(selected,indent=2)+'\\n',encoding='utf-8')
sys.exit(subprocess.run(sys.argv[1:],env=env).returncode)
''')
        junction=context/'.lake/packages';junction.parent.mkdir()
        p=subprocess.run(['powershell','-NoProfile','-Command',"New-Item -ItemType Junction -Path '"+str(junction)+"' -Target '"+str(ROOT/'.lake/packages')+"' | Out-Null"],capture_output=True)
        write(OUT/('junction-'+tag+'.json'),dict(exit_code=p.returncode,stdout=p.stdout.decode(errors='replace'),stderr=p.stderr.decode(errors='replace')))
        assert p.returncode==0 and junction.is_junction() and junction.resolve()==packages
        if tag=='n':
            for row in native_rows:
                dst=src/(row['module'].replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(pathof(row['source_copy']).read_bytes())
            modules=native_modules;imports=[native_modules[-1]];order=native_modules.copy()
        else:
            for f in sorted((BATCH/'staged/Definitions').glob('*.lean')):
                dst=src/'Definitions'/f.name;dst.parent.mkdir(exist_ok=True);dst.write_bytes(f.read_bytes())
            modules=[r['module'] for r in plan['canonical_dependencies']]+['Definitions.Def_ZetaNine_AnalyticUniformWeighted'];order=modules.copy();imports=modules.copy()
        if tag in ['m','c','u']:
            target=next(r for r in plan['targets'] if r['key']=={'m':'moment','c':'changing','u':'uniform'}[tag]);module=target['local_solution'][:-5].replace('/','.')
            source=BATCH/'staged'/target['local_solution'];dst=src/target['local_solution'];dst.parent.mkdir(exist_ok=True);dst.write_bytes(source.read_bytes())
            # Every complete original proof text occurs once in the actual Solution SOURCE.
            text=dst.read_text(encoding='utf-8')
            for row in design['complete_original_proof_SOURCE_contracts']:assert text.count(row['text'])==1,row['full_name']
            imports=[module];modules=modules+[module];order.append(module)
            raw=pathof(next(r for r in design['raw4_by_target_source_only'] if r['target']==target['theorem_name'])['binding']).read_text(encoding='utf-8')
            raw=raw.replace('AUPIndependentRawContract','GAIRawContract')
            write(src/'GAIRawContracts.lean',raw);order.append('GAIRawContracts')
        write(src/'GAIExprDag.lean',(exports/'AUPlatformExprDag.lean').read_text(encoding='utf-8'))
        order.append('GAIExprDag')
        if tag=='r':
            references=[]
            for target in plan['targets']:
                dst=src/target['local_reference'];dst.parent.mkdir(exist_ok=True);dst.write_bytes((BATCH/'staged'/target['local_reference']).read_bytes());references.append(target['local_reference'][:-5].replace('/','.'))
            order.extend(references)
            # Catalog placeholders are checked only as full types and never reused as mathematical proof values.
            ref='\n'.join('import '+m for m in references)+'''\nimport GAIExprDag
import Lean
open Lean Meta Elab Command
set_option autoImplicit false
set_option maxRecDepth 200000
run_cmd liftTermElabM do
'''
            for target in plan['targets']:
                name=target['theorem_name'];ref+='''  let ci ← getConstInfo ``'''+name+'''
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type ci.type)
  let (a,b) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  unless Expr.equal ci.type a && Expr.equal ci.type b && (← isDefEq ci.type a) do throwError "Reference full type mismatch"
  liftM <| IO.println ("GAI_RECORD|" ++ (Json.mkObj [("kind",toJson "reference_type_catalog_only"),("name",toJson "'''+name+'''"),("type_raw",toJson (reprStr ci.type)),("complete_type_roundtrip",toJson true)]).compress)
'''
            write(src/'GAIReferences.lean',ref);order.append('GAIReferences')
            imports=references
        else:
            typecode=changed_template(types,imports,modules,tag=='d')
            write(src/'GAITypes.lean',typecode);order.append('GAITypes')
            kcode=changed_template(kernel,imports,definitions_only=tag=='d')
            if tag in ['n','d']:kcode=re.sub(r'(?m)^  afCompare "selected_wrapper_compare" .*\n  afRecord "selected_wrapper_proof" .*\n?','',kcode)
            if tag=='d':
                start=kcode.index('namespace GAIExpected');end=kcode.index('end GAIExpected')+len('end GAIExpected');kcode=kcode[:start]+kcode[end:]
                kcode=re.sub(r'(?m)^  afCompare "theorem_compare" .*\n  afRecord "expected_theorem_value" .*\n?','',kcode)
            elif tag in ['c','u']:
                name=target['theorem_name'].rsplit('.',1)[-1]
                kcode=re.sub(r'(afCompare "selected_wrapper_compare" ``solution ``GAIExpected\.)\w+',r'\g<1>'+name,kcode)
            write(src/'GAIKernel.lean',kcode);order.append('GAIKernel')
            if tag!='d':
                write(src/'GAIBoundary.lean',changed_template(boundary,imports));order.append('GAIBoundary')
        write(src/'GAIResolver.lean',changed_template(resolver,imports,definitions_only=tag in ['d','r']));order.append('GAIResolver')
        if tag=='d':
            fixture=(exports/'AUPlatformExprDagValidation.lean').read_text(encoding='utf-8').replace('AUPlatformExprDag','GAIExprDag')
            write(src/'GAIFixtures.lean',fixture);order.append('GAIFixtures')
        assert not list((context/'b').rglob('*.olean'))
        context_bindings=[bind(f) for f in sorted(context.rglob('*')) if f.is_file() and '.lake' not in f.relative_to(context).parts]
        bindings.extend(context_bindings);orders[tag]=order;contexts[tag]=dict(context=context.relative_to(TASK).as_posix(),own_math_modules=modules,all_source_bindings=context_bindings)
    write(OUT/'A-source-preparation.json',dict(created_at_utc=datetime.now(timezone.utc).isoformat(),role='independent',project_initially_absent=True,private_project=PROJECT.relative_to(TASK).as_posix(),Root_grant=bind(GRANT),author_report=bind(authorpath),Root_pin=bind(ROOTPIN),pure_design=bind(designpath),personal_author_stock_preflight=bind(OUT/'A-personal-author-stock-preflight.json'),source_bindings=bindings,contexts=contexts,compile_orders=orders,all_original_complete_headers=headers,all29_original_whole_definitions=whole,regenerated_expected_types_from_all122_original_headers=True,regenerated_expected_values_from_all29_original_whole_bodies=True,independently_preserve_full_field_helper_pairing=True,foreign_mathematical_objects_copied=0,actual_Lean_calls=0,API_calls=0,credential_reads=0,initializer=bind(Path(__file__))))
    print(json.dumps(dict(status='FRESH_INDEPENDENT_SOURCE_READY',contexts=len(contexts),SOURCE_bindings=len(bindings),author_personal_bindings=len(unique),stock_precompile_bindings=len(stock),elapsed_seconds=time.monotonic()-t)),flush=True)

if __name__=='__main__':main()
