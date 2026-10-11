"""Independent SOURCE preparation and complete, streaming author/import verification.

No Lean, API, or credentials access. Own mathematical objects must start absent.
"""
from __future__ import annotations
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import sys
import time

sys.dont_write_bytecode = True
TASK = Path(__file__).resolve().parents[2]
ROOT = TASK.parents[1]
OUT = Path(__file__).resolve().parent
AUTHOR = TASK / 'verification/formalization-analytic-factorial-preparation-2026-10-07'
PROJECT = TASK / '.rt/aui1'
AUTHOR_SHA = 'fa1b455c1de84c664c89d169a39538e77e229a6c16961abbebe5b84951020c81'
ROOT_SHA = '7d4039a18e0bf575c1fb45ad6897471b3d95448caa77b00b46ae512060afdb09'

def load(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def stream(p):
    h = hashlib.sha256(); size = 0
    with p.open('rb') as f:
        while b := f.read(1024*1024):
            h.update(b); size += len(b)
    return size, h.hexdigest()

def binding(p):
    size, digest = stream(p)
    if p.is_relative_to(TASK): return {'task_relative':p.relative_to(TASK).as_posix(),'bytes':size,'sha256':digest}
    if p.is_relative_to(ROOT): return {'root_relative':p.relative_to(ROOT).as_posix(),'bytes':size,'sha256':digest}
    return {'absolute_path':str(p),'bytes':size,'sha256':digest}

def path_of(row):
    if 'task_relative' in row: return TASK / row['task_relative']
    if 'root_relative' in row: return ROOT / row['root_relative']
    return Path(row['absolute_path'])

def walk_bindings(obj):
    if isinstance(obj, dict):
        if 'bytes' in obj and 'sha256' in obj and any(k in obj for k in ('task_relative','root_relative','absolute_path')):
            yield obj
        else:
            for v in obj.values(): yield from walk_bindings(v)
    elif isinstance(obj,list):
        for v in obj: yield from walk_bindings(v)

def verify(row):
    p=path_of(row)
    size,digest=stream(p)
    assert size==row['bytes'] and digest==row['sha256'], (row,size,digest)
    return row

def write_new(p,data):
    assert not p.exists(), 'Frozen evidence must not be replaced: '+str(p)
    p.parent.mkdir(parents=True,exist_ok=True)
    if isinstance(data,str): p.write_text(data,encoding='utf-8')
    else: p.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

def theorem_headers(text):
    return {m.group(1):text[m.start():text.index(':=',m.end())].rstrip() for m in re.finditer(r'(?m)^theorem (\w+)\b',text)}

def defs(text):
    return {m.group(1):m.group(0).strip() for m in re.finditer(r'(?ms)^def (\w+)\b.*?(?=\n\n)',text)}

def qual(text,names):
    # Replace only unqualified own references; no binder, metadata, or body field deletion.
    for short,long in sorted(names.items(),key=lambda kv:-len(kv[0])):
        text=re.sub(r'(?<![\w.])'+re.escape(short)+r'(?![\w.])',long,text)
    return text

def main():
    started=time.monotonic()
    assert not PROJECT.exists(), 'Fresh project already exists; stop instead of reusing it.'
    report=AUTHOR/'author-complete-audit.json'
    root_report=TASK/'verification/formalization-project-handoff-2026-10-07/root-analytic-uniform-author-complete-binding-rehash.json'
    assert binding(report)['sha256']==AUTHOR_SHA
    assert binding(root_report)['sha256']==ROOT_SHA
    audit=load(report); root=load(root_report)
    assert audit['author_calls']==29 and audit['all_actual_handles_terminal']
    assert not audit['actual_own_WMI_live_processes']
    assert root['mismatches']==0 and root['import_freeze_is_post_author_not_backdated_precompile']
    calls=load(path_of(audit['all_actual_calls_frozen']))
    recorded=list(walk_bindings(calls))+list(walk_bindings(audit))+[binding(report),binding(root_report)]
    with ThreadPoolExecutor(max_workers=2) as ex:
        list(ex.map(verify,recorded))
    # Includes author own objects read only, never installed into the independent project.
    artifacts=root['current_import_artifact_bindings']
    with ThreadPoolExecutor(max_workers=2) as ex:
        list(ex.map(verify,artifacts))
    packages=(ROOT/'.lake/packages').resolve()
    reusable=[r for r in artifacts if not path_of(r).resolve().is_relative_to((AUTHOR/'.rt/afb1').resolve())]
    for row in reusable:
        p=path_of(row).resolve()
        assert p.is_relative_to(packages) or '.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/' in p.as_posix(),p
    plan=load(path_of(audit['frozen_original_layout']))
    exports={r['module']:r for r in audit['all_complete_exports']}
    originals=[]; names={}; header_rows=[]; def_rows=[]; native=[]
    for row in plan['actual_source_copy_order']:
        mod=row['module_name']; source=path_of(row['source'])
        export=path_of(exports[mod]['complete_source_export'])
        verify(row['source']); verify(exports[mod]['complete_source_export'])
        old=source.read_text(encoding='utf-8'); new=export.read_text(encoding='utf-8')
        hs=theorem_headers(old); ds=defs(old)
        assert hs==theorem_headers(new),mod
        assert ds==defs(new),mod
        ns=re.search(r'(?m)^namespace ([\w.]+)',old).group(1)
        for name in ds:
            assert name not in names,(name,mod)
            names[name]=ns+'.'+name
            def_rows.append({'module':mod,'name':ns+'.'+name,'whole_source':ds[name]})
        new_chain=mod.startswith('Analytic') and mod!='AnalyticPhaseUpperBound'
        for name,header in hs.items():
            header_rows.append({'module':mod,'name':ns+'.'+name,'complete_original_header':header,'new_chain':new_chain})
        native.append({'module':mod,'original':binding(source),'compiled_author_export':binding(export),'theorems':len(hs),'definitions':len(ds)})
        originals.append((mod,old,new))
    new_headers=[r for r in header_rows if r['new_chain']]
    assert len(new_headers)==70 and len(def_rows)==29
    assert sum(len(defs(old)) for mod,old,new in originals if mod.startswith('Analytic') and mod!='AnalyticPhaseUpperBound')==13
    # The actual series and coefficient-independent uniform quantifier domains are checked explicitly.
    final=next(r for r in new_headers if r['name'].endswith('.actual_weighted_uniform_o_one'))['complete_original_header']
    assert '∃ ε : ℕ → ℝ' in final and '∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →' in final
    assert all(x not in final for x in ('Summable','HasSum','Even','heightBound','MomentBound'))
    PROJECT.mkdir(parents=True,exist_ok=False)
    for mod,old,new in originals:
        target=PROJECT/'src'/(mod.replace('.','/')+'.lean')
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(path_of(exports[mod]['complete_source_export']).read_bytes())
    controls=PROJECT/'controls'; controls.mkdir()
    export_controls=AUTHOR/'native-author-export/controls'
    for old,new in [('AFExprDag','AUExprDag'),('AFExprDagValidation','AUExprDagValidation'),('AFTypes','AURecords'),('AFBoundary','AUBoundary'),('AFResolver','AUResolver')]:
        text=(export_controls/(old+'.lean')).read_text(encoding='utf-8')
        text=text.replace('AFExprDag','AUExprDag').replace('AFBoundary','AUBoundary').replace('AF_RECORD|','AU_RECORD|')
        if new=='AURecords':
            text=text.replace('if (env.find? n).isSome then afRecord "module_extra" n', '''afEmit <| Json.mkObj [("kind",toJson "compiler_extra_environment_visibility"),("module",toJson m.toString),
          ("name",toJson n.toString),("actual_env_find_some",toJson (env.find? n).isSome)]
        if (env.find? n).isSome then afRecord "module_extra" n''')
        (controls/(new+'.lean')).write_text(text,encoding='utf-8')
    # Rebuild expected complete types and whole definition bodies from originals,
    # independently of the author's already prepared expected declarations.
    kernel=(export_controls/'AFKernel.lean').read_text(encoding='utf-8').replace('AFExprDag','AUExprDag').replace('AFOriginalDefs','AUOriginalDefs').replace('AFExpected','AUExpected').replace('AF_RECORD|','AU_RECORD|')
    fresh_defs=[]
    for row in def_rows:
        header,body=row['whole_source'].split(':=',1)
        fresh_defs.append(header+' := '+qual(body,names))
    expected=[]
    for row in new_headers:
        h=row['complete_original_header']; first,rest=h.split(' ',2)[1:]
        # Qualify references in the entire complete statement while preserving all binders.
        expected.append('theorem '+first+' '+qual(rest,names)+' := '+row['name'])
    ds_start=kernel.index('namespace AUOriginalDefs'); ds_end=kernel.index('end AUOriginalDefs')+len('end AUOriginalDefs')
    kernel=kernel[:ds_start]+'namespace AUOriginalDefs\n\n'+'\n\n'.join(fresh_defs)+'\n\nend AUOriginalDefs'+kernel[ds_end:]
    es_start=kernel.index('namespace AUExpected'); es_end=kernel.index('end AUExpected')+len('end AUExpected')
    kernel=kernel[:es_start]+'namespace AUExpected\n\n'+'\n\n'.join(expected)+'\n\nend AUExpected'+kernel[es_end:]
    (controls/'AUKernel.lean').write_text(kernel,encoding='utf-8')
    config=(AUTHOR/'.rt/afb1')
    (PROJECT/'lean-toolchain').write_bytes((config/'lean-toolchain').read_bytes())
    (PROJECT/'lake-manifest.json').write_bytes((ROOT/'lake-manifest.json').read_bytes())
    (PROJECT/'lakefile.lean').write_text('''import Lake
open Lake DSL
package zeta9UniformAnalyticIndependent where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib UniformAnalyticIndependent where
  srcDir := "src"
  roots := #[`AnalyticWeightedBound]
''',encoding='utf-8')
    (PROJECT/'leaf.py').write_bytes((config/'leaf.py').read_bytes())
    assert not list(PROJECT.rglob('*.olean'))
    source_bindings=[binding(p) for p in sorted(PROJECT.rglob('*')) if p.is_file()]
    write_new(OUT/'personal-author-and-import-rehash.json',{
        'checked_at_utc':datetime.now(timezone.utc).isoformat(),'status':'PURE_FULL_STREAMING_HASH_AND_SOURCE_REVIEW_PASS',
        'author_report':binding(report),'root_author_pin':binding(root_report),
        'recorded_binding_occurrences':len(recorded),'recorded_bindings':recorded,
        'all_author_and_root_current_artifacts':len(artifacts),'current_artifact_bindings':artifacts,
        'reusable_package_intrinsic_artifacts':len(reusable),'reusable_artifact_bindings':reusable,
        'post_author_current_import_freeze_not_backdated':True,'mismatches':0,'Lean_calls':0,'API_calls':0,
        'elapsed_seconds':time.monotonic()-started})
    write_new(OUT/'source-preparation.json',{
        'status':'FRESH_SOURCE_ONLY_COMPLETE_INDEPENDENT_EXPECTED_CONTROLS','project':PROJECT.relative_to(TASK).as_posix(),
        'project_initially_absent':True,'foreign_own_proof_objects_copied':0,
        'original_source_gates':native,'all_original_complete_headers':header_rows,'all_whole_definitions':def_rows,
        'new_chain_complete_types':70,'all_own_definitions':29,'new_actual_definitions':13,
        'complete_domain_and_no_assumed_bounds':True,'independently_regenerated_original_expected_declarations':True,
        'generic_lossless_DAG_source_template_reuse_only':True,'compiler_extras_explicit_env_find_records':True,
        'source_bindings':source_bindings,'Lean_calls':0,'API_calls':0})
    print(json.dumps({'fresh_project':str(PROJECT),'recorded_bindings':len(recorded),'all_artifacts':len(artifacts),'reusable_artifacts':len(reusable),'headers':len(header_rows),'new_types':70,'whole_defs':29,'copied_own_objects':0,'elapsed_seconds':time.monotonic()-started}))

if __name__=='__main__': main()
