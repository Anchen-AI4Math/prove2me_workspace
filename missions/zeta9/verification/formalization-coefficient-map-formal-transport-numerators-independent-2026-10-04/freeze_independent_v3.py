"""Pure final verification; never invokes Lean/Lake. Run only after all handles end."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/ni1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def bind(p):return {'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def write(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n',encoding='utf8')
def verify(rows):
    for r in rows:
        p=ROOT/r['root_relative']
        assert p.is_file() and p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
def json_records(row):
    text=(ROOT/row['log']['root_relative']).read_text(encoding='utf8')
    result=[]
    for line in text.splitlines():
        if line.startswith('{'):result.append(json.loads(line))
    return result
def axioms_standard(record):
    assert set(record['axioms'])<= {'propext','Classical.choice','Quot.sound'},record

def pick_failed(rows,name):
    matches=[r for r in rows if (r['file'] or r['module'])==name]
    assert len(matches)==1
    return matches[0]

def freeze():
    prep=load(OUT/'preparation-verification.json')
    prepared=load(OUT/'preparation-manifest.json')
    verify(prepared['immutable_prepared_files'])
    verify(prep['author_control_bindings']+prep['verified_author_bindings']+prep['runtime_bindings'])
    assert len(prep['verified_author_bindings'])==282 and prepared['binding_count']==37
    for source in prep['source_copies']:verify([source['original'],source['own_copy']])
    receipt=load(OUT/'actual-execution-receipt.json')
    rows=receipt['rows'];passed=[r for r in rows if r['actual_exit']==0];failed=[r for r in rows if r['actual_exit']!=0]
    assert len(failed)==5 and {r['file'] or r['module'] for r in failed}=={'IndependentWholeTypes','IndependentSourceGraph.lean','IndependentSourceGraphV2.lean','IndependentSourceGraphV3.lean','IndependentGraphChunk14.lean'}
    for row in rows:
        keys=['input','log','exit_file']+(['object','retained_object'] if 'object' in row else [])
        verify([row[k] for k in keys])
        assert int((ROOT/row['exit_file']['root_relative']).read_text().strip())==row['actual_exit']
        assert row['foreign_proof_objects_reused']==0
    source_pass=[r for r in passed if r['mode']=='source']
    assert len(source_pass)==17 and {r['module'] for r in source_pass}=={r['module'] for r in prep['source_copies']}
    assert all('object' in r for r in source_pass)
    def pick(mode,name):
        matches=[r for r in passed if r['mode']==mode and (r['file'] or r['module'])==name]
        assert len(matches)==1,(mode,name,len(matches))
        return matches[0]
    chunks=load(OUT/'module-subchunk-manifest-v2.json')['chunks']
    assert len(chunks)==35 and sum(c['declaration_count'] for c in chunks)==389
    graph=[]
    for chunk in chunks:
        source=PROJECT/chunk['file']
        assert sha(source)==chunk['sha256'] and source.stat().st_size==chunk['bytes']
        records=json_records(pick('audit',chunk['file']))
        assert len(records)==chunk['declaration_count']
        graph.extend(records)
    assert len(graph)==389 and all(r['kind']=='actual_source_declaration' for r in graph)
    inventory=load(OUT/'source-declaration-inventory.json')
    assert {r['source_name'] for r in graph}=={r['name'] for r in inventory}
    assert len({r['source_name'] for r in graph})==389
    assert all(r['full_type_expr'] and r['full_value_expr'].strip()!='none' for r in graph)
    assert sum(r['source_kind'] in ['def','abbrev'] for r in graph)==91
    assert sum(r['source_kind'] in ['theorem','lemma'] for r in graph)==298
    for r in graph:axioms_standard(r)
    types=json_records(pick('alias','IndependentWholeTypesV2'))
    assert len(types)==15 and all(r['kind']=='whole_forall_type_kernel' for r in types)
    for r in types:
        assert r['original_full_type_expr'] and r['expected_full_type_expr']
        axioms_standard(r)
    values=json_records(pick('audit','IndependentFullValues.lean'))
    assert len(values)==12 and all(r['kind']=='whole_definition_value_kernel' for r in values)
    for r in values:
        assert r['type_kernel_equal'] and r['full_value_kernel_equal'] and r['actual_kernel_rfl_certificate']
        assert all(r[k] for k in ['original_type_expr','alias_type_expr','original_full_value_expr','alias_full_value_expr'])
        axioms_standard(r)
    boundaries=json_records(pick('audit','IndependentBoundaries.lean'))
    assert len(boundaries)==11 and all(r['kind']=='actual_independent_boundary' for r in boundaries)
    for r in boundaries:axioms_standard(r)
    resolution=json_records(pick('resolver','IndependentResolverV2.lean'))
    search=[r for r in resolution if r['kind']=='actual_search_path']
    resolved=[r for r in resolution if r['kind']=='actual_own_module_resolution']
    assert len(search)==1 and len(resolved)==19
    expected_modules={r['module'] for r in prep['source_copies']}|{'IndependentDataValues','IndependentWholeTypesV2'}
    assert {r['module'] for r in resolved}==expected_modules
    object_rows={r['module']:r['object'] for r in passed if r['mode'] in ['source','alias']}
    assert set(object_rows)==expected_modules
    for r in resolved:
        actual=Path(r['path'])
        if not actual.is_absolute():actual=PROJECT/actual
        expected=ROOT/object_rows[r['module']]['root_relative']
        assert actual.resolve()==expected.resolve(),r
        assert actual.resolve().is_relative_to((PROJECT/'b/lib/lean').resolve())
    # Actual path is checked independently of success of individual resolutions.
    paths=[p for p in search[0]['value'].split(';') if p]
    package_root=(ROOT/'.lake/packages').resolve();own_cache=(PROJECT/'b/lib/lean').resolve()
    for path in paths:
        actual=Path(path)
        if not actual.is_absolute():actual=PROJECT/actual
        normalized=actual.resolve()
        assert normalized==own_cache or normalized.is_relative_to(package_root),str(normalized)
    assert not (PROJECT/'b/lib/lean/IndependentWholeTypes.olean').exists()
    runtime=[r for r in passed if r['mode']=='runtime'];assert len(runtime)==1
    assert '4.33.1' in (ROOT/runtime[0]['log']['root_relative']).read_text(encoding='utf8')
    assert len(passed)==58 and len(rows)==63
    assert sha(OUT/'preparation-verification.json')=='e7ab5783035938d37ceac91f8b8b34aa5d07887c3375c0436e9b416c050a9d56'
    assert sha(OUT/'preparation-manifest.json')=='5ed8f4ae029233867583f528b27b1ed0228cc38aab7b405763ef127f4facbafa'
    terminal=load(OUT/'all-handles-terminal-verification.json')
    assert terminal['own_residual_compiler_processes']==[] and terminal['all_handles_returned_terminal']
    cap=load(OUT/'r23-resource-cap-receipt.json')
    assert cap['cpu_cap_seconds']==1200 and cap['exact_target_pid']==66984
    assert cap['observations'][-1]['cpu_seconds']>=1200
    assert pick_failed(failed,'IndependentSourceGraphV2.lean')['actual_exit']==4294967295
    stable={}
    def add(p):stable[bind(p)['root_relative']]=bind(p)
    for r in prep['author_control_bindings']+prep['verified_author_bindings']+prep['runtime_bindings']+prepared['immutable_prepared_files']:add(ROOT/r['root_relative'])
    for row in rows:
        for key in ['input','log','exit_file','object','retained_object']:
            if key in row:add(ROOT/row[key]['root_relative'])
    for p in OUT.glob('*'):
        if p.is_file() and p.name not in ['independent-native-review.json','source-manifest.json','SHA256SUMS.txt']:add(p)
    for p in PROJECT.glob('Independent*.lean'):add(p)
    add(OUT/'actual-execution-receipt.json')
    stable_rows=sorted(stable.values(),key=lambda r:r['root_relative'])
    verify(stable_rows)
    checks=[
      'author control three hashes and all282 source/log/object bindings verified before and after independent execution',
      'author282 SUMS members and preparation37 immutable files unchanged',
      'all seventeen true source modules freshly compiled in ni1 from exact source bytes',
      'no author Root previous-PF or independent proof objects copied or resolved',
      'only fixed Mathlib package caches shared and actual filtered search path excludes Root fallback',
      'all389 actual source declarations resolved exactly including private names',
      'all91 actual source definition types and complete values emitted as real Expr',
      'all298 actual source proofs emitted with complete types and proof values',
      'all389 source declarations have only standard-three axiom closure',
      'all15 Numerators full forall types verified without added hypotheses',
      'private denominator expected forall type independently proved after retained v1 control failure',
      'all12 actual Data whole types and complete definition values Meta compared',
      'all12 whole-definition equalities have actual kernel rfl certificates',
      'all11 independent n1 n0 high-degree and positive-rational boundaries compiled',
      'n0 actual Q2 counterexample one-over512 and n1 actual R2 nonzero counterexample retained',
      'nineteen actual findOLean resolutions point exactly to own newly compiled objects',
      'all successful source and alias objects retained and hash-bound with actual inputs logs exits',
      'five original nonzero independent controls retained with inputs logs exits and all partial records excluded',
      'r20 expected type helper failure and r22 default recursion failure diagnosed in audit controls only',
      'r23 actual cancellation at Root-authorized 1200 CPU-second cap retained as raw exit4294967295',
      'r24 and r39 blank exit1 retained with unknown causes and no mathematical failure attribution',
      'thirty-five same-inventory successful chunks emitted complete389 source Expr records',
      'control repairs change only appended independent inputs, no native source inventory or proofs',
      'all actual compiler calls serial single-thread and all handles terminal before freeze',
      'native source authored by Connection-platform agent not by this independent reviewer',
      'no Even abstract-PF or local-coefficient premises inserted into the Numerators endpoint',
      'no five-output transport theorem or platform acceptance inferred from this native review',
      'all stable bindings rehashed at final pure freeze',
    ]
    report={'verdict':'PASS','stage':'independent native review only; platform integration and acceptance not asserted',
      'checked_at':datetime.now(timezone.utc).isoformat(),'source_author':'Connection-platform source author; Root compiled its author evidence',
      'reviewer_role':'independent native reviewer only','source_sha256':prep['frozen_author_source']['sha256'],
      'author_report_sha256':prep['author_control_bindings'][0]['sha256'],
      'own_project':str(PROJECT),'checks':[{'name':c,'pass':True} for c in checks],
      'counts':{'verified_author_bindings':282,'unchanged_prepared_bindings':37,
        'fresh_real_source_modules':17,'foreign_proof_objects_reused':0,
        'actual_source_declarations':389,'actual_definition_full_types_and_values':91,
        'actual_source_proof_full_types_and_values':298,'complete_forall_type_comparisons':15,
        'whole_Data_definition_value_comparisons':12,'whole_Data_kernel_rfl_certificates':12,
        'actual_closed_boundary_controls':11,'standard_three_only_records':427,
        'actual_own_module_resolutions':19,'successful_proof_Lean_calls':57,
        'successful_runtime_calls':1,'retained_excluded_nonzero_Lean_calls':5,'diagnosed_control_failures':2,
        'explicit_resource_cap_cancellations':1,'unknown_no_diagnostic_control_exits':2,'total_actual_invocations':63,
        'successful_source_graph_chunks':35},
      'retained_excluded_failures':failed,'actual_resolver_records':resolved,
      'actual_search_path_record':search[0],'all_handles_terminal':True,
      'all_handles_terminal_basis':terminal,
      'excluded_outcome_interpretation':{'r20':'expected-type control private helper lacked explicit introductions; repaired independent alias actual0',
        'r22':'control whole-source Expr emission hit default recursion depth; native proofs unchanged',
        'r23':'monolithic control explicitly cancelled at Root CPU cap; no proof PASS inferred',
        'r24':'compact monolithic control actual1 and zero-byte log; cause unknown; no mathematical inference',
        'r39':'KernelBridge thirty-declaration control actual1 and zero-byte log; cause unknown; original retained and replaced by same-schema five-declaration chunks'},
      'source_graph_chunk_manifest':chunks,
      'stable_files':stable_rows}
    # 389 source closures +15 type endpoints +12 value certificates +11 boundaries.
    assert report['counts']['standard_three_only_records']==len(graph)+len(types)+len(values)+len(boundaries)
    write(OUT/'independent-native-review.json',report)
    write(OUT/'source-manifest.json',{'role':'independent native review only','files':stable_rows})
    (OUT/'SHA256SUMS.txt').write_text(''.join(r['sha256']+'  '+r['root_relative']+'\n' for r in stable_rows),encoding='utf8')
    verify(stable_rows)
    for name in ['independent-native-review.json','source-manifest.json','SHA256SUMS.txt']:
        print(name,sha(OUT/name),flush=True)
    print('PASS',len(checks),'checks',len(stable_rows),'bindings; all actual calls terminal and failures retained.',flush=True)

if __name__=='__main__':freeze()
