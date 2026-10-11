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


def nat(x):assert type(x) is int and x>=0
def name(x):
    assert isinstance(x,list)
    if x[0]=='anonymous':assert len(x)==1
    elif x[0]=='str':assert len(x)==3 and isinstance(x[2],str);name(x[1])
    elif x[0]=='num':assert len(x)==3;name(x[1]);nat(x[2])
    else:raise AssertionError(('Name',x[0]))
def level(x):
    assert isinstance(x,list)
    if x[0]=='zero':assert len(x)==1
    elif x[0]=='succ':assert len(x)==2;level(x[1])
    elif x[0] in ['max','imax']:assert len(x)==3;level(x[1]);level(x[2])
    elif x[0] in ['param','mvar']:assert len(x)==2;name(x[1])
    else:raise AssertionError(('Level',x[0]))
def substring(x):assert len(x)==3 and isinstance(x[0],str);nat(x[1]);nat(x[2])
def sourceinfo(x):
    if x[0]=='none':assert len(x)==1
    elif x[0]=='original':assert len(x)==5;substring(x[1]);nat(x[2]);substring(x[3]);nat(x[4])
    elif x[0]=='synthetic':assert len(x)==4 and type(x[3]) is bool;nat(x[1]);nat(x[2])
    else:raise AssertionError(('SourceInfo',x[0]))
def syntax(x):
    if x[0]=='missing':assert len(x)==1
    elif x[0]=='node':
        assert len(x)==4;sourceinfo(x[1]);name(x[2])
        for child in x[3]:syntax(child)
    elif x[0]=='atom':assert len(x)==3 and isinstance(x[2],str);sourceinfo(x[1])
    elif x[0]=='ident':
        assert len(x)==5;sourceinfo(x[1]);substring(x[2]);name(x[3])
        for pre in x[4]:
            if pre[0]=='namespace':assert len(pre)==2;name(pre[1])
            elif pre[0]=='decl':assert len(pre)==3 and all(isinstance(s,str) for s in pre[2]);name(pre[1])
            else:raise AssertionError(('Preresolved',pre[0]))
    else:raise AssertionError(('Syntax',x[0]))
def metadata(x):
    for entry in x:
        assert len(entry)==2;name(entry[0]);v=entry[1];assert len(v)==2
        if v[0]=='ofString':assert isinstance(v[1],str)
        elif v[0]=='ofBool':assert type(v[1]) is bool
        elif v[0]=='ofName':name(v[1])
        elif v[0]=='ofNat':nat(v[1])
        elif v[0]=='ofInt':assert type(v[1]) is int
        elif v[0]=='ofSyntax':syntax(v[1])
        else:raise AssertionError(('DataValue',v[0]))
def validate_dag(payload):
    assert payload['format']=='lean-expr-dag-v1'
    nodes=payload['nodes'];assert isinstance(nodes,list) and nodes
    children=[]
    arities={'bvar':2,'fvar':2,'mvar':2,'sort':2,'const':3,'app':3,'lam':5,'forallE':5,'letE':6,'litNat':2,'litString':2,'mdata':3,'proj':4}
    for idx,n in enumerate(nodes):
        assert isinstance(n,list) and n[0] in arities and len(n)==arities[n[0]]
        kind=n[0];refs=[]
        if kind in ['bvar','litNat']:nat(n[1])
        elif kind in ['fvar','mvar']:name(n[1])
        elif kind=='sort':level(n[1])
        elif kind=='const':
            name(n[1])
            for u in n[2]:level(u)
        elif kind=='app':refs=n[1:3]
        elif kind in ['lam','forallE']:
            name(n[1]);refs=n[2:4];assert n[4] in ['default','implicit','strictImplicit','instImplicit']
        elif kind=='letE':name(n[1]);refs=n[2:5];assert type(n[5]) is bool
        elif kind=='litString':assert isinstance(n[1],str)
        elif kind=='mdata':metadata(n[1]);refs=[n[2]]
        elif kind=='proj':name(n[1]);nat(n[2]);refs=[n[3]]
        for ref in refs:nat(ref);assert ref<idx
        children.append(refs)
    roots=[payload['type_root'],payload['value_root']]
    for root in roots:nat(root);assert root<len(nodes)
    visited=set();todo=list(roots)
    while todo:
        idx=todo.pop()
        if idx in visited:continue
        visited.add(idx);todo.extend(children[idx])
    assert len(visited)==len(nodes),'Dead/unbound DAG node'

def freeze():
    prep=load(OUT/'preparation-verification.json')
    prepared=load(OUT/'preparation-manifest.json')
    verify(prepared['immutable_prepared_files'])
    verify(prep['author_control_bindings']+prep['verified_author_bindings']+prep['runtime_bindings'])
    assert len(prep['verified_author_bindings'])==282 and prepared['binding_count']==37
    for source in prep['source_copies']:verify([source['original'],source['own_copy']])
    receipt=load(OUT/'actual-execution-receipt.json')
    rows=receipt['rows'];passed=[r for r in rows if r['actual_exit']==0];failed=[r for r in rows if r['actual_exit']!=0]
    assert len(failed)==9 and {r['file'] or r['module'] for r in failed}=={'IndependentWholeTypes','IndependentSourceGraph.lean','IndependentSourceGraphV2.lean','IndependentSourceGraphV3.lean','IndependentGraphChunk14.lean','IndependentGraphModule14Part02.lean','IndependentExprDagValidationV1.lean','IndependentExprDagValidationV2.lean','IndependentBoundaries.lean'}
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
    plan=load(OUT/'source-graph-dag-plan-v1.json')
    chunks=plan['raw_tree_successful_chunks']
    assert len(chunks)==14 and sum(c['declaration_count'] for c in chunks)==288
    raw=[]
    for chunk in chunks:
        source=PROJECT/chunk['file']
        assert sha(source)==chunk['sha256'] and source.stat().st_size==chunk['bytes']
        records=json_records(pick('audit',chunk['file']))
        assert len(records)==chunk['declaration_count']
        raw.extend(records)
    assert len(raw)==288 and all(r['kind']=='actual_source_declaration' for r in raw)
    assert all(r['full_type_expr'] and r['full_value_expr'].strip()!='none' for r in raw)
    dag=json_records(pick('audit',plan['dag_file']))
    assert sha(PROJECT/plan['dag_file'])==plan['dag_source_sha256']
    assert len(dag)==101 and all(r['kind']=='actual_source_declaration_expr_dag_v1' for r in dag)
    assert {r['source_name'] for r in dag}=={r['name'] for r in plan['dag_remaining_source_inventory']}
    for record in dag:
        assert record['json_roundtrip_reconstructed'] and record['original_full_type_structurally_equal'] and record['original_full_value_structurally_equal']
        validate_dag(record['full_expr_dag'])
    validation=json_records(pick('audit','IndependentExprDagValidationV3.lean'))
    assert len(validation)==23 and all(r['all_fields_roundtrip'] and r['raw_repr_reconstruction_equal'] for r in validation)
    assert sum(r['kind']=='expr_dag_validation' for r in validation)==20
    small=[r for r in validation if r['kind']=='expr_dag_small_source_validation']
    assert len(small)==3
    for record in validation:validate_dag(record['payload'])
    for record in small:axioms_standard(record)
    graph=raw+dag
    assert len(graph)==389
    inventory=load(OUT/'source-declaration-inventory.json')
    assert {r['source_name'] for r in graph}=={r['name'] for r in inventory}
    assert len({r['source_name'] for r in graph})==389
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
    boundaries=json_records(pick('audit','IndependentBoundariesV2.lean'))
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
    assert len(passed)==39 and len(rows)==48
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
      'nine original nonzero independent controls retained with inputs logs exits and all partial records excluded',
      'r20 expected type helper failure and r22 default recursion failure diagnosed in audit controls only',
      'r23 actual cancellation at Root-authorized 1200 CPU-second cap retained as raw exit4294967295',
      'r24 r39 r41 blank exit1 retained with unknown causes and no mathematical failure attribution',
      'r42 r43 serializer control syntax failures retained and appended V3 actual0 validated',
      'r46 independent numeric n1 control finite-product expansion failure retained; V2 unchanged11 boundary statements actual0',
      'fourteen raw-tree chunks emitted288 complete Expr source declarations',
      'versioned lossless Expr DAG emitted remaining101 full source declarations with all fields',
      'all101 DAG payloads JSON-parsed topologically reconstructed and structurally compared to original CI',
      'twenty all-constructor metadata binder and sharing fixtures plus3 real sources rebuild to identical raw repr',
      'pure final validator independently checks all DAG constructor arities fields child topology and root reachability',
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
        'actual_own_module_resolutions':19,'successful_proof_Lean_calls':38,
        'successful_runtime_calls':1,'retained_excluded_nonzero_Lean_calls':9,'diagnosed_control_failures':5,
        'explicit_resource_cap_cancellations':1,'unknown_no_diagnostic_control_exits':3,'total_actual_invocations':48,
        'successful_raw_tree_source_graph_chunks':14,'successful_DAG_graph_calls':1,
        'raw_tree_source_declarations':288,'lossless_DAG_source_declarations':101,
        'DAG_all_constructor_metadata_sharing_fixtures':20,'DAG_raw_source_reconstruction_validations':3},
      'retained_excluded_failures':failed,'actual_resolver_records':resolved,
      'actual_search_path_record':search[0],'all_handles_terminal':True,
      'all_handles_terminal_basis':terminal,
      'excluded_outcome_interpretation':{'r20':'expected-type control private helper lacked explicit introductions; repaired independent alias actual0',
        'r22':'control whole-source Expr emission hit default recursion depth; native proofs unchanged',
        'r23':'monolithic control explicitly cancelled at Root CPU cap; no proof PASS inferred',
        'r24':'compact monolithic control actual1 and zero-byte log; cause unknown; no mathematical inference',
        'r39':'KernelBridge30 raw control actual1 zero-byte log; unknown cause',
        'r41':'KernelBridge5 raw control actual1 zero-byte log; unknown cause',
        'r42':'DAG validation V1 StateM control branch typing and universe keyword errors',
        'r43':'DAG validation V2 StateM return typing errors; V3 pure Json branch fix actual0',
        'r46':'independent R1(2) numerical proof lacked range2 finite-product expansion; V2 fixes only this control script'},
      'source_graph_chunk_manifest':chunks,'source_graph_DAG_plan':plan,
      'source_graph_formats':{'raw288':'Lean complete reprStr tree strings',
        'DAG101':'lean-expr-dag-v1 full constructors fields shared child IDs and type/value roots; distinct schema, not identical bytes'},
      'DAG_reconstruction_evidence':{'actual_Lean_all101_full_type_and_value_structural_comparisons':True,
        'actual_Lean20_constructor_metadata_sharing_fixtures':True,'actual_Lean3_small_source_raw_repr_comparisons':True,
        'pure_JSON_all_DAG_constructor_arity_topology_reachability_checks':True},
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
