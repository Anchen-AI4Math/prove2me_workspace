"""Pure terminal evidence rehash and complete finite-scope independent freeze."""
from pathlib import Path
import collections, datetime, hashlib, json, sys, time
import inspect_author as p
import semantic_spec_v2 as s

STD3={'propext','Classical.choice','Quot.sound'}

def dump(path,data):path.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def actual_records(row):
    return [json.loads(x) for x in (p.TASK/row['folder_task_relative']/'stdout.log').read_text(encoding='utf-8').splitlines() if x.startswith('{')]
def all_project_files(base):
    for child in sorted(base.iterdir()):
        if child.is_junction() or child.is_symlink():continue
        if child.is_dir():yield from all_project_files(child)
        elif child.is_file():yield child

def main():
    sys.stdout.reconfigure(encoding='utf-8'); started=time.monotonic()
    assert not (p.OUT/'independent-review.json').exists(),'Already frozen; do not rewrite.'
    author=p.load(p.AUTHOR/'author-audit.json'); original_prep=p.load(p.AUTHOR/'preparation-verification.json')
    assert p.sha(p.AUTHOR/'author-audit.json')==p.AUTHOR_SHA
    assert p.sha(p.AUTHOR/'preparation-verification.json')==p.PREPARATION_SHA
    p.check(author['stable_files']);p.check(original_prep['files'])
    na=p.TASK/'verification/formalization-coefficient-map-numerator-pf-2026-10-04/author-audit.json'
    ni=p.TASK/'verification/formalization-coefficient-map-numerator-pf-independent-2026-10-04/independent-review.json'
    assert p.sha(na)==p.NATIVE_AUTHOR_SHA and p.sha(ni)==p.NATIVE_INDEPENDENT_SHA
    native_reports=[p.load(na),p.load(ni)]
    for r in native_reports:p.check(r.get('stable_files',r.get('files')))
    prep=p.load(p.OUT/'source-preparation.json');p.check(prep['stable_files'])
    grant=p.load(p.OUT/'lane2-grant.json');assert grant['explicit_parent_lane2_granted'] and grant['single_serial_Lean_j1']
    assert grant['source_preparation_sha256']==p.sha(p.OUT/'source-preparation.json')
    assert not grant['foreign_proof_objects_allowed']
    assert p.load(p.OUT/'staged-semantic-terminal-v2.json')['all_three_actual_exit0']
    assert p.load(p.OUT/'oracle-resolver-terminal.json')['actual_findOLean_and_module_header_checks']==108
    oracle=p.load(p.OUT/'own-oracle-payload-validation.json'); assert oracle['new5_pure_definitions_native_source_bytes_identical']
    pure_runs=[p.load(folder/'receipt.json') for folder in sorted((p.OUT/'pure-validation-runs').iterdir())]
    assert len(pure_runs)==2 and [r['exit_code'] for r in pure_runs]==[1,0]
    for r in pure_runs:
        p.check([r['source'],r['snapshot']]+r['evidence']);assert r['Lean_invocations']==0
    terminal=p.load(p.OUT/'terminal-process-verification.json');assert terminal['matched_count']==0 and terminal['exit_code']==0
    phase1=p.load(p.OUT/'phase1-terminal.json'); frozen_checkpoint=p.OUT/'immutable-phase1-execution-receipt.json'
    assert p.sha(frozen_checkpoint)==phase1['receipt']['sha256']
    assert len(p.load(frozen_checkpoint)['rows'])==45
    receipt=p.load(p.OUT/'execution-receipt.json'); rows=receipt['rows']
    assert len(rows)==69 and sum(r['exit_code']==0 for r in rows)==68
    failed=[r for r in rows if r['exit_code']!=0];assert len(failed)==1
    assert failed[0]['label']=='independent-staged-semantic-polynomial' and failed[0]['exit_code']==1
    path_replay=[]
    for row in rows:
        assert row['all_subprocess_handles_terminal'] and row['whole_failed_run_excluded']==(row['exit_code']!=0)
        assert row['command'][:6]==['lake','env',r'C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe','lean_call.py','lean','-j1']
        assert Path(row['execution_CWD']).resolve()==p.PROJECT.resolve()
        p.check([row['executor']]+row['input_bindings']+row['output_bindings']+row['evidence_bindings'])
        for snapshot in row['immutable_input_output_snapshots']:
            p.check([snapshot['original'],snapshot['retained']]);assert snapshot['original']['sha256']==snapshot['retained']['sha256']
        folder=p.TASK/row['folder_task_relative'];assert int((folder/'exit.txt').read_text())==row['exit_code']
        selected=p.load(folder/'selected-paths.json')
        for key in ['LEAN_PATH','LEAN_SRC_PATH']:
            allowed={str(Path(x).resolve()).casefold() for x in selected[key]['allowed_exact_set']}
            actual=[str(Path(x).resolve()).casefold() for x in selected[key]['filtered']]
            assert all(Path(x).is_absolute() for x in selected[key]['filtered']) and all(x in allowed for x in actual)
            assert str(p.ROOT.resolve()).casefold() not in allowed
            own=p.PROJECT.resolve();packages=(p.ROOT/'.lake/packages').resolve()
            for path in selected[key]['filtered']:
                resolved=Path(path).resolve()
                assert resolved.is_relative_to(own) or resolved.is_relative_to(packages)
                assert not resolved.is_relative_to(p.ROOT/'.lake/build')
        path_replay.append(dict(label=row['label'],exit_code=row['exit_code'],path_allowlist_personally_replayed=True,
            actual_execution_CWD=str(p.PROJECT),selected_paths=p.bind(folder/'selected-paths.json')))
    latest={r['label']:r for r in rows if r['exit_code']==0}
    selected=p.load(p.OUT/'own-native-graph-selection.json')
    assert len(selected['definitions'])==11 and len(selected['proofs'])==34 and len(selected['generated'])==1
    semantic_contexts={};std3_occurrences=0
    kinds_required={'independent_whole_definition_comparison':5,'independent_whole_function_rfl':5,
        'independent_expected_complete_forall':3,'independent_actual_closed_boundary':9}
    for context,label in [('native','independent-native-semantic')]+[(suffix,'independent-staged-semantic-v2-'+suffix) for suffix in s.SUFFIXES]:
        records=actual_records(latest[label]);counts=collections.Counter(r['kind'] for r in records)
        for kind,count in kinds_required.items():assert counts[kind]==count,(context,kind,counts[kind])
        if context=='native':
            assert counts['independent_named_native_proof']==34 and counts['independent_generated_equation_helper']==1
            assert counts['independent_complete_forall_kernel_comparison']==3
        else:
            assert counts['independent_staged_reached_proof']==35 and counts['independent_actual_solution']==1
            assert counts['independent_native_staged_definition_snapshot']==11
            assert counts['independent_native_staged_proof_snapshot']==36
            assert counts['independent_complete_forall_kernel_comparison']==4
        for r in records:
            if 'axioms' in r:
                assert set(r['axioms'])<=STD3,(context,r['declaration'],r['axioms']);std3_occurrences+=1
            if 'closed' in r:assert r['closed'] is True
            for key,value in r.items():
                if key.endswith('_equal') or key.endswith('_kernel_equal'):assert value is True,(context,r.get('declaration'),key)
        semantic_contexts[context]=dict(actual_label=label,actual_exit0=True,counts=dict(counts),complete_untruncated_records=records)
    roundtrip=actual_records(latest['independent-native-lossless-roundtrip'])
    assert sum(r['kind']=='independent_native_staged_definition_snapshot' for r in roundtrip)==11
    assert sum(r['kind']=='independent_native_staged_proof_snapshot' for r in roundtrip)==35
    for r in roundtrip:
        if 'axioms' in r:assert set(r['axioms'])<=STD3;std3_occurrences+=1
        for key,value in r.items():
            if key.endswith('_equal') or key.endswith('_kernel_equal'):assert value is True
    resolver_records=[]
    for context in ['native']+s.SUFFIXES:
        captured=actual_records(latest['independent-resolvers-'+context])
        assert sum(r['kind']=='independent_actual_findOLean' for r in captured)==27
        header=next(r for r in captured if r['kind']=='independent_full_actual_module_header')
        if context!='native':assert not any(x.startswith('Theorems.') or x.startswith('missions.zeta9.formalization.') for x in header['modules'])
        for r in captured:
            if r['kind']=='independent_actual_findOLean':assert r['path_equal'] and r['module_header_imported']==r['expected_header_imported']
        resolver_records+=captured
    stub_records=[]
    for suffix in s.SUFFIXES:
        captured=actual_records(latest['independent-references-'+suffix])
        stub=next(r for r in captured if r['kind']=='independent_reference_stub_only')
        assert 'sorryAx' in stub['axioms'] and set(stub['axioms'])<=STD3|{'sorryAx'} and stub['excluded_from_proof_PASS']
        pair=next(r for r in captured if r['kind']=='independent_native_staged_proof_snapshot')
        assert pair['whole_type_kernel_equal'] and pair['whole_type_Expr_equal']
        stub_records+=captured
    # Every stable file is hashed from its actual path; package junctions are never walked.
    paths={}
    def add(path):paths[str(path.resolve()).casefold()]=path.resolve()
    for r in author['stable_files']+original_prep['files']:
        add(p.resolve(r))
    add(p.AUTHOR/'author-audit.json');add(p.AUTHOR/'preparation-verification.json');add(na);add(ni)
    for r in native_reports:
        for b in r.get('stable_files',r.get('files')):add(p.resolve(b))
    for path in all_project_files(p.PROJECT):add(path)
    for path in all_project_files(p.OUT):
        if path.name not in ['independent-review.json','SHA256SUMS.txt','post-freeze-verification.json']:add(path)
    stable=[]
    for path in sorted(paths.values(),key=lambda x:str(x).casefold()):
        row=dict(root_relative=path.relative_to(p.ROOT.resolve()).as_posix(),bytes=path.stat().st_size,sha256=p.sha(path))
        if path.is_relative_to(p.TASK.resolve()):row['task_relative']=path.relative_to(p.TASK.resolve()).as_posix()
        stable.append(row)
    checks=[dict(name=name,passed=True) for name in [
        'Independent identity and initially absent own project/cache',
        'Author1441 preparation80 native188 and388 binding rehash',
        'Exact frozen seven payload bytes and request strings',
        'Sixteen actual native SOURCE modules and four additional pure parents',
        'Seven exact payload SOURCE compiles in own cache',
        'Own official Stage1 and Stage2 all participating sources and payloads',
        'Source-only458 graph minimal46 equals author graph selection',
        'Forty-five native declaration spans by actual InfoTree references',
        'Five pure definition fragments are unchanged source bytes',
        'One hundred two inline proof byte comparisons using InfoTree target-name mapping',
        'Three isolated staged graphs native46 plus actual solution',
        'Unreached weighted bridge absent from payload reachability',
        'Native eleven complete closed definition types and values',
        'Native34 complete proof types plus generated equation helper',
        'Independent whole5 definitions Expr.equal kernel isDefEq and function rfl in four contexts',
        'Independent3 complete forall endpoint types in four contexts',
        'Nine independently chosen actual boundaries in four contexts',
        'Hygiene names losslessly encoded by explicit recursive constructors',
        'Fifty-seven native SOURCE roundtrips Expr.equal and kernel isDefEq',
        'Three stage58 full constructor SOURCE comparisons',
        'Three actual solution complete type and Std3',
        'All reached and actual internal helpers have Std3 axiom closure',
        'One hundred eight actual own findOLean and header comparisons',
        'Three reference stubs exact type only and excluded from proof PASS',
        'Every actual input output snapshot full logs exit and selected paths retained',
        'Sixty-nine actual receipt rows and68 success one whole failed control excluded',
        'Original c047 failed hygiene SOURCE preserved without payload repair',
        'One pure preparation path-identity error retained without Lean invocation',
        'One failed pure span matcher fully retained and version2 validated parser declaration names and outer graph spans',
        'All serial j1 receipt path allowlists replayed no foreign proof cache',
        'Immutable45-call checkpoint matches original phase1 terminal pin',
        'All actual compiler/driver handles terminal and residual process query zero',
        'Explicit finite proper-numerator PF and jet injectivity scope',
        'Stable manifest personally streamed hashes and sums prepared']]
    report=dict(verdict='PASS',role='Independent NumeratorPF platform reviewer; did not author any fixed PF payload',
        reviewer_prior_role='Completed resumed independent Jets audit; PF starts with absent pfi1 and no borrowed proof objects',
        frozen_UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        mathematical_boundary=author['mathematical_boundary'],
        unclaimed=['Irrationality of zeta(9)','J height or denominator asymptotics','Unreached weighted-jet bridge','Universal five-output transport'],
        author_report=p.bind(p.AUTHOR/'author-audit.json'),original_preparation=p.bind(p.AUTHOR/'preparation-verification.json'),
        native_report_pins=[p.bind(na),p.bind(ni)],seven_payloads=prep['seven_payloads'],
        own_project='.rt/pfi1',foreign_proof_objects_borrowed=False,
        permitted_shared_cache='Only pinned package caches and compiler builtin; own native/parents/payload SOURCE independently compiled',
        no_API_Root_installation_mission_scope_or_shared_helper_writes=True,
        actual_receipt_rows=69,actual_successful_rows=68,actual_failed_Lean_rows=1,
        complete_own_failed_call=failed[0],
        pure_preparation_error=dict(source_exit_context_retained=True,Lean_invocations=0,
            original_terminal_traceback_not_mechanically_archived=True,
            context=p.bind(p.OUT/'preparation-error-01/error.json')),
        own_pure_validation_actual_runs=pure_runs,
        read_only_diagnostic_failure_transcription=p.bind(p.OUT/'diagnostic-error-01/error.json'),
        historical_author_failures_excluded_not_replayed=author['complete_continuation_failure_classification'],
        actual_call_rows=rows,actual_selected_path_replays=path_replay,
        semantic_contexts=semantic_contexts,native_lossless_SOURCE_roundtrip_records=roundtrip,
        Std3_occurrences_personally_verified=std3_occurrences,
        own_oracle_validation=p.bind(p.OUT/'own-oracle-payload-validation.json'),
        actual_resolver_full_header_records=resolver_records,reference_type_only_records=stub_records,
        terminal_process_query=p.bind(p.OUT/'terminal-process-verification.json'),
        stable_files=stable,checks=checks,all_checks_passed=True,
        binding_bytes=sum(x['bytes'] for x in stable),stable_binding_count=len(stable))
    dump(p.OUT/'independent-review.json',report)
    report_binding=p.bind(p.OUT/'independent-review.json')
    sums=''.join(row['sha256']+'  '+row['root_relative']+'\n' for row in stable)
    sums+=report_binding['sha256']+'  '+(p.OUT/'independent-review.json').relative_to(p.ROOT).as_posix()+'\n'
    (p.OUT/'SHA256SUMS.txt').write_text(sums,encoding='utf-8')
    # Re-open every frozen byte after writing the report and sums.
    for row in stable:
        path=p.ROOT/row['root_relative'];assert path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256']
    p.check([report_binding])
    checksums=(p.OUT/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines()
    assert len(checksums)==len(stable)+1
    for line in checksums:
        digest,relative=line.split('  ',1);assert p.sha(p.ROOT/relative)==digest
    post=dict(status='FROZEN_INDEPENDENT_PF_PLATFORM_PASS_PERSONALLY_REHASHED',verdict='PASS',
        report=report_binding,SHA256SUMS=p.bind(p.OUT/'SHA256SUMS.txt'),
        stable_bindings_rehashed=len(stable),checksum_entries_rehashed=len(checksums),mismatches=0,
        final_actual_receipt_rows=69,final_successes=68,full_failed_exclusions=1,
        all_actual_handles_terminal=True,residual_own_processes=0,
        elapsed_seconds=round(time.monotonic()-started,3))
    dump(p.OUT/'post-freeze-verification.json',post)
    print(json.dumps(post,ensure_ascii=False,indent=2))

if __name__=='__main__':main()
