from __future__ import annotations
from datetime import datetime,timezone
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import json,os,subprocess,sys,time
from prepare_A_independent import OUT,TASK,ROOT,PROJECT,BATCH,PURE,ROOTPIN,load,bind,pathof,verify,write,walk

sys.dont_write_bytecode=True
CONTEXT=PROJECT/'u2'
GRANT=TASK/'verification/graph-integration-root-2026-10-08/A-uniform-focused-independent-lane2-grant.json'
SCOPE='LIMIT_SCOPE_TO_UNIFORM_ENDPOINT_AND_STANDALONE13_DEFINITION_AFTER_COMPLETE_STOCK_PREFREEZE'

def main():
    started=time.monotonic();sys.stdout.reconfigure(encoding='utf-8')
    grant=load(GRANT)
    assert grant['Root_explicit_grant'] and grant['owner']=='graph_integration_audit_1008' and grant['lane']==2
    assert grant['fresh_private_project']==CONTEXT.relative_to(TASK).as_posix()
    assert not CONTEXT.exists(),'U2 context must be genuinely absent before SOURCE initialization'
    stockpath=OUT/'A-stock-supplement-preflight.json';stock=load(stockpath)
    assert stock['status']=='TRUE_PRECOMPILE_BASELINE_FOR_FUTURE_FRESH_SOURCE_RECHECK_ONLY'
    assert stock['stock_count']==44052 and stock['mismatches']==0 and stock['Lean_calls']==0
    assert stock['supplement_binds_future_calls_not_first67'] and stock['first67_unchanged_compile_SUCCESS_but_prepost_gap_preserved']
    originalpath=OUT/'A-source-preparation-v2.json';original=load(originalpath)
    for row in original['source_bindings']:verify(row)
    for row in [original['author_report'],original['Root_pin'],original['pure_design']]:verify(row)
    design=load(pathof(original['pure_design']))
    assert len(original['all_original_complete_headers'])==122 and len(original['all29_original_whole_definitions'])==29
    author=load(pathof(original['author_report']))
    policy=load(pathof(author['own_SOURCE_input_policy']));calls=load(pathof(author['frozen_actual_calls']))
    handoff=load(pathof(author['original_SOURCE_handoff']))
    recorded=list(walk(author))+list(walk(calls))+list(walk(policy))+list(walk(handoff))+[original['author_report'],original['Root_pin'],bind(GRANT)]
    unique={os.path.normcase(str(pathof(b))):b for b in recorded}
    with ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(verify,unique.values()))
    # Stock prefreeze was completed before this initializer and every new actual call.
    # No current hash is retroactively substituted into the earlier 67-call baseline.
    src=CONTEXT/'src';src.mkdir(parents=True)
    for name in ['lakefile.lean','lake-manifest.json','lean-toolchain','leaf.py']:
        (CONTEXT/name).write_bytes((PROJECT/'u'/name).read_bytes())
    for source in sorted((PROJECT/'u/src').rglob('*.lean')):
        destination=src/source.relative_to(PROJECT/'u/src');destination.parent.mkdir(parents=True,exist_ok=True)
        destination.write_bytes(source.read_bytes())
    plan=load(BATCH/'target-plan.json');target=next(t for t in plan['targets'] if t['key']=='uniform')
    solution=src/target['local_solution'];assert solution.read_bytes()==(BATCH/'staged'/target['local_solution']).read_bytes()
    text=solution.read_text(encoding='utf-8')
    for row in design['complete_original_proof_SOURCE_contracts']:assert text.count(row['text'])==1,row['full_name']
    assert len(design['complete_original_proof_SOURCE_contracts'])==122
    for definition in (src/'Definitions').glob('*.lean'):
        assert definition.read_bytes()==(BATCH/'staged/Definitions'/definition.name).read_bytes()
    junction=CONTEXT/'.lake/packages';junction.parent.mkdir()
    result=subprocess.run(['powershell','-NoProfile','-Command',"New-Item -ItemType Junction -Path '"+str(junction)+"' -Target '"+str(ROOT/'.lake/packages')+"' | Out-Null"],capture_output=True)
    write(OUT/'A-uniform-focused-junction.json',dict(exit_code=result.returncode,stdout=result.stdout.decode(errors='replace'),stderr=result.stderr.decode(errors='replace')))
    assert result.returncode==0 and junction.is_junction() and junction.resolve()==(ROOT/'.lake/packages').resolve()
    assert not (CONTEXT/'b').exists()
    sourcebindings=[bind(p) for p in sorted(src.rglob('*.lean'))]+[bind(CONTEXT/name) for name in ['lakefile.lean','lake-manifest.json','lean-toolchain','leaf.py']]
    order=original['compile_orders']['u'];assert len(order)==11
    report=dict(created_at_utc=datetime.now(timezone.utc).isoformat(),role='independent',owner='graph_integration_audit_1008',lane=2,
        scope=SCOPE,private_project=CONTEXT.relative_to(TASK).as_posix(),project_initially_absent=True,
        Root_grant=bind(GRANT),author_report=original['author_report'],Root_pin=original['Root_pin'],pure_design=original['pure_design'],
        original_source_preparation=bind(originalpath),complete_actual_stock_prefreeze=bind(stockpath),
        stock_prefreeze_count=stock['stock_count'],stock_prefreeze_bytes=stock['stock_bytes'],
        current_author_occurrences=len(recorded),current_author_unique_bindings=list(unique.values()),current_author_mismatches=0,
        source_bindings=sourcebindings,own_math_modules=original['contexts']['u']['own_math_modules'],compile_order=order,
        all_original_complete_headers=original['all_original_complete_headers'],all29_original_whole_definitions=original['all29_original_whole_definitions'],
        complete122_original_proof_SOURCE_occurs_once_each=True,whole_new13_Def_SOURCE_byte_exact=True,
        independent_original_SOURCE_generated_controls_reused_as_SOURCE_only=True,
        all_foreign_math_objects_copied=0,actual_Lean_calls=0,API_calls=0,credential_reads=0,
        other_two_endpoint_complete_prepost_not_claimed=True,first67_math_calls_preserved_with_explicit_stock_gap=True,
        initializer=bind(Path(__file__)),elapsed_seconds=time.monotonic()-started)
    write(OUT/'A-uniform-focused-source-preparation.json',report)
    print(json.dumps(dict(status='U2_FRESH_SOURCE_READY_AFTER_COMPLETE_ACTUAL_STOCK_PREFREEZE',scope=SCOPE,source_bindings=len(sourcebindings),compile_calls=len(order),preparation=bind(OUT/'A-uniform-focused-source-preparation.json'),elapsed_seconds=time.monotonic()-started)))

if __name__=='__main__':main()
