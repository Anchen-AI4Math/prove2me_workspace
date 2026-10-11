"""Pure hash freeze only. No Lean/Lake invocation or compiled claims."""
from pathlib import Path
import os,json,sys
import prepare as p


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert not (p.OUT/'preparation-verification.json').exists()
    state=p.load(p.OUT/'preparation-state.json')
    p.native_gate()
    assert not (p.PROJECT/'b').exists() and not (p.PROJECT/'.lake').exists()
    assert not (p.OUT/'compile-receipt.json').exists()
    assert not (p.OUT/'Root-lane-grant.json').exists()
    probes=p.load(p.OUT/'exact-precheck.json')
    assert probes['Lean_invocations']==0 and probes['candidate_uncompiled']
    assert probes['check_count']==588 and all(r['passed'] for r in probes['checks'])
    active={p.PROJECT/r['project_relative'] for r in state['source']+state['controls']}
    paths=[path for path in p.OUT.rglob('*') if path.is_file() and '__pycache__' not in path.parts
        and path.name not in ['preparation-verification.json','SHA256SUMS.txt']]
    paths.extend([p.CANDIDATE,p.TASK/'research/coefficient-map-formal-transport-outputs-pure-preparation-2026-10-04.md'])
    for directory,dirs,names in os.walk(p.PROJECT):
        dirs[:]=[n for n in dirs if n not in ['.lake','b','__pycache__']]
        paths.extend(Path(directory)/name for name in names if Path(directory)/name not in active)
    paths=sorted(set(paths));files=[p.binding(path) for path in paths]
    report=dict(status='PURE_AUTHOR_RUNTIME_PREPARATION_ONLY',Lean_invocations=0,Lake_invocations=0,
        author_PASS_claimed=False,candidate_actually_compiled=False,
        native_source_import_schedule_count=21,inventory_not_actual_Lean_graph=True,
        static_original_headers=16,closed_boundary_candidates=9,control_source_candidates=4,
        finite_exact_prechecks=588,finite_matrix_entry_prechecks=100,finite_checks_not_universal_proof=True,
        source_only_project_task_relative=p.PROJECT.relative_to(p.TASK).as_posix(),
        project_absent_before_creation=True,build_cache_absent=True,package_junction_absent=True,
        verified_Jets_SOURCE_override_sha256=p.JETS_SHA,shared_failed_b081_compiler_input=False,
        ja1_ni1_or_other_task_proof_objects_borrowed=False,
        existing_frozen5_38_439_and_ja1_modified=False,files=files,
        current_candidate_source=p.binding(p.CANDIDATE),planned_future_actual_calls=state['future_actual_calls'],
        Root_API_credentials_scope_modified=False)
    p.dump(p.OUT/'preparation-verification.json',report)
    p.write(p.OUT/'SHA256SUMS.txt',''.join(p.sha(path)+'  '+path.relative_to(p.TASK).as_posix()+'\n'
        for path in paths+[p.OUT/'preparation-verification.json']))
    for line in (p.OUT/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
        digest,relative=line.split('  ',1);assert p.sha(p.TASK/relative)==digest
    print(json.dumps(dict(status=report['status'],bindings=len(files),Lean_invocations=0,
        source_sha256=p.sha(p.CANDIDATE),preparation_sha256=p.sha(p.OUT/'preparation-verification.json'),
        sums_sha256=p.sha(p.OUT/'SHA256SUMS.txt'))))


if __name__=='__main__':main()
