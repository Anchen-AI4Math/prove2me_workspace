"""Freeze a real-source setup, not any Lean result. Never invokes Lean/Lake."""
from pathlib import Path
import json,sys
import prepare as p


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    p.native_gate()
    assert not (p.OUT/'preparation-verification.json').exists()
    assert not (p.OUT/'compile-receipt.json').exists()
    assert not (p.PROJECT/'b').exists() and not (p.PROJECT/'.lake').exists()
    state=p.load(p.OUT/'preparation-state.json')
    assert state['source_count']==19 and state['future_actual_calls']['total']==23
    assert state['static_source_inventory_count']==26 and state['future_boundary_proof_count']==15
    files=[path for path in sorted(p.OUT.rglob('*')) if path.is_file()
        and '__pycache__' not in path.parts and path.name not in
        ['preparation-verification.json','PREPARATION_SHA256SUMS.txt']]
    files += [p.TASK/r['immutable_initial_snapshot']['task_relative'] for r in state['source']]
    files += [p.PROJECT/name for name in ['lakefile.lean','lean-toolchain','lake-manifest.json',
        'lean_call.py','resolver.lean']]
    files=sorted(set(files))
    report=dict(status='PURE_AUTHOR_RUNTIME_PREPARATION_ONLY',Lean_invocations=0,Lake_invocations=0,
        source_sha256=p.SOURCE_SHA,original5bindings_manifest_sha256=p.PREP_SHA,
        author_PASS_claimed=False,actual_type_graph_kernel_claimed=False,
        source_count=19,expected_type_candidates=26,boundary_proof_candidates=15,
        future_actual_calls=23,own_cache_absent=True,own_package_junction_absent=True,
        initial_source_project_copies_are_explicit_bindings=True,
        private_project_proof_repairs_require_retained_actual_failures_and_exact_original_headers=True,
        files=[p.binding(path) for path in files],
        pending=['Root hash/binding verification','explicit Root lane grant',
            'fresh compile all19 sources; no proof objects from any previous runtime',
            'actual full source/expected type kernel and standard axiom records',
            'actual15 closed boundary controls and own21 module resolutions',
            'all handles terminal and honest author freeze','independent native review'])
    p.dump(p.OUT/'preparation-verification.json',report)
    p.write(p.OUT/'PREPARATION_SHA256SUMS.txt',''.join(p.sha(path)+'  '+
        path.relative_to(p.TASK).as_posix()+'\n' for path in files+[p.OUT/'preparation-verification.json']))
    for row in report['files']:
        path=p.TASK/row['task_relative']
        assert path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256']
    print(json.dumps(dict(status=report['status'],files=len(files),Lean_invocations=0,
        preparation_sha256=p.sha(p.OUT/'preparation-verification.json'),
        sums_sha256=p.sha(p.OUT/'PREPARATION_SHA256SUMS.txt'))))


if __name__=='__main__':main()
