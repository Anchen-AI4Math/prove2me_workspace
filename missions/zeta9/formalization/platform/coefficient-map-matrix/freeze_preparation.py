"""Freeze pure Matrix preparation bytes, never run Lean or make author claims."""
from pathlib import Path
import json, os
import prepare as p


def main():
    p.native_gate()
    assert not (p.OUT/'compile-receipt.json').exists()
    assert not (p.PROJECT/'b').exists() and not (p.PROJECT/'.lake').exists()
    state = p.load(p.OUT/'preparation-state.json')
    assert state['status'] == 'PREPARATION_ONLY' and not state['Lean_executed']
    assert not state['Stage1_Stage2_results_claimed'] and not state['author_PASS_claimed']
    assert len(state['native_sources']) == 13 and len(state['parent_definitions']) == 12
    assert len(state['native_controls']) == 4 and len(state['selected_actual_endpoints']) == 3
    assert all(row['passed'] and row['path_plus_64'] <= 259 for row in state['path_checks'])
    assert (p.PROJECT/'lean_call.py').read_bytes() == (p.OUT/'lean_call.template.py').read_bytes()
    files = [path for path in p.OUT.rglob('*') if path.is_file()
        and '__pycache__' not in path.parts and path.name not in
        ['preparation-verification.json','PREPARATION_SHA256SUMS.txt']]
    for directory, directories, names in os.walk(p.PROJECT):
        directories[:] = [name for name in directories if name not in ['.lake','b','__pycache__']]
        files.extend(Path(directory)/name for name in names)
    files = sorted(set(files))
    report = dict(status='PREPARATION_ONLY_BYTES_VERIFIED',Lean_executed=False,
        Stage1_Stage2_results_claimed=False,author_PASS_claimed=False,
        source_sha256=p.SOURCE_SHA,native_author_sha256=p.AUTHOR_SHA,
        native_independent_sha256=p.INDEPENDENT_SHA,verified_native_bindings=517,
        native_sources=13,parent_Definitions=12,native_controls=4,selected_targets=3,
        new_Definitions=5,source_proofs=17,files=[p.binding(path) for path in files],
        pending=['Root lane grant', '44 actual native/source/control/oracle calls',
            'actual graph/valueRefs and source parser proof closure',
            'five whole native/staged shared-alias kernel comparisons per environment',
            'complete staged proofs/reference statement compilation and exact type/axiom audits',
            'actual native/staged controls, module resolution and author evidence freeze',
            'independent platform transplantation review', 'Root scoped build and external acceptance'])
    p.dump(p.OUT/'preparation-verification.json',report)
    p.write(p.OUT/'PREPARATION_SHA256SUMS.txt',''.join(p.sha(path)+'  '+
        Path(os.path.relpath(path,p.OUT)).as_posix()+'\n'
        for path in files+[p.OUT/'preparation-verification.json']))
    for row in report['files']:
        path=p.TASK/row['task_relative']
        assert p.sha(path)==row['sha256'] and path.stat().st_size==row['bytes']
    print(json.dumps(dict(status=report['status'],files=len(files),Lean_executed=False,
        preparation_sha256=p.sha(p.OUT/'preparation-verification.json'))))


if __name__ == '__main__':main()
