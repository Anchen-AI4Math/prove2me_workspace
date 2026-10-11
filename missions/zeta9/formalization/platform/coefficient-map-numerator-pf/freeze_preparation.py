"""Freeze pure GenericNumeratorPF preparation; execute no Lean/Lake."""
from pathlib import Path
import json,os,sys
import prepare as p


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    p.native_gate()
    assert not (p.OUT/'preparation-verification.json').exists()
    assert not (p.OUT/'compile-receipt.json').exists()
    assert not (p.PROJECT/'b').exists() and not (p.PROJECT/'.lake').exists()
    state=p.load(p.OUT/'preparation-state.json')
    assert state['status']=='PREPARATION_ONLY' and state['Lean_executed'] is False
    assert not state['Stage1_Stage2_results_claimed'] and not state['author_PASS_claimed']
    assert len(state['native_sources'])==16 and len(state['parent_definitions'])==5
    assert len(state['native_controls'])==4 and len(state['selected_actual_endpoints'])==3
    assert state['future_oracle_calls']['total']==43
    assert state['minimal_new_Definitions_membership'] is None
    assert state['actual_proof_closure_size'] is None and state['actual_definition_valueRefs'] is None
    assert all(row['passed'] and row['path_plus_64']<=259 for row in state['path_checks'])
    assert (p.PROJECT/'lean_call.py').read_bytes()==(p.OUT/'lean_call.template.py').read_bytes()
    files=[path for path in p.OUT.rglob('*') if path.is_file() and '__pycache__' not in path.parts
        and path.name not in ['preparation-verification.json','PREPARATION_SHA256SUMS.txt']]
    for directory,dirs,names in os.walk(p.PROJECT):
        dirs[:]=[name for name in dirs if name not in ['.lake','b','__pycache__']]
        files.extend(Path(directory)/name for name in names)
    files=sorted(set(files))
    report=dict(status='PREPARATION_ONLY_BYTES_VERIFIED',Lean_executed=False,
        Stage1_Stage2_results_claimed=False,author_PASS_claimed=False,
        source_sha256=p.SOURCE_SHA,native_author_sha256=p.AUTHOR_SHA,
        native_independent_sha256=p.INDEPENDENT_SHA,
        verified_author_bindings=188,verified_independent_bindings=388,
        native_sources=16,parent_Definitions=5,native_controls=4,selected_targets=3,
        minimal_new_Definitions_membership=None,PF_source_definitions=4,PF_source_proofs=23,
        future_initial_actual_calls=43,files=[p.binding(path) for path in files],
        pending=['Root lane grant','43 real source/control/Stage1/Stage2/header/runtime calls',
            'actual minimal Data/PF definition and helper closure selection',
            'full type/value native/staged kernel comparisons and closed whole-function rfl',
            'three complete staged proofs and explicit reference statement compilation',
            'actual expected-type and relevant boundary replay with exclusions listed',
            'module resolution and complete author evidence freeze',
            'independent platform transplantation review','Root scoped build and platform acceptance'])
    p.dump(p.OUT/'preparation-verification.json',report)
    p.write(p.OUT/'PREPARATION_SHA256SUMS.txt',''.join(p.sha(path)+'  '+
        Path(os.path.relpath(path,p.OUT)).as_posix()+'\n' for path in files+[p.OUT/'preparation-verification.json']))
    for row in report['files']:
        path=p.TASK/row['task_relative']
        assert p.sha(path)==row['sha256'] and path.stat().st_size==row['bytes']
    print(json.dumps(dict(status=report['status'],files=len(files),Lean_executed=False,
        preparation_sha256=p.sha(p.OUT/'preparation-verification.json'),
        sums_sha256=p.sha(p.OUT/'PREPARATION_SHA256SUMS.txt'))))


if __name__=='__main__':main()
