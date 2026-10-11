"""Private elaboration-only repair after retained actual Outputs failure."""
from pathlib import Path
import json,sys
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];PROJECT=TASK/'.rt/oa1'
PREP=TASK/'verification/formalization-coefficient-map-formal-transport-outputs-preparation-2026-10-04'
sys.path.insert(0,str(PREP));import prepare as p
receipt=p.load(OUT/'compile-receipt.json')
failure=receipt['rows'][-1]
assert failure['label']=='source-CoefficientMapFormalTransportOutputs' and failure['exit_code']==1
assert failure['failure_retained'] and failure['actual_original_input_output_metadata_preserved']
paths=[PROJECT/'missions/zeta9/formalization/CoefficientMapFormalTransportOutputs.lean',
       PROJECT/'OutputsFullTypeAudit.lean']
records=[];versions=OUT/'versions/v2';versions.mkdir(parents=True,exist_ok=False)
for path in paths:
    original=path.read_bytes();assert original.count(b'open scoped BigOperators\n')==1
    revised=original.replace(b'open scoped BigOperators\n',b'open scoped BigOperators Matrix\n',1)
    if path.name=='CoefficientMapFormalTransportOutputs.lean':
        needle=b'    Nat.cast_add, Nat.cast_one, add_comm] using h.symm'
        assert revised.count(needle)==1
        revised=revised.replace(needle,b'    Nat.cast_add, Nat.cast_one, add_comm (1 : \xe2\x84\x9a)] using h.symm',1)
        assert p.sha(path)=='f16dc8be54bd58c09f240ed3404ba3810297e1a8e9d9ab9806893d410862f09d'
    assert p.statement_headers(revised)==p.statement_headers(original)
    if path.name=='OutputsFullTypeAudit.lean':
        assert revised.split(b'\nopen Lean Meta\n')[-1]==original.split(b'\nopen Lean Meta\n')[-1]
    snapshot=versions/path.name;snapshot.write_bytes(revised);path.write_bytes(revised)
    records.append(dict(previous_sha256=p.sha(TASK/failure['retained_input_bindings'][-1]['snapshot_binding']['task_relative'])
        if path.name=='CoefficientMapFormalTransportOutputs.lean' else None,
        snapshot=p.binding(snapshot),current=p.binding(path),full_headers_preserved=True))
ledger=dict(role='Private v2 after actual recorded failure; original complete headers unchanged',
    original_source_headers_preserved=True,shared_original_and_frozen_sources_unchanged=True,
    retained_failure_log=failure['log'],retained_failure_attempt=failure['attempt'],
    mathematical_hypotheses_or_conclusions_changed=False,
    changes=['Only rational add_comm at remainder PF cast normalization','Open actual Matrix notation scope in private source/control context'],
    allowed_current_source_bindings=[row['current'] for row in records],records=records)
p.dump(OUT/'private-proof-repairs.json',ledger)
print(json.dumps(dict(private_versions=[row['current'] for row in records],all16_complete_headers_preserved=True)))
