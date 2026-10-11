"""Authorized own proof-body repair after the first real failed main compile."""
from pathlib import Path
import difflib
import prepare as p


def main():
    p.native_gate()
    receipt=p.load(p.OUT/'compile-receipt.json')
    failed=next(r for r in reversed(receipt['rows']) if
        r['label']=='source-CoefficientMapFormalTransportJets' and r['exit_code']==1)
    source=p.PROJECT/(p.NATIVE.replace('.','/')+'.lean')
    assert p.sha(source)==p.SOURCE_SHA
    old=source.read_text(encoding='utf-8-sig')
    before='  rw [h, sum_lower_zero_extension]\n  rfl\n'
    after='  rw [h]\n  exact sum_lower_zero_extension n (fun j => weightedLocalCoefficient n j s P)\n'
    assert old.count(before)==1
    new=old.replace(before,after)
    assert p.statement_headers(new.encode())==p.statement_headers(old.encode())
    p.write(p.OUT/'retained-private-main-before-repair-01.lean',source.read_bytes())
    p.write(source,new)
    p.write(p.OUT/'private-repair-01.diff',''.join(difflib.unified_diff(old.splitlines(keepends=True),
        new.splitlines(keepends=True),fromfile='initial-candidate',tofile='actual-private-repair-01')))
    p.dump(p.OUT/'private-proof-repairs.json',dict(
        shared_original_source_and_old5bindings_unchanged=True,
        proof_bodies_only_no_original_header_changes=True,
        initial_candidate_sha256=p.SOURCE_SHA,
        allowed_current_source_bindings=[p.binding(source)],
        repairs=[dict(number=1,after_actual_failed_label=failed['label'],
            after_actual_failed_attempt=failed['attempt'],actual_Lean_exit=failed['exit_code'],
            description='Supply the finite padding theorem explicit n and old-jet function; no statement change.',
            retained_before=p.binding(p.OUT/'retained-private-main-before-repair-01.lean'),
            diff=p.binding(p.OUT/'private-repair-01.diff'),after=p.binding(source))]))
    p.native_gate()
    print('PRIVATE_PROOF_REPAIR_01',p.sha(source),'original26headers unchanged')


if __name__=='__main__':main()
