"""Pure new runtime derivation from explicit frozen recorder SOURCE only."""
import prepare as p


def main():
    original=p.TASK/'verification/formalization-coefficient-map-formal-transport-jets-author-2026-10-04/execute.py'
    retaining=p.TASK/'verification/formalization-coefficient-map-formal-transport-jets-author-2026-10-04/retain_actual_inputs.py'
    text=original.read_text(encoding='utf-8-sig')
    text=text.replace('Jets native author','Outputs native author').replace('Jets native','Outputs native')
    text=text.replace('all38','all Outputs').replace('all26','all16')
    text=text.replace("    state=gate()\n    if not (OUT/'compile-receipt.json').exists():",
        "    assert (OUT/'Root-lane-grant.json').is_file(), 'Explicit current Root grant file required.'\n    state=gate()\n    if not (OUT/'compile-receipt.json').exists():")
    text=text.replace('assert len(latest)==23','assert len(latest)==27')
    text=text.replace('assert len(resolved)==21','assert len(resolved)==25')
    p.write(p.OUT/'execute.py',text)
    p.write(p.OUT/'retain_actual_inputs.py',retaining.read_bytes())
    p.dump(p.OUT/'runner-provenance.json',dict(role='SOURCE-only recorder reuse, no execution',
        original_recorder_source=p.binding(original),original_retaining_source=p.binding(retaining),
        new_recorder_source=p.binding(p.OUT/'execute.py'),new_retaining_source=p.binding(p.OUT/'retain_actual_inputs.py'),
        Lean_invocations=0,new_explicit_Root_grant_file_required=True,
        all_actual_inputs_logs_exits_path_selection_and_partial_objects_to_be_retained=True,
        initial_original_headers_must_remain_exact_on_any_future_private_proof_repair=True,
        Root_API_credentials_scope_modified=False))
    print('PURE_RUNTIME_SOURCE_PREPARED',p.sha(p.OUT/'execute.py'))


if __name__=='__main__':main()
