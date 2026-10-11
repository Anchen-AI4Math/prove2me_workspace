"""Private Upper V2 fixes actual derivative congruence and elementary cap elaboration."""
import sys
sys.dont_write_bytecode=True
import prepare_native as p
from repair_base_v2 import prefixes

def main():
    original=(p.TASK/'formalization/AnalyticPhaseUpperBound.lean').read_text(encoding='utf-8-sig')
    source=original.replace('  convert h using 1 <;>\n    simp only [smoothPhaseGap, smoothPhaseSlope, add_zero, sub_eq_add_neg] <;> ring',
      '  convert h using 1\n  all_goals first | rfl | (funext y; simp [smoothPhaseGap, id_eq, Pi.neg_apply, sub_eq_add_neg]; ring) | (simp [smoothPhaseSlope, id_eq, sub_eq_add_neg]; ring)')
    source=source.replace('    field_simp [ne_of_gt hu]\n    ring\n  calc','    field_simp [ne_of_gt hu]\n  calc')
    source=source.replace('add_le_add_left hmul u','add_le_add (le_refl u) hmul')
    assert source!=original and prefixes(source)==prefixes(original)
    assert source[:source.index('theorem phase_one_eq')]==original[:original.index('theorem phase_one_eq')]
    private=p.PROJECT/'missions/zeta9/formalization/AnalyticPhaseUpperBound.lean';snap=p.OUT/'private-source-upper-v2/AnalyticPhaseUpperBound.lean'
    p.write(snap,source);p.write(private,source)
    p.dump(p.OUT/'private-upper-v2-repair.json',dict(changed_theorems=['smoothPhaseGap_hasDerivAt','mul_one_add_log_div_le'],
      all19_declaration_prefixes_exact=True,original_header_and_definitions_exact=True,only_private_proof_bodies_changed=True,
      private_source=p.binding(private),snapshot=p.binding(snap),original_shared=p.binding(p.TASK/'formalization/AnalyticPhaseUpperBound.lean'),
      V1_failures_retained='actual-runs/native-upper-v1-01'))
    print('Private Upper V2 prepared.',flush=True)
if __name__=='__main__':main()
