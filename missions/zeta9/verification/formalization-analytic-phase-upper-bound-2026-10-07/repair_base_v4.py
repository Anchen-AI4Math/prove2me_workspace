"""Private V4: solve structure congruences before scalar/function normalization."""
import sys
sys.dont_write_bytecode=True
import prepare_native as p
from repair_base_v2 import prefixes

BODIES={
'hasDerivAt_mul_log_shift':'''  have h := ((hasDerivAt_id x).add_const a).mul
    (((hasDerivAt_id x).add_const a).log ha)
  convert h using 1
  all_goals first | rfl | simp [id_eq, one_div, mul_inv_cancel₀ ha]
''',
'phase_hasDerivAt':'''  have h0 : x + 0 ≠ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by linarith
  have hm : x + (-1) ≠ 0 := by linarith
  have hp : x + 1 ≠ 0 := by linarith
  have h := (((hasDerivAt_mul_log_shift x 0 h0).const_mul 10).add
    (hasDerivAt_mul_log_shift x 2 h2)).sub
    (hasDerivAt_mul_log_shift x (-1) hm)
  have h' := h.sub ((hasDerivAt_mul_log_shift x 1 hp).const_mul 10)
  convert h' using 1
  all_goals first | rfl | (simp [phase, phaseSlope, id_eq, Pi.neg_apply, sub_eq_add_neg]; ring)
''',
'phase_le_right_endpoint':'''  have h0 : (101 / 100 : ℝ) ∈ Ici (101 / 100 : ℝ) := by
    change (101 / 100 : ℝ) ≤ (101 / 100 : ℝ)
    exact le_rfl
  exact phase_strictAntiOn_right.antitoneOn h0 hx hx
'''}

def main():
    original=(p.TASK/'formalization/AnalyticPhase.lean').read_text(encoding='utf-8-sig')
    source=original
    for name,body in BODIES.items():
        start=source.index('theorem '+name);a=source.index(':=',start)+2
        end=source.find('\ntheorem ',a);assert end>0
        source=source[:a]+' by\n'+body+'\n'+source[end:]
    assert prefixes(source)==prefixes(original)
    assert source[:source.index('theorem phaseGap_identity')]==original[:original.index('theorem phaseGap_identity')]
    private=p.PROJECT/'missions/zeta9/formalization/AnalyticPhase.lean'
    snap=p.OUT/'private-source-v4/AnalyticPhase.lean'
    p.write(snap,source);p.write(private,source)
    p.dump(p.OUT/'private-base-v4-repair.json',dict(changed_theorems=list(BODIES),all15_declaration_prefixes_exact=True,
      original_header_and_definitions_exact=True,only_private_proof_bodies_changed=True,
      private_source=p.binding(private),snapshot=p.binding(snap),original_shared=p.binding(p.TASK/'formalization/AnalyticPhase.lean'),
      V3_failures_retained='actual-runs/native-base-v3-01',mathematical_content_unchanged=True))
    print('Private Base V4 prepared.',flush=True)
if __name__=='__main__':main()
