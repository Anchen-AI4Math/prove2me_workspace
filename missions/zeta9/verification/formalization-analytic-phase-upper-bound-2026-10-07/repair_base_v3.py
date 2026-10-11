"""Private finalization of derivative congruence and typed endpoint membership."""
import re,sys
sys.dont_write_bytecode=True
import prepare_native as p
from repair_base_v2 import prefixes

BODIES={
'hasDerivAt_mul_log_shift':'''  have h := ((hasDerivAt_id x).add_const a).mul
    (((hasDerivAt_id x).add_const a).log ha)
  simpa only [id_eq, one_mul, one_div, mul_inv_cancel₀ ha] using h
''',
'phase_hasDerivAt':'''  have h0 : x + 0 ≠ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by linarith
  have hm : x + (-1) ≠ 0 := by linarith
  have hp : x + 1 ≠ 0 := by linarith
  have h := (((hasDerivAt_mul_log_shift x 0 h0).const_mul 10).add
    (hasDerivAt_mul_log_shift x 2 h2)).sub
    (hasDerivAt_mul_log_shift x (-1) hm)
  have h' := h.sub ((hasDerivAt_mul_log_shift x 1 hp).const_mul 10)
  have hd :
      10 * (Real.log (x + 0) + 1) + (Real.log (x + 2) + 1) -
        (Real.log (x + (-1)) + 1) - 10 * (Real.log (x + 1) + 1) = phaseSlope x := by
    simp only [phaseSlope, add_zero, sub_eq_add_neg]
    ring
  apply (h'.congr_deriv hd).congr_of_eventuallyEq
  filter_upwards [] with y
  simp only [phase, Pi.add_apply, Pi.sub_apply, add_zero, sub_eq_add_neg]
  ring
''',
'phase_le_right_endpoint':'''  have h0 : (101 / 100 : ℝ) ∈ Ici (101 / 100 : ℝ) := le_rfl
  exact phase_strictAntiOn_right.antitoneOn h0 hx hx
'''}

def main():
    original=(p.TASK/'formalization/AnalyticPhase.lean').read_text(encoding='utf-8-sig')
    source=original
    for name,body in BODIES.items():
        marker='theorem '+name
        start=source.index(marker);a=source.index(':=',start)+2
        end=source.find('\ntheorem ',a)
        assert end>0
        source=source[:a]+' by\n'+body+'\n'+source[end:]
    assert prefixes(source)==prefixes(original)
    assert source[:source.index('theorem phaseGap_identity')]==original[:original.index('theorem phaseGap_identity')]
    private=p.PROJECT/'missions/zeta9/formalization/AnalyticPhase.lean'
    p.write(p.OUT/'private-source-v3/AnalyticPhase.lean',source);p.write(private,source)
    p.dump(p.OUT/'private-base-v3-repair.json',dict(changed_theorems=list(BODIES),all15_declaration_prefixes_exact=True,
      original_header_and_definitions_exact=True,only_private_proof_bodies_changed=True,
      private_source=p.binding(private),snapshot=p.binding(p.OUT/'private-source-v3/AnalyticPhase.lean'),
      original_shared=p.binding(p.TASK/'formalization/AnalyticPhase.lean'),
      V2_failures_retained='actual-runs/native-base-v2-01',
      mathematical_content_unchanged=True))
    print('Private Base V3 explicit derivative congruence prepared.',flush=True)
if __name__=='__main__':main()
