"""Private-only proof-body compatibility repair; all shared bytes stay frozen."""
import re,sys
sys.dont_write_bytecode=True
import prepare_native as p
def prefixes(source):
    result={}
    matches=list(re.finditer(r'(?m)^theorem (\w+)',source))
    for row in matches:
        end=source.index(':=',row.end())
        result[row.group(1)]=source[row.start():end+2]
    return result
def main():
    original=(p.TASK/'formalization/AnalyticPhase.lean').read_text(encoding='utf-8-sig')
    assert p.sha(p.TASK/'formalization/AnalyticPhase.lean')==p.EXPECTED['AnalyticPhase']
    private=p.PROJECT/'missions/zeta9/formalization/AnalyticPhase.lean'
    assert private.read_text(encoding='utf-8-sig')==original
    source=original.replace('  convert h using 1 <;> field_simp [ha] <;> ring',
      '  have hd : (x + a) * (1 / (x + a)) = 1 := by\n    field_simp [ha]\n  simpa [id_eq, hd] using h')
    source=source.replace('  convert h\' using 1 <;> simp only [phase, phaseSlope, add_zero, sub_eq_add_neg] <;> ring',
      '  convert h\' using 1 <;> (try simp only [phase, phaseSlope, add_zero, sub_eq_add_neg]) <;> ring')
    source=source.replace('    phase_strictAntiOn_right.antitoneOn (by exact le_rfl) hx hx',
      '    phase_strictAntiOn_right.antitoneOn\n      (show (101 / 100 : ℝ) ∈ Ici (101 / 100 : ℝ) from le_rfl) hx hx')
    assert source!=original and prefixes(source)==prefixes(original)
    assert source[:source.index('theorem phaseGap_identity')]==original[:original.index('theorem phaseGap_identity')]
    p.write(p.OUT/'private-source-v2/AnalyticPhase.lean',source)
    p.write(private,source)
    p.dump(p.OUT/'private-base-v2-repair.json',dict(reason='Actual native-base-v1 failures: redundant no-progress tactics and untyped endpoint membership',
      only_private_proof_bodies_changed=True,all15_declaration_prefixes_exact=True,original_header_and_definitions_exact=True,
      original_shared=p.binding(p.TASK/'formalization/AnalyticPhase.lean'),private_corrected=p.binding(private),
      corrected_source_snapshot=p.binding(p.OUT/'private-source-v2/AnalyticPhase.lean'),
      failures_retained='actual-runs/native-base-v1-01',
      changed_theorems=['hasDerivAt_mul_log_shift','phase_hasDerivAt','phase_le_right_endpoint']))
    print('Prepared private Base V2, unchanged 15 statement prefixes/header/definitions.',flush=True)
if __name__=='__main__':main()
