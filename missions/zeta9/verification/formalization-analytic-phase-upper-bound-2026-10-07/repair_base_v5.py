"""Private V5: explicitly extensionalize the phase function congruence."""
import sys
sys.dont_write_bytecode=True
import prepare_native as p
from repair_base_v2 import prefixes
from repair_base_v4 import BODIES

def main():
    original=(p.TASK/'formalization/AnalyticPhase.lean').read_text(encoding='utf-8-sig')
    source=original; bodies=dict(BODIES)
    bodies['phase_hasDerivAt']=bodies['phase_hasDerivAt'].replace(
      '  all_goals first | rfl | (simp [phase, phaseSlope, id_eq, Pi.neg_apply, sub_eq_add_neg]; ring)',
      '  all_goals first | rfl | (funext y; simp [phase, Pi.neg_apply, sub_eq_add_neg]; ring) | (simp [phaseSlope, id_eq, sub_eq_add_neg]; ring)')
    for name,body in bodies.items():
        a=source.index(':=',source.index('theorem '+name))+2
        end=source.find('\ntheorem ',a);assert end>0
        source=source[:a]+' by\n'+body+'\n'+source[end:]
    assert prefixes(source)==prefixes(original)
    assert source[:source.index('theorem phaseGap_identity')]==original[:original.index('theorem phaseGap_identity')]
    private=p.PROJECT/'missions/zeta9/formalization/AnalyticPhase.lean';snap=p.OUT/'private-source-v5/AnalyticPhase.lean'
    p.write(snap,source);p.write(private,source)
    p.dump(p.OUT/'private-base-v5-repair.json',dict(changed_theorems=list(bodies),all15_declaration_prefixes_exact=True,
      original_header_and_definitions_exact=True,only_private_proof_bodies_changed=True,private_source=p.binding(private),
      snapshot=p.binding(snap),original_shared=p.binding(p.TASK/'formalization/AnalyticPhase.lean'),V4_failures_retained='actual-runs/native-base-v4-01'))
    print('Private Base V5 prepared.',flush=True)
if __name__=='__main__':main()
