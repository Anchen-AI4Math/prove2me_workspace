"""Use the finite ledger maximum in the operational cost assembly.

Run after the preceding scoped component build completes. Analytic principal
certificates and the frozen benchmark statement are kept in their own modules.
Every edited operational proof must be rebuilt before publication.
"""
from pathlib import Path
import re
root=Path(__file__).resolve().parent/'machine/lean/Submission/ThreeSum'
changed=[]
for p in sorted(root.glob('*.lean')):
    if p.stem in ('Parameters','AnalysisDefinitions','RawCostExponent'):
        continue
    original=p.read_text(encoding='utf-8')
    s=re.sub(r'\bcertificateExponent\b','rawCostExponent',original)
    s=s.replace('all_costs_le_certificate','all_costs_le_raw_exponent')
    s=s.replace('certificate_lt_target','raw_exponent_lt_target')
    if s==original: continue
    s=s.replace('by norm_num [rawCostExponent]','by linarith [raw_exponent_lower]')
    s=s.replace('norm_num [rawCostExponent]','linarith [raw_exponent_lower]')
    s=s.replace('unfold rawCostExponent; norm_num','exact raw_exponent_nonnegative')
    s=s.replace('unfold rawCostExponent epsilon',
                'unfold epsilon\n    have hraw := raw_exponent_lower')
    s=s.replace('unfold rawCostExponent', 'have hraw := raw_exponent_lower')
    s=s.replace('by norm_num [bandShift,epsilon,rawCostExponent]',
                'by\n    have hraw := raw_exponent_lower\n    norm_num [bandShift,epsilon]\n    linarith')
    if 'import Submission.ThreeSum.RawCostExponent' not in s:
        s='import Submission.ThreeSum.RawCostExponent\n'+s
    p.write_text(s,encoding='utf-8')
    changed.append(p.stem)
print('Operational maximum migration:',len(changed),'modules. A scoped rebuild is required.')
