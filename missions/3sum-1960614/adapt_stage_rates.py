"""Replace only the old epsilon factors in the selected operational rate port."""
from pathlib import Path

root=Path(__file__).resolve().parent/'machine/lean/Submission/ThreeSum'
changes={
    '(E + bandShift) / 5':'epsilon * (E + bandShift)',
    '2 * E / 5':'2 * epsilon * E',
    '(E + 1 / 2) / 5':'epsilon * (E + 1 / 2)',
    '(1 / 2 + bandShift) / 5':'epsilon * (1 / 2 + bandShift)',
    '(1 / 2 - bandShift) / 5':'epsilon * (1 / 2 - bandShift)',
    '(2 * E + 2 * bandShift - boxSaving) / 5':'epsilon * (2 * E + 2 * bandShift - boxSaving)',
    'entropy initialTheta / 5':'epsilon * entropy initialTheta',
    '(entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5':'epsilon * (entropyRatio * (1 + boxSaving - 2 * bandShift))',
    'kappa / 5':'epsilon * kappa',
    '(1 - terminalFraction) / 5':'epsilon * (1 - terminalFraction)',
    '(1 / (5 * Real.log 2))':'(epsilon / Real.log 2)',
    '(E+1/2)/5':'epsilon*(E+1/2)',
    '(E+bandShift)/5':'epsilon*(E+bandShift)',
}
for name in ('MassScales.lean','StageBounds.lean','UniformStageBounds.lean','ArithmeticStageBounds.lean'):
    p=root/name
    s=p.read_text(encoding='utf-8')
    if name == 'ArithmeticStageBounds.lean':
        s=s.replace('232','256')
    for old,new in changes.items():
        s=s.replace(old,new)
    p.write_text(s,encoding='utf-8')
    print(name,'updated')
