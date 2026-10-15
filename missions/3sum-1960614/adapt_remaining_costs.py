"""Update the concrete epsilon factors and final target in selected cost modules."""
from pathlib import Path
import re
root=Path(__file__).resolve().parent/'machine/lean/Submission/ThreeSum'
rates=('BandPrimeCostBounds','EncodedColorResourceScale','EncodedColorTimeCounts',
       'EncodedColorTimeNormalize','EncodedColorTimeWanted')
for name in rates:
    p=root/(name+'.lean')
    s=p.read_text(encoding='utf-8')
    for old,new in (
        ('(E+bandShift)/5','epsilon*(E+bandShift)'),
        ('(E+1/2)/5','epsilon*(E+1/2)'),
        ('(Parameters.E+1/2)/5','Parameters.epsilon*(Parameters.E+1/2)'),
        ('2*E/5','2*epsilon*E'),
        ('(1/2+bandShift)/5','epsilon*(1/2+bandShift)'),
        ('unfold certificateExponent','unfold certificateExponent epsilon'),
        ('[bandShift,certificateExponent]','[bandShift,epsilon,certificateExponent]'),
        ('have hh := Parameters.E_bounds.2; linarith',
         'have hh := Parameters.E_bounds.2; unfold Parameters.epsilon; linarith'),
    ):
        s=s.replace(old,new)
    s=re.sub(r'\bunfold bandShift(?: epsilon)*','unfold bandShift epsilon',s)
    p.write_text(s,encoding='utf-8')

targets=('BandPrimeCostBounds','ThreeSumParameterResourcesTime','ThreeSumHybridCosts',
         'ThreeSumHybridEndBridge','Target','FinalSolver','EncodedColorPipelineTime',
         'EncodedColorReportingCosts','LightDenseSetupCosts','SharedReportingBankCosts',
         'SharedTraversalDispatchCosts','SharedTraversalScanCosts','ThreeSumColorDriverCosts')
for name in targets:
    p=root/(name+'.lean')
    s=p.read_text(encoding='utf-8').replace('981/500','980307/500000').replace('981 / 500','980307 / 500000')
    if name=='FinalSolver':
        s=s.replace('solvedInTime_981_500','solvedInTime_980307_500000')
    p.write_text(s,encoding='utf-8')
print('Updated selected raw cost factors and the exact rational target.')
