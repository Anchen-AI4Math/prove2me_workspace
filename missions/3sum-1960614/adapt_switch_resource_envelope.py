"""Update only the inherited envelope for the actual quartic program scalars."""
from pathlib import Path
root=Path(__file__).resolve().parent/'machine/lean/Submission/ThreeSum'
for name in ('SharedReportingBankResourceBounds','SharedReportingBankResourceBoundsScales',
             'SharedReportingBankResourceBoundsPolynomial'):
    p=root/(name+'.lean')
    s=p.read_text(encoding='utf-8')
    s=s.replace('1001','1000000001').replace('^64','^96').replace(') 64',') 96').replace('.pow 64','.pow 96')
    s=s.replace('131072','196608')
    p.write_text(s,encoding='utf-8')
p=root/'EncodedColorWantedConsumerEnds.lean'
s=p.read_text(encoding='utf-8').replace('LocalMaskGraph.maskAt (512*','LocalMaskGraph.maskAt (464*')
p.write_text(s,encoding='utf-8')
