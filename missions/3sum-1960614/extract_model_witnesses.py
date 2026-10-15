"""Read the already audited exact interval checker and record model witnesses."""
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import sys

here=Path(__file__).resolve().parent
source=Path('D:/users/self_projects/math_discovery/3 SUM/3sum_certificate_1p960614_v3/3sum_certificate_v3')
sys.path.insert(0,str(source))
spec=importlib.util.spec_from_file_location('audited_certificate',source/'verify_certificate.py')
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
data=json.loads((source/'certificates/c232_quartic.json').read_text(encoding='utf-8'))
t=m.rational(data['barrier_split'])
u=m.rational(data['barrier_ratio_point'])
rho=m.floor_dec((m.entropy(u)/(1+m.gamma(232,u))).lo,15)
g=m.ceil_dec(m.gamma(232,t).hi,18)
h=m.floor_dec(m.entropy(t).lo,18)
E0=m.rational(data['analytic_caps']['E_lower'])
k0=m.rational(data['analytic_caps']['kappa_lower'])
a=1-2*rho
A=F(1,2)-k0-rho
UG=(2*A+a*g)/3
UH=(1-2*rho-k0-a*h)/(2-rho)
U=max(UG,UH)
C=a*E0-A
lower=2-a*U/(C+(2-rho)*U)
record={key:str(value) for key,value in dict(t=t,u=u,rho=rho,gamma_upper=g,
    entropy_lower=h,E_lower=E0,kappa_lower=k0,a=a,A=A,UG=UG,UH=UH,U=U,C=C,
    model_lower=lower).items()}
assert C>0 and U>0 and lower>F(196061349120,100000000000)
(here/'verification/model-witnesses.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
formal_g=F(318487605190926,10**15)
formal_h=F(244168410993740,10**15)
formal_U=F(193175572822,10**12)
assert g<=formal_g and formal_h<=h
assert (2*A+a*formal_g)/3<=formal_U
assert (1-2*rho-k0-a*formal_h)/(2-rho)<=formal_U
formal_lower=2-a*formal_U/(C+(2-rho)*formal_U)
assert formal_lower>F(196061349120,100000000000)
formal={key:str(value) for key,value in dict(gamma_upper=formal_g,entropy_lower=formal_h,
    saving_upper=formal_U,model_lower=formal_lower).items()}
(here/'verification/model-formal-witnesses.json').write_text(json.dumps(formal,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
