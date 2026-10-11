"""Exact checks of the rational ellipse and full output minima, no zeta decimals."""
from pathlib import Path
from fractions import Fraction as F
import sys,json,hashlib
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from probe_exterior_cone import Q,Mat,connection
from verify_vc_budget import log_interval
sys.path.insert(0,str(M/'round6/scripts'))
from independent_audit import independent_columns

def dot(u,v,gram):return sum((u[i]*gram[i,j]*v[j] for i in range(2) for j in range(2)),Q(0))
def nearest(x):
    y=F(str(x));return (2*y.numerator+y.denominator)//(2*y.denominator)
def reduce_gram(gram):
    u,v=[1,0],[0,1]
    while True:
        a=dot(u,u,gram);c=dot(v,v,gram)
        if c<a:u,v=v,u;continue
        b=dot(u,v,gram);q=nearest(b/a)
        if not q:break
        v=[v[i]-q*u[i] for i in range(2)]
    assert abs(u[0]*v[1]-u[1]*v[0])==1
    a,b,c=dot(u,u,gram),dot(u,v,gram),dot(v,v,gram)
    assert a<=c and 2*abs(b)<=a
    return u,v,a,b,c
def log_bounds(x):
    x=F(str(x));k=0
    while x>2:x/=2;k+=1
    while x<1:x*=2;k-=1
    a,b=log_interval(x);c,d=log_interval(F(2))
    return (a+k*c,b+k*d) if k>=0 else (a+k*d,b+k*c)
def main():
    targets={2,12,20,48,96};f=Mat(independent_columns(2));records=[]
    for n in range(2,max(targets)+1,2):
        if n in targets:
            inv=f.inv();e=Mat([[inv[i,j]*n**(2*j) for j in range(5)] for i in (0,4)])
            gram=e*e.transpose();area2=gram.det();t2=gram[0,0]
            xi=gram[0,1]/t2;s2=area2/t2;eta2=s2/t2
            assert t2*xi==gram[0,1] and t2*(xi*xi+eta2)==gram[1,1]
            u,v,l1,b,l2=reduce_gram(gram)
            assert l1>=min(t2,s2) and 3*l1*l1<=4*area2
            for z,length in [(u,l1),(v,l2)]:
                assert length==t2*((z[0]+z[1]*xi)**2+eta2*z[1]**2)
            records.append({'n':n,'t_squared':str(t2),'s_squared':str(s2),
                'rational_center':str(xi),'eta_squared':str(eta2),
                'first_output':list(map(str,u)),'second_output':list(map(str,v)),
                'first_norm_squared':str(l1),'second_norm_squared':str(l2)})
        if n<max(targets):f=connection(n)*f
    path=M/'verification/exterior-cone-2026-09-29/certificate.json'
    cone=json.loads(path.read_text(encoding='utf-8'))
    al,ah=map(F,cone['eigenvalue_intervals']['A']);bl,bh=map(F,cone['eigenvalue_intervals']['B'])
    rates={
      'alpha':[log_bounds(al)[0]/2,log_bounds(ah)[1]/2],
      'beta':[log_bounds(bl)[0]/2,log_bounds(bh)[1]/2],
      'gamma':[log_bounds(al*bl)[0]/4,log_bounds(ah*bh)[1]/4],
      'delta':[log_bounds(al/bh)[0]/4,log_bounds(ah/bl)[1]/4]}
    assert rates['beta'][0]>F(45293,100000)
    assert rates['beta'][1]<rates['gamma'][0]<rates['gamma'][1]<rates['alpha'][0]
    result={'status':'passed','scope':'Exact finite implementation checks of the all-output algebraic identity; rationality alternatives are proved in the note, not inferred from samples.',
      'cases':records,'rate_intervals':{k:list(map(str,v)) for k,v in rates.items()},
      'rate_display':{k:list(map(float,v)) for k,v in rates.items()},
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'cone_certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
    out=M/'verification/output-normal-form-2026-09-29';out.mkdir(parents=True,exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'passed','cases':len(records),'rate_intervals':result['rate_display']},indent=2))
if __name__=='__main__':main()
