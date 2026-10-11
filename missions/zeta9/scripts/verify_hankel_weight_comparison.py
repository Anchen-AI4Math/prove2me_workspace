"""Exact Eulerian identities and finite rigorous checks of weight comparison."""
from pathlib import Path
import sys, json, hashlib
from fractions import Fraction
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from probe_positive_hankel import P,Q,arb,ctx


def ballq(value):
    f=Fraction(value)
    return arb(f.numerator)/f.denominator


def log_primitive(row):
    coeff=list(map(int,row['primitive_integer_coefficients']))
    ctx.prec=max(512,max(abs(c).bit_length() for c in coeff)+512)
    z=arb(row['s']).zeta();v=arb(0)
    for c in reversed(coeff): v=v*z+c
    assert v>0 and v.rel_accuracy_bits()>80
    return v.log()


def main():
    x=P([0,1]);a=P([1]);found={0:a}
    # sum l^m q^l=q A_m(q)/(1-q)^(m+1), m>=1.
    a=P([1]);found={1:a}
    for m in range(1,8):
        a=(1+m*x)*a+x*(1-x)*a.derivative()
        found[m+1]=a
    assert list(found[4])==[1,11,11,1]
    assert list(found[8])==[1,247,4293,15619,15619,4293,247,1]
    assert all(c>=0 for c in found[8]-found[4])
    assert found[8](1)==40320
    data=json.loads((M/'verification/positive-hankel-2026-09-29/certificate.json').read_text())
    rows=[]
    for k in (4,8,12,16,20,24,32,40):
        pair=[next(c for c in data['cases'] if c['s']==s and c['K']==k and c['power']==6) for s in (5,9)]
        v5=log_primitive(pair[0]);v9=log_primitive(pair[1])
        logscale=ballq(pair[1]['positive_multiplier']).log()-ballq(pair[0]['positive_multiplier']).log()
        real=v9-v5-logscale
        h=pair[0]['h'];u=6*pair[0]['N']
        lower=-h*arb(1680).log()
        upper=h*arb(6144*(k+1)**4).log()+(6*h+2*h*(h-1)+2*u*h)*(arb(k+1)/k).log()
        assert real>lower and real<upper
        rows.append({'K':k,'h':h,'numerator_degree_bound':u,
          'normalized_log_difference_over_K2':((v9-v5)/(k*k)).str(30),
          'scalar_log_difference_over_K2':(logscale/(k*k)).str(30),
          'real_log_difference_over_K2':(real/(k*k)).str(30),
          'proved_lower_log_ratio':lower.str(30),'proved_upper_log_ratio':upper.str(30),
          'strict_ball_comparison':True})
    out=M/'verification/hankel-weight-comparison-2026-09-30';out.mkdir(parents=True,exist_ok=True)
    result={'status':'PASS','cases':rows,
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'input_certificate_sha256':hashlib.sha256((M/'verification/positive-hankel-2026-09-29/certificate.json').read_bytes()).hexdigest(),
      'boundary':'All-parameter bound comes from the written integral proof; these are finite checks only.'}
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','case_count':len(rows),'last':rows[-1]}))


if __name__=='__main__':main()
