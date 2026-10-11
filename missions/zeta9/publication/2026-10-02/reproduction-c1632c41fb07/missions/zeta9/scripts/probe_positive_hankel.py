"""Exact positive-Hankel polynomials; finite Arb evaluations are diagnostics only."""
from pathlib import Path
import sys, math, json, hashlib, argparse
from fractions import Fraction

M = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(M/'scripts'))
import verify_local_connection  # existing python-flint path
from flint import fmpq as Q, fmpq_poly as P, fmpq_mat as Mat, arb, ctx
sys.set_int_max_str_digits(0)
x = P([0, 1])

def D(k):
    p = P([1])
    for j in range(1, k+1): p *= x+j*j
    return p

def moment(s, e):
    return (-1)**e * Q.bernoulli(2*e+2) * Q(math.prod(range(2*e+3,2*e+s+1)), math.factorial(s-1))

def construct(s, k, n, power, verbose=True):
    assert s >= 3 and s%2 and 0 <= n < k and power >= 1
    h = k-n; dn = D(n); tail = D(k)//dn; dt = tail.derivative()
    weight = dn**(power-1)
    harms={j:sum((Q(1,v**s) for v in range(1,j+1)),Q(0)) for j in range(n+1,k+1)}
    entries=[]
    for r in range(2*h-1):
        num=weight*x**r; quotient,remainder=divmod(num,tail)
        a=sum((quotient[e]*moment(s,e) for e in range(len(quotient))),Q(0));b=Q(0)
        for j in range(n+1,k+1):
            residue=remainder(-j*j)/dt(-j*j)
            a+=residue*(-j**(s-1)*harms[j]-Q(1,s-1)+Q(1,2*j))
            b+=residue*j**(s-1)
        entries.append((a,b))
    A=Mat([[entries[i+j][0] for j in range(h)] for i in range(h)])
    B=Mat([[entries[i+j][1] for j in range(h)] for i in range(h)])
    expected=Q((-1)**(h*(h-1)//2))
    for j in range(n+1,k+1): expected*=j**(s-1)*dn(-j*j)**(power-1)
    assert B.det()==expected and expected
    delta=(-B.inv()*A).charpoly()*expected
    assert delta.degree()==h
    for t in (0,1,-1): assert delta(t)==(A+t*B).det()
    denominator=math.lcm(*(int(c.denom()) for c in delta))
    integers=[int((c*denominator).numer()) for c in delta]
    content=math.gcd(*integers)
    integers=[v//content for v in integers]
    assert math.gcd(*integers)==1
    polynomial=P(integers)
    assert polynomial==delta*Q(denominator,content)
    precision=max(512,max(abs(v).bit_length() for v in integers)+256)
    for attempt in range(5):
        ctx.prec=precision; z=arb(s).zeta();value=arb(0)
        for c in reversed(integers): value=value*z+c
        if value>0 and value.rel_accuracy_bits()>80:break
        precision*=2
    else:raise AssertionError('insufficient precision')
    logvalue=value.log(); scale=logvalue/(k*k)
    result={'s':s,'K':k,'N':n,'power':power,'h':h,'degree':delta.degree(),
      'leading_coefficient_identity':True,'three_determinant_checks':True,
      'primitive_integer_coefficients':list(map(str,integers)),
      'positive_multiplier':str(Q(denominator,content)),
      'precision_bits':precision,'value_ball':value.str(35),
      'log_value_ball':logvalue.str(35),'log_value_over_K_squared_ball':scale.str(35),
      'log_value_over_K_squared_display':float(scale.mid()),
      'all_n_positivity':'proved from the positive Gram representation in the note, not from these samples'}
    if verbose: print(json.dumps({key:result[key] for key in ('s','K','N','power','h','log_value_over_K_squared_ball')}),flush=True)
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--quick',action='store_true');ap.add_argument('--grid',action='store_true');args=ap.parse_args()
    cases=[]
    if args.grid:
        for k in (16,24):
            for n in range(0,k,2):
                for power in ((1,) if n==0 else (1,2,4,6,8,10)):
                    cases.append(construct(9,k,n,power,False))
            best=min((c for c in cases if c['K']==k),key=lambda c:c['log_value_over_K_squared_display'])
            print(json.dumps({'K':k,'best_N':best['N'],'best_power':best['power'],'best_log_over_K2':best['log_value_over_K_squared_ball']}),flush=True)
    else:
        for s in (5,9):
            for k in ((4,8,12) if args.quick else (4,8,12,16,20,24,32,40)):
                n=3*k//40
                for power in ((6,) if s==5 else (6,10)):
                    cases.append(construct(s,k,n,power))
    out=M/'verification/positive-hankel-2026-09-29';out.mkdir(parents=True,exist_ok=True)
    payload={'status':'passed','cases':cases,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'boundary':'Exact construction and rigorous finite evaluations; no asymptotic decay or irrationality proof. Primitive normalization may outperform a proved universal normalization but has no proved asymptotic cost.'}
    (out/('grid.json' if args.grid else ('quick.json' if args.quick else 'certificate.json'))).write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__':main()
