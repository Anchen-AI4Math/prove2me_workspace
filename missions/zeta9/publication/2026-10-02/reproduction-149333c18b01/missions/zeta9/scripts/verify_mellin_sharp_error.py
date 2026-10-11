"""Exact finite checks for the written all-degree Mellin error sandwich."""
from pathlib import Path
import sys, math, json, hashlib
M = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(M/'scripts'))
from probe_positive_hankel import Q, P, Mat, arb, ctx


def kernel(d,b):
    return 8*math.comb(d+8,8)*math.comb(d+b+8,8)


def beta(a,b):
    return Q(math.factorial(a)*math.factorial(b),math.factorial(a+b+1))


def integral(poly,b):
    return sum((c*beta(i+b,7) for i,c in enumerate(poly)),Q(0))


def jacobi(k,b):
    # Rodrigues is implemented literally, with exact division.
    x=P([0,1])
    num=x**(k+b)*(1-x)**(k+7)
    for _ in range(k): num=num.derivative()
    quo,rem=divmod(num,x**b*(1-x)**7)
    assert not rem
    return quo*Q((-1)**k,math.factorial(k))


def check_kernel(d,b):
    total=P([0]); diagonal=Q(0)
    for k in range(d+1):
        j=jacobi(k,b)
        norm=Q(math.factorial(k+7)*math.factorial(k+b),
               (2*k+b+8)*math.factorial(k)*math.factorial(k+b+7))
        assert j.degree()==k and j(1)==math.comb(k+7,7)
        assert integral(j*j,b)==norm
        for r in range(k): assert integral(j*P([0]*r+[1]),b)==0
        diagonal+=j(1)**2/norm
        total+=j*j(1)/norm
    assert diagonal==kernel(d,b)
    q=total/diagonal
    assert q(1)==1 and integral(q*q,b)==1/diagonal


def rational_approx(shift,d):
    H=[Q(0)]
    for k in range(1,2*(shift+d)+1): H.append(H[-1]+Q(1,k**9))
    h0=H[2*shift]
    if d==0: return h0
    b=Mat([[h0-H[2*shift+i]] for i in range(1,d+1)])
    C=Mat([[-H[2*shift+i+j]+H[2*shift+i]+H[2*shift+j]-h0
            for j in range(1,d+1)] for i in range(1,d+1)])
    assert C.det()>0
    return h0+(b.transpose()*C.inv()*b)[0,0]


def ab(q):
    return arb(int(q.numer()))/int(q.denom())


def main():
    for b in (0,1,2,4,8,16):
        for d in range(7): check_kernel(d,b)
    rows=[]
    for shift in (0,1,2,4,8,24):
        for d in (2,3,4,6,8,10,12):
            q=rational_approx(shift,d)
            lo=Q(1,math.factorial(8)*kernel(d,2*shift))
            r=max(0,2-shift)
            hi=Q(1,math.factorial(8)*kernel(d-r,2*(shift+r)-4))
            ctx.prec=max(512,int(q.denom()).bit_length()+128)
            eps=arb(9).zeta()-ab(q)
            assert eps>ab(lo) and eps<ab(hi)
            asym=Q(5040,d**8*(d+2*shift)**8)
            rows.append({'M':shift,'D':d,'q_numerator':str(q.numer()),
              'primitive_denominator':str(q.denom()),'error_ball':eps.str(30),
              'lower':str(lo),'upper':str(hi),
              'lower_over_asymptotic':str(lo/asym),'upper_over_asymptotic':str(hi/asym),
              'strict_ball_sandwich':True})
    out=M/'verification/mellin-sharp-error-2026-09-30'
    out.mkdir(parents=True,exist_ok=True)
    result={'status':'PASS','jacobi_kernel_checks':42,'rational_approximation_cases':rows,
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'boundary':'Finite checks supplement the written all-parameter proof; no denominator asymptotic or irrationality claim.'}
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':result['status'],'jacobi_checks':42,'sandwich_cases':len(rows)}))


if __name__=='__main__': main()
