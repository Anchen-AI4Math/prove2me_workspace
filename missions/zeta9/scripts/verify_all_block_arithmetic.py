"""All-block arithmetic: rational series bounds and linked model certificates."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from verify_vc_budget import log_interval
sys.set_int_max_str_digits(0)
OUT=M/'verification/all-block-arithmetic-2026-09-29'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def log_positive(x):
    power=0
    while x>2: x/=2; power+=1
    while x<1: x*=2; power-=1
    lo,hi=log_interval(x); l2,u2=log_interval(Q(2))
    return (lo+power*l2,hi+power*u2) if power>=0 else (lo+power*u2,hi+power*l2)


def main():
    paths={
      'even':M/'verification/all-even-models-2026-09-29/certificate.json',
      'odd':M/'verification/odd-model-connection-2026-09-29/all-odd-models.json',
      'odd_connection':M/'verification/odd-model-connection-2026-09-29/symbolic.json',
      'cone':M/'verification/exterior-cone-2026-09-29/certificate.json',
      'odd_local':M/'verification/first-block-joint-2026-09-29/certificate.json',
      'even_local':M/'verification/even-block-sharpening-2026-09-29/certificate.json',
    }
    data={k:json.loads(p.read_text()) for k,p in paths.items()}
    assert all(v['status']=='passed' for v in data.values())
    for k,script in [('even','verify_all_even_models.py'),('odd','verify_all_odd_models.py'),
                     ('odd_connection','verify_odd_model_connection.py'),
                     ('cone','verify_exterior_cone.py')]:
        assert data[k]['script_sha256']==sha(M/'scripts'/script)
    assert data['odd']['connection_sha256']==sha(paths['odd_connection'])
    assert data['even']['source_sha256'][str(paths['cone'].relative_to(M))]==sha(paths['cone'])
    K=1000
    sfinite=sum((1/Q(2*k)-1/(Q(2*k)+Q(2,7)) for k in range(1,K+1)),Q())
    stail=[log_interval(1+1/Q(7*(K+1)))[0]/2,
           log_interval(1+1/Q(7*K))[1]/2]
    dfinite=sum((1/(Q(2*j)+Q(8,7))-1/(Q(2*j)+Q(4,3)) for j in range(K)),Q())
    def dtail_at(x): return log_interval((2*Q(x)+Q(4,3))/(2*Q(x)+Q(8,7)))
    dtail=[dtail_at(K)[0]/2,dtail_at(K-1)[1]/2]
    sint=[sfinite+v for v in stail]; dint=[dfinite+v for v in dtail]
    signed=[sint[0]-dint[1],sint[1]-dint[0]]
    gamma=list(map(Q,data['cone']['area_exponent_interval']))
    volume=gamma[1]+(Q(19,2)+signed[1])/2
    margin=Q(2641,250)-volume
    alpha_lo=log_positive(Q(data['cone']['eigenvalue_intervals']['A'][0]))[0]/2
    rational_sigma_lo=alpha_lo-volume
    assert sint[1]<Q(10661775,10**8) and dint[0]>Q(16526813,10**8)
    assert signed[1]<-Q(5865038,10**8)
    assert volume<Q(1022921877,10**8)
    assert margin>Q(33478123,10**8)
    assert rational_sigma_lo>Q(33493507,10**8)
    result=dict(status='passed',K=K,
      even_finite=str(sfinite),even_tail_interval=list(map(str,stail)),
      odd_discount_finite=str(dfinite),odd_discount_tail_interval=list(map(str,dtail)),
      unsigned_envelope_interval=list(map(str,sint)),discount_envelope_interval=list(map(str,dint)),
      signed_envelope_interval=list(map(str,signed)),gamma_interval=list(map(str,gamma)),
      arithmetic_h_rate_upper=str(Q(19,2)+signed[1]),volume_upper=str(volume),margin_lower=str(margin),
      rational_branch_sigma_lower=str(rational_sigma_lo),
      display=dict(unsigned_lower=float(sint[0]),unsigned_upper=float(sint[1]),
        discount_lower=float(dint[0]),discount_upper=float(dint[1]),
        signed_lower=float(signed[0]),signed_upper=float(signed[1]),
        h_rate_upper=float(Q(19,2)+signed[1]),volume_upper=float(volume),
        margin_lower=float(margin),rational_branch_sigma_lower=float(rational_sigma_lo)),
      fixed_direction_deficit='For every fixed integer (b,a) with a nonzero, log(h_n/q_n)=o(n).',
      source_sha256={str(p.relative_to(M)):sha(p) for p in paths.values()},
      script_sha256=sha(Path(__file__)),
      boundary='Intervals bound an upper-envelope integral, not the actual arithmetic rate. Rational-branch conclusions are conditional; no J or irrationality proof.')
    OUT.mkdir(exist_ok=True)
    (OUT/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='passed',**result['display']),indent=2))


if __name__=='__main__':main()
