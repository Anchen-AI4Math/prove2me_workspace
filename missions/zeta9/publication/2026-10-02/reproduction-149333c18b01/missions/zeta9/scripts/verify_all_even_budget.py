"""Rational log certificates for the budget using all even models."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from verify_vc_budget import log_interval
OUT=M/'verification/all-even-budget-2026-09-29'


def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    cone_path=M/'verification/exterior-cone-2026-09-29/certificate.json'
    models_path=M/'verification/all-even-models-2026-09-29/certificate.json'
    old_path=M/'verification/vc-budget-2026-09-29/certificate.json'
    cone=json.loads(cone_path.read_text()); models=json.loads(models_path.read_text())
    old=json.loads(old_path.read_text())
    assert all(x['status']=='passed' for x in (cone,models,old))
    assert models['source_sha256'][str(cone_path.relative_to(M))]==digest(cone_path)
    assert models['script_sha256']==digest(M/'scripts/verify_all_even_models.py')
    K=100
    finite=sum((1/Q(2*j)-1/(Q(2*j)+Q(2,7)) for j in range(1,K+1)),Q())
    even_tail_lo=log_interval(1+1/Q(7*(K+1)))[0]/2
    even_tail_hi=log_interval(1+1/Q(7*K))[1]/2
    log2=log_interval(Q(2))
    harmonic=sum((1/Q(j) for j in range(11,21)),Q())
    odd_tail=[7*(v-harmonic) for v in log2]
    unsigned=[finite+even_tail_lo+odd_tail[0],finite+even_tail_hi+odd_tail[1]]
    discount=sum((1/(Q(m)+Q(1,7))-1/(Q(m)+Q(1,3)) for m in range(1,20,2)),Q())
    assert discount==Q(old['discount_lower'])
    signed=[v-discount for v in unsigned]
    area_lo,area_hi=map(Q,cone['area_exponent_interval'])
    volume_hi=area_hi+(Q(19,2)+signed[1])/2
    margin=Q(2641,250)-volume_hi
    assert signed[1]<Q(116686,10**6)
    assert volume_hi<Q(10316887,10**6)
    assert margin>Q(247113,10**6)
    result=dict(status='passed',K=K,even_finite=str(finite),
                even_tail_interval=[str(even_tail_lo),str(even_tail_hi)],
                odd_tail_formula='7*(log(2)-H_20+H_10)',odd_tail_interval=list(map(str,odd_tail)),
                unsigned_envelope_interval=list(map(str,unsigned)),discount_lower=str(discount),
                signed_envelope_interval=list(map(str,signed)),area_exponent_interval=[str(area_lo),str(area_hi)],
                volume_upper=str(volume_hi),margin_lower=str(margin),
                display=dict(unsigned_lower=float(unsigned[0]),unsigned_upper=float(unsigned[1]),
                  signed_lower=float(signed[0]),signed_upper=float(signed[1]),
                  volume_upper=float(volume_hi),margin_lower=float(margin)),
                source_sha256={str(p.relative_to(M)):digest(p) for p in [cone_path,models_path,old_path]},
                script_sha256=digest(Path(__file__)),
                boundary='Intervals enclose the proved upper-envelope integral, not the actual arithmetic budget. No J or irrationality claim.')
    OUT.mkdir(exist_ok=True)
    (OUT/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='passed',**result['display']),indent=2))


if __name__=='__main__':main()
