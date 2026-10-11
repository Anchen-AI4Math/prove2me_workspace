"""Exact integration and rational logarithm bounds for the written VC proof.

This checks finite algebra/certificates, not the quantified mathematical proof.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

M = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def log_interval(x, count=48):
    """For 1 <= x <= 2, bound log(x) by a positive atanh series."""
    assert 1 <= x <= 2
    z = (x-1)/(x+1)
    lo = 2*sum((z**(2*j+1)/Q(2*j+1) for j in range(count)), Q())
    rem = 2*z**(2*count+1)/(Q(2*count+1)*(1-z*z))
    return lo, lo+rem


def main():
    source_records = []
    certificates = {}
    for name, script in [
        ('odd-anchor', 'verify_odd_anchor.py'),
        ('even-block-direction', 'verify_even_block_direction.py'),
        ('first-block-refinement', 'verify_first_block_refinement.py'),
        ('first-block-joint', 'verify_first_block_joint.py'),
        ('even-block-sharpening', 'verify_even_block_sharpening.py'),
    ]:
        path = M/'verification'/f'{name}-2026-09-29'/'certificate.json'
        data = json.loads(path.read_text(encoding='utf-8'))
        assert data['status'] == 'passed'
        assert data['script_sha256'] == digest(M/'scripts'/script)
        certificates[name] = data
        source_records.append({'path': str(path.relative_to(M)), 'sha256': digest(path),
                               'script': script, 'script_sha256': data['script_sha256']})
    odd = certificates['odd-anchor']['symbolic']
    even = certificates['even-block-direction']['models']
    assert [x['m'] for x in odd] == list(range(1,20,2))
    assert [x['m'] for x in even] == list(range(2,21,2))
    assert all(Q(x['determinant']) != 0 for x in odd+even)
    # Relink certificates to their actual model and connection inputs.
    connection = M/'verification/local-connection-2026-09-28/symbolic.json'
    joint = certificates['first-block-joint']['real_matrix_audit']
    assert joint['model_sha256'] == source_records[0]['sha256']
    assert joint['connection_sha256'] == digest(connection)
    assert certificates['even-block-sharpening']['finite']['source_sha256'] == digest(connection)

    positive = [{'m': m, 'integral': str(1/Q(m)-1/(Q(m)+Q(2,7)))}
                for m in range(2,21,2)]
    discounts = [{'m': m, 'integral': str(1/(Q(m)+Q(1,7))-1/(Q(m)+Q(1,3)))}
                 for m in range(1,20,2)]
    finite = sum((Q(x['integral']) for x in positive), Q())
    discount = sum((Q(x['integral']) for x in discounts), Q())
    unsigned = finite+Q(7,21)
    signed = unsigned-discount
    assert unsigned == Q(538676482493,1243484457600)
    assert signed == Q(18357395198580260881,67333687347989462400)
    assert unsigned < Q(433200,1000000) and signed < Q(272634,1000000)

    # C = 2^31 * x, 1 < x < 2; certify the original VC threshold.
    C = 3711015000
    l2, u2 = log_interval(Q(2))
    lx, ux = log_interval(Q(C,2**31))
    log_lo, log_hi = 31*l2+lx, 31*u2+ux
    tau = Q(2641,250)
    threshold_lo = 2*tau-log_hi/2-Q(19,2)
    threshold_hi = 2*tau-log_lo/2-Q(19,2)
    assert unsigned < threshold_lo and threshold_lo > Q(610714,1000000)
    arithmetic_unsigned = (Q(19,2)+unsigned)/2
    arithmetic_signed = (Q(19,2)+signed)/2
    volume_upper = log_hi/4+arithmetic_signed
    assert volume_upper < tau-Q(169,1000)
    result = {
        'status': 'passed', 'sources': source_records,
        'connection_sha256': digest(connection),
        'positive_blocks': positive, 'discount_blocks': discounts,
        'finite_positive': str(finite), 'tail': '1/3',
        'unsigned_VC_upper': str(unsigned), 'discount_lower': str(discount),
        'signed_budget_upper': str(signed),
        'threshold_interval': [str(threshold_lo), str(threshold_hi)],
        'arithmetic_rate_unsigned_upper': str(arithmetic_unsigned),
        'arithmetic_rate_signed_upper': str(arithmetic_signed),
        'volume_rate_upper': str(volume_upper), 'tau': str(tau),
        'display': {k: float(v) for k,v in {
            'unsigned': unsigned, 'signed': signed, 'discount': discount,
            'threshold_lower': threshold_lo, 'threshold_upper': threshold_hi,
            'arithmetic_rate_signed_upper': arithmetic_signed,
            'volume_rate_upper': volume_upper, 'volume_margin_lower': tau-volume_upper,
        }.items()},
        'script_sha256': digest(Path(__file__)),
        'boundary': 'Checks exact arithmetic and linked finite certificates; the all-n proof is in vc-closure-2026-09-29.md. S and irrationality remain open; no Lean verification.',
    }
    out = M/'verification/vc-budget-2026-09-29'
    out.mkdir(parents=True, exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status': result['status'], **result['display']},indent=2))


if __name__ == '__main__':
    main()
