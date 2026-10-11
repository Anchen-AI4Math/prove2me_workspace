"""Exact discount budgets using the reviewed odd/even trace theorems."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from verify_local_connection import P,fmpq,fmpq_mat,local_n_data,local_n_exponent

def sharp(y):
    m=y//1;t=y-m
    return -int(Q(1,7)<=t<Q(1,3)) if m%2 else int(t<Q(2,7))

def tail(y):
    t=y-2*(y//2)
    return Q(7) if t>=1 else 7+(3*t)//2+(7*t)//2-int(t>=Q(2,3))

def run():
    mean=sum((tail(Q(2*k+1,42)) for k in range(42)),Q(0))/42
    assert mean==Q(107,14)
    primitive=Q(0);values=[primitive]
    for k in range(42):
        primitive+=(tail(Q(2*k+1,42))-mean)/21;values.append(primitive)
    assert primitive==0 and min(values)==-Q(9,49) and max(values)==Q(9,14)
    conditional=[];nonnegative=[]
    for blocks in (8,10,11,12,14,20):
        area=Q(0)
        for k in range(21,2100):
            a,b=Q(k,21),Q(k+1,21);y=(a+b)/2
            area+=(sharp(y) if y<blocks+1 else tail(y))*(1/a-1/b)
        lo=area+mean/100-Q(9,490000)
        hi=area+mean/100+Q(9,140000)
        conditional.append({'blocks':blocks,'lower':str(lo),'upper':str(hi),
                            'lower_decimal':float(lo),'upper_decimal':float(hi)})
        if blocks==10:assert lo>Q(611,1000)
        if blocks==11:assert hi<Q(575,1000)
    for blocks in (11,14,20):
        area=Q(0)
        for k in range(21,2100):
            a,b=Q(k,21),Q(k+1,21);y=(a+b)/2
            area+=(max(0,sharp(y)) if y<blocks+1 else tail(y))*(1/a-1/b)
        hi=area+mean/100+Q(9,140000)
        lo=area+mean/100-Q(9,490000)
        nonnegative.append({'blocks':blocks,'lower':str(lo),'upper':str(hi),'upper_decimal':float(hi)})
        if blocks==14:assert hi<Q(605,1000)
        if blocks==20:assert hi<Q(463,1000)
    discounts=[]
    for mmax in (1,11,19):
        v=sum((1/(Q(m)+Q(1,7))-1/(Q(m)+Q(1,3)) for m in range(1,mmax+1,2)),Q(0))
        discounts.append({'odd_block_max':mmax,'liminf_U_over_n_lower_bound':str(v),'decimal':float(v)})
    assert discounts[0]['liminf_U_over_n_lower_bound']=='1/8'
    finite_even=sum((1/Q(m)-1/(Q(m)+Q(2,7)) for m in range(2,21,2)),Q(0))
    positive=finite_even+Q(1,3)
    discount=Q(discounts[-1]['liminf_U_over_n_lower_bound'])
    signed=positive-discount
    assert positive==Q(538676482493,1243484457600)<Q(434,1000)
    assert signed==Q(18357395198580260881,67333687347989462400)<Q(273,1000)
    proof_inputs={}
    for rel in ('research/first-block-joint-2026-09-29.md','research/even-block-sharpening-2026-09-29.md',
                'verification/odd-anchor-2026-09-29/certificate.json','verification/even-block-direction-2026-09-29/certificate.json'):
        proof_inputs[rel]=hashlib.sha256((M/rel).read_bytes()).hexdigest()
    odd=json.loads((M/'verification/odd-anchor-2026-09-29/certificate.json').read_text())['symbolic']
    even=json.loads((M/'verification/even-block-direction-2026-09-29/certificate.json').read_text())['models']
    assert sorted(x['m'] for x in odd)==list(range(1,20,2))
    assert sorted(x['m'] for x in even)==list(range(2,21,2))
    for item in odd:
        assert fmpq_mat([[fmpq(z) for z in row] for row in item['matrix']]).det()==fmpq(item['determinant'])!=0
    for item in even:
        assert fmpq_mat([[fmpq(z) for z in row] for row in item['low_matrix']]).det()==fmpq(item['determinant'])!=0
    baseline=M/'verification/block-budget-continuation-2026-09-29/certificate.json'
    cases=json.loads(baseline.read_text())['finite']['cases']
    counterexamples=[]
    for c in cases:
        proposed=11+sharp(Q(c['n'],c['p']))
        assert c['actual']<=proposed+c['exception_loss']
        if c['actual']>proposed:counterexamples.append({**c,'proposed_unqualified_bound':proposed})
    source=M/'verification/local-connection-2026-09-28/symbolic.json'
    rows=json.loads(source.read_text())['connection']
    entries=[[(P(list(map(int,e['numerator']))),P(list(map(int,e['denominator'])))) for e in row] for row in rows]
    sys.path.insert(0,str(M/'round6/scripts'))
    from independent_audit import independent_columns
    selected={116:[101],136:[101],204:[101],232:[101],300:[257],318:[101],430:[53]}
    F=fmpq_mat(independent_columns(2));direct=[]
    for n in range(2,431,2):
        if n in selected:
            data=local_n_data(F)
            for p in selected[n]:
                actual=local_n_exponent(data,p)
                direct.append({'n':n,'p':p,'N_valuation':actual,'pattern':11+sharp(Q(n,p))})
        if n<430:F=fmpq_mat([[fmpq(a(n),b(n)) for a,b in row] for row in entries])*F
    assert next(c for c in direct if c['n']==300)['N_valuation']==11
    assert next(c for c in direct if c['n']==116)['N_valuation']==10
    result={'status':'passed','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'input_sha256':{'connection':hashlib.sha256(source.read_bytes()).hexdigest(),
                            'existing_cases':hashlib.sha256(baseline.read_bytes()).hexdigest()},
            'new_tail':{'mean':str(mean),'primitive_min':str(min(values)),'primitive_max':str(max(values))},
            'proof_inputs_sha256':proof_inputs,'signed_integral_certificates':conditional,
            'nonnegative_integral_certificates':nonnegative,'discount_lower_bound_certificates':discounts,
            'constant_tail_budget':{'finite_even_integral':str(finite_even),'tail_bound':'1/3',
                                    'nonnegative_upper':str(positive),'nonnegative_upper_decimal':float(positive),
                                    'discount_lower':str(discount),'signed_upper':str(signed),
                                    'signed_upper_decimal':float(signed)},
            'finite':{'existing_case_count':len(cases),'unqualified_pattern_counterexamples':counterexamples,
                      'with_known_exception_loss_all_pass':True,'recomputed_cases':direct},
            'warning':'These bounds use the cited reviewed written trace theorems and fixed nonzero model certificates. Finite matrix cases are only implementation checks; no lattice-shape or irrationality claim is made.'}
    out=M/'verification/discount-direction-2026-09-29';out.mkdir(exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','constant_tail_budget':result['constant_tail_budget'],'discounts':discounts,
                      'counterexamples_without_exceptions':len(counterexamples),'direct':direct},indent=2))

if __name__=='__main__':run()
