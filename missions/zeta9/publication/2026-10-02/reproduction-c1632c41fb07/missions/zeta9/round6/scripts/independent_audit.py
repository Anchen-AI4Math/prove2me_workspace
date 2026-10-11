"""Independent 5x5 inverse, integral lifts, raw products and interval review."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT/'tmp/zeta7/exact_packages'))
sys.path.insert(0, str(ROOT/'missions/zeta9/round5/scripts'))
sys.set_int_max_str_digits(0)
from flint import arb, ctx, fmpq, fmpq_mat, fmpz_mat
from independent_round5 import product_form, compose_w, direct_sum_audit, iv
from audit_archives import saturation_by_minors
from positivity import sturm_open_ray

OUT = ROOT/'missions/zeta9/round6/verification'


def Q(x):
    return fmpq(int(x[0]),int(x[1]))


def ints(rows):
    return [list(map(int,row)) for row in rows]


def qs(rows):
    return [[Q(x) for x in row] for row in rows]


def read(path):
    with gzip.open(path,'rt',encoding='utf-8') as stream:
        return json.load(stream)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def old_interval(v):
    unit=fmpq(10)**int(v['exp'])
    return arb(int(v['mid'])*unit,arb(int(v['rad'])*unit).upper())


def independent_columns(n):
    base=product_form(9,n,[(n,1)],[1])
    H={s:[fmpq(0)] for s in range(1,10)}
    for s in H:
        for j in range(1,n+1):
            H[s].append(H[s][-1]+fmpq(1,j**s))
    columns=[]
    for r in range(5):
        poles={s:[] for s in range(1,10)}
        for j in range(n+1):
            local=compose_w([0]*r+[1],-j,n,8)
            for s in range(1,10):
                poles[s].append(sum((local[h]*base['pole_coeffs'][s+h][j] for h in range(10-s)),fmpq(0)))
        sums={s:sum(poles[s],fmpq(0)) for s in poles}
        assert sums[1]==0 and all(sums[s]==0 for s in (2,4,6,8))
        B=-sum((poles[s][j]*H[s][j] for s in poles for j in range(n+1)),fmpq(0))
        columns.append([B]+[sums[s] for s in (3,5,7,9)])
    return columns


def canonical(p):
    if p[1]<0 or (p[1]==0 and p[0]<0):
        return [-x for x in p]
    return p


def audit(n, products=True):
    started=time.monotonic()
    ip=OUT/f'search-input-n{n}.json.gz'
    op=OUT/f'search-n{n}.json.gz'
    inp, output=read(ip),read(op)
    assert output['input_sha256']==sha(ip)
    columns=qs(inp['raw_monomial_vectors'])
    if products:
        assert independent_columns(n)==columns
    Ffull=fmpq_mat([[columns[r][k] for r in range(5)] for k in range(5)])
    inverse=Ffull.inv()
    expected=[[inverse[j,i] for j in range(5)] for i in (0,4)]
    E=qs(output['inverse_map_E_rows_qB_qA'])
    assert E==expected
    K=ints(inp['integer_W_basis_K_rows'])
    saturation=saturation_by_minors(K,5)
    assert fmpq_mat(K)*Ffull.transpose()==fmpq_mat([[Q(inp['raw_image_F_rows_B_A'][i][0]),0,0,0,Q(inp['raw_image_F_rows_B_A'][i][1])] for i in range(2)])
    D=int(inp['common_denominator_Q'])
    J=ints(inp['J_rows_B_A'])
    rawF=qs(inp['raw_image_F_rows_B_A'])
    assert all(rawF[i][j]*D==J[i][j] for i in range(2) for j in range(2))
    det=int(fmpz_mat(J).det())
    s1=math.gcd(*(x for row in J for x in row))
    assert s1==int(inp['SNF_s1']) and abs(det)//s1==int(inp['SNF_s2'])
    common=int(output['integer_weighted_E_common_D'])
    weights=[n**(2*r) for r in range(5)]
    integral=ints(output['integer_weighted_E_rows'])
    assert all(E[i][r]*common*weights[r]==integral[i][r] for i in range(2) for r in range(5))
    transform=fmpz_mat(ints(output['LLL_transform_unimodular_T']))
    assert abs(int(transform.det()))==1
    assert transform*fmpz_mat(integral)==fmpz_mat(ints(output['LLL_reduced_integer_weighted_rows']))
    T=ints(output['LLL_transform_unimodular_T'])
    all_candidates={}
    for x,y in itertools.product(range(-4,5),repeat=2):
        if math.gcd(x,y)!=1:
            continue
        pair=canonical([x*T[0][j]+y*T[1][j] for j in range(2)])
        poly=[pair[0]*E[0][r]+pair[1]*E[1][r] for r in range(5)]
        l1=sum((abs(poly[r])*weights[r] for r in range(5)),fmpq(0))
        sq=sum(((poly[r]*weights[r])**2 for r in range(5)),fmpq(0))
        all_candidates[tuple(pair)]=(l1,sq,max(map(abs,pair)),pair)
    ordered=sorted(v for k,v in all_candidates.items() if k[1])[:8]
    assert [x[3] for x in ordered]==[list(map(int,c['primitive_pair_B_A'])) for c in output['selected']]
    rows=[]
    best=None
    for index,c in enumerate(output['selected']):
        B,A=map(int,c['primitive_pair_B_A'])
        assert A>0 and math.gcd(A,B)==1
        W=list(map(int,c['integer_W']))
        z=list(map(int,c['integer_K_coordinates']))
        assert math.gcd(*W)==math.gcd(*z)==1
        M=Q(c['primitive_multiplier_M'])
        assert [sum(z[i]*K[i][r] for i in range(2)) for r in range(5)]==W
        q=[B*E[0][r]+A*E[1][r] for r in range(5)]
        assert [M*x for x in W]==q==[Q(x) for x in c['inverse_preimage_qE']]
        raw=[sum((W[r]*columns[r][k] for r in range(5)),fmpq(0)) for k in range(5)]
        assert raw==[B/M,fmpq(0),fmpq(0),fmpq(0),A/M]
        image=[sum(z[i]*J[i][j] for i in range(2)) for j in range(2)]
        assert image==[D*B/M,D*A/M]
        content=math.gcd(*image)
        assert M==fmpq(D,content)
        assert content % s1==0 and (abs(det)//s1**2)%(content//s1)==0
        norm=sum((abs(q[r])*weights[r] for r in range(5)),fmpq(0))
        assert norm==Q(c['qE_weighted_l1'])
        sturm=sturm_open_ray(W,(n+1)*(2*n+1))
        bits=max(2048,2*max(abs(A).bit_length(),abs(B).bit_length())+256)
        with ctx.workprec(bits):
            value=arb(A)*(arb(9).zeta()+arb(fmpq(B,A)))
            assert value.overlaps(old_interval(c['arb']['value_interval']))
            sign=1 if value.lower()>0 else (-1 if value.upper()<0 else 0)
            assert sign!=0 and sign==int(c['arb']['sign'])
            if sturm['raw_L_sign_if_certified'] is not None:
                assert sign==sturm['raw_L_sign_if_certified']
            score=abs(value).log()/n
            row=dict(selected_index=index,primitive_pair_B_A=[str(B),str(A)],
                     independent_value_interval=iv(value),log_abs_per_n=iv(score),
                     normalized_weighted_l1_log_per_n=iv(arb(norm).log()/n),
                     nonzero=True,below_one=bool(abs(value).upper()<1),
                     sturm=sturm,primitive_pair_sha256=hashlib.sha256(f'{B},{A}'.encode()).hexdigest())
            rows.append(row)
            if best is None or float(score)<best[0]:
                best=(float(score),index,W,raw,bits)
    _,ix,W,raw,bits=best
    form=dict(p=9,n=n,layers=[(n,1)],W=W,raw_vector=raw,zeta_orders=[3,5,7,9])
    direct=direct_sum_audit(form,T=max(256,8*n),bits=max(bits,4096))
    assert direct['direct_excludes_zero']
    record=dict(status='passed',n=n,input_sha256=sha(ip),search_sha256=sha(op),
                full_five_by_five_inverse_equal=True,independent_product_columns=5 if products else 0,
                saturated_kernel=saturation,selection_reproduced_without_zeta=True,
                candidate_count=len(rows),candidates=rows,direct_best_selected_index=ix,
                direct=direct,seconds=time.monotonic()-started,
                script_sha256=sha(Path(__file__)))
    (OUT/f'independent-n{n}.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='passed',n=n,candidates=len(rows),seconds=record['seconds'],
                         best_log_abs_per_n=best[0],positive_or_negative_W=sum(r['sturm']['raw_L_sign_if_certified'] is not None for r in rows))),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--n',type=int,required=True)
    parser.add_argument('--skip-products',action='store_true')
    args=parser.parse_args()
    audit(args.n,products=not args.skip_products)
