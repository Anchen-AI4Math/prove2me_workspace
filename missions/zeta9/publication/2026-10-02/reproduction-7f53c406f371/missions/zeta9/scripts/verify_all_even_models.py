"""All even model determinants via a narrower actual exterior invariant cone."""
from pathlib import Path
import hashlib,json,sys
from fractions import Fraction
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from probe_exterior_cone import P,Q,Mat,V,VI,PAIRS,compound,connection
sys.path.insert(0,str(M/'round6/scripts'))
from independent_audit import independent_columns
OUT=M/'verification/all-even-models-2026-09-29'


def main():
    source=M/'verification/exterior-cone-2026-09-29/certificate.json'
    data=json.loads(source.read_text())
    assert data['connection_sha256']==hashlib.sha256((M/'verification/local-connection-2026-09-28/symbolic.json').read_bytes()).hexdigest()
    assert data['coordinate_matrix']==[[str(V[i,j]) for j in range(5)] for i in range(5)]
    T=[[P(list(map(int,p))) for p in row] for row in data['transformed_numerators']]
    N=22; q=10000
    shifted=[[p(P([N,1])) for p in row] for row in T]
    degree=max(p.degree() for row in shifted for p in row)
    coefficients=[[[int(p[k]) for k in range(degree+1)] for p in row] for row in shifted]
    lower=[q*coefficients[0][0][k]-sum(abs(coefficients[i][0][k]) for i in range(1,10))
           for k in range(degree+1)]
    margins=[[lower[k]-q*q*abs(coefficients[0][j][k])
              -q*sum(abs(coefficients[i][j][k]) for i in range(1,10))
              for k in range(degree+1)] for j in range(1,10)]
    assert all(x>0 for x in lower)
    assert all(x>=0 for row in margins for x in row)
    # The old exact scalar is positive for all n>=20, hence all n>=22.
    common=P(list(map(int,data['common_factor'])))
    det_at20=P(list(map(int,data['det_P_shifted_positive_coefficients'])))
    assert common(22)>0 and all(c>=0 for c in common(P([22,1])))
    assert det_at20(0)>0 and all(c>=0 for c in det_at20)
    direct_checks=[]
    for n in (22,24,42):
        Ci=connection(n).inv()
        G=Mat([[Ci[i,j]*Q((n+2)**(2*j),n**(2*i)) for j in range(5)] for i in range(5)])
        actual=-compound(VI*G*V)
        scale=Q(T[0][0](n))/actual[0,0]
        assert scale>0
        assert all(T[i][j](n)==scale*actual[i,j] for i in range(10) for j in range(10))
        direct_checks.append(n)
    inverse_exterior=compound(VI); target=PAIRS.index((3,4))
    restore=[inverse_exterior[i,target] for i in range(10)]
    dominance=abs(restore[0])-sum(abs(x) for x in restore[1:])/q
    assert restore[0]>0 and dominance>0
    oldpath=M/'verification/even-block-direction-2026-09-29/certificate.json'
    old={r['m']:Q(r['determinant']) for r in json.loads(oldpath.read_text())['models']}
    small=[]; initial=None
    for n in range(2,23,2):
        F=Mat(independent_columns(n)); inv=F.inv()
        delta=Mat([[F[i,j] for j in (1,2,3)] for i in range(3)]).det()
        minor=inv[0,3]*inv[4,4]-inv[0,4]*inv[4,3]
        assert delta==-F.det()*minor
        assert delta*((-1)**(n//2+1))>0
        if n<=20: assert delta==old[n]
        small.append(dict(m=n,delta=str(delta),inverse_minor_34=str(minor),jacobi_verified=True))
        if n==22:
            E=Mat([[inv[i,j]*n**(2*j) for j in range(5)] for i in (0,4)])*V
            z=[E[0,i]*E[1,j]-E[0,j]*E[1,i] for i,j in PAIRS]
            assert z[0]<0 and all(q*abs(x)<abs(z[0]) for x in z[1:])
            assert sum(z[i]*restore[i] for i in range(10))==minor*n**14
            initial=dict(n=n,ratios=[str(x/z[0]) for x in z],
                         first_coordinate_sign=-1,max_ratio=float(max(abs(x/z[0]) for x in z[1:])))
    from verify_vc_budget import log_interval
    logarithm=log_interval(Fraction(2))
    rational=sum((Fraction(1,j) for j in range(11,21)),Fraction(0))
    tail_bounds=[7*(v-rational) for v in logarithm]
    assert tail_bounds[1]<Fraction(170631,10**6)
    result=dict(status='passed',scope='Uniform cone coefficient certificate, not finite-m determinant extrapolation.',
                N=N,epsilon='1/10000',degree=degree,
                positive_lower_coefficients=list(map(str,lower)),
                cone_margin_coefficients=[list(map(str,row)) for row in margins],
                restore_column=list(map(str,restore)),restore_dominance=str(dominance),
                initial=initial,small_models=small,direct_connection_checks=direct_checks,
                sign_formula='sign Delta_m = (-1)^(m/2+1) for every even m>=2',
                fixed_direction_defect_tail=dict(formula='7*(log(2)-H_20+H_10)',
                   subtracted_rational=str(rational),interval=list(map(str,tail_bounds)),
                   strict_upper='0.170631'),
                source_sha256={str(p.relative_to(M)):hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in [source,oldpath,M/'scripts/probe_exterior_cone.py',
                                         M/'round6/scripts/independent_audit.py']},
                script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    OUT.mkdir(exist_ok=True)
    (OUT/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='passed',degree=degree,small_models=len(small),
                         initial_max_ratio=initial['max_ratio'],
                         restore_dominance=float(dominance),all_even_nonzero=True)))


if __name__=='__main__':main()
