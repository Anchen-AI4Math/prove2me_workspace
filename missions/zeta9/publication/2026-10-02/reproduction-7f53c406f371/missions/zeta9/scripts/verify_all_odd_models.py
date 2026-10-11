"""All positive odd local models: actual odd connection and rational exterior cone."""
from pathlib import Path
import sys,json,math,hashlib
MISSION=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(MISSION/'scripts'))
from probe_exterior_cone import P,Q,Mat,V,VI,PAIRS,compound
from verify_exterior_cone import clear
from verify_local_connection import determinant
from verify_odd_model_connection import raw_matrix

def main():
    source=MISSION/'verification/odd-model-connection-2026-09-29/symbolic.json'
    data=json.loads(source.read_text())
    ENT=[[(P(list(map(int,e['numerator']))),P(list(map(int,e['denominator'])))) for e in row] for row in data['connection']]
    x=P([0,1]);den=(x+1)**10*(x+2)**8
    A=[]
    for row in ENT:
        line=[]
        for a,b in row:
            value,remainder=divmod(a*den,b);assert not remainder;line.append(value)
        A.append(line)
    comps=[tuple(k for k in range(5) if k not in I) for I in PAIRS]
    nums=[]
    for I,Ic in zip(PAIRS,comps):
        row=[]
        for J,Jc in zip(PAIRS,comps):
            p=determinant([[A[j][i] for i in Ic] for j in Jc])
            p*=(-1)**(sum(I)+sum(J))*x**(14-2*sum(I))*(x+2)**(2*sum(J))
            row.append(p)
        nums.append(row)
    common=P([])
    for row in nums:
        for p in row:common=common.gcd(p)
    if common.leading_coefficient()<0:common=-common
    for i in range(10):
        for j in range(10):
            nums[i][j],r=divmod(nums[i][j],common);assert not r
    L,dl=clear(compound(VI));R,dr=clear(compound(V))
    left=[[sum((L[i][k]*nums[k][j] for k in range(10)),P([])) for j in range(10)] for i in range(10)]
    T=[[-sum((left[i][k]*R[k][j] for k in range(10)),P([])) for j in range(10)] for i in range(10)]
    content=math.gcd(*(int(c) for row in T for p in row for c in p))
    T=[[p//content for p in row] for row in T]
    N=51;q=10000
    detP=determinant(A)
    for p in (common,detP):
        assert p(N)>0 and all(c>=0 for c in p(P([N,1])))
    # Tpoly=s(n)*[-compound(V^-1 G_n V)] with
    # s=dl*dr*n^14*detP/(content*common*den^2)>0 for all n>=N.
    shifted=[[p(P([N,1])) for p in row] for row in T]
    degree=max(p.degree() for row in shifted for p in row)
    coeff=[[[int(p[k]) for k in range(degree+1)] for p in row] for row in shifted]
    lower=[q*coeff[0][0][k]-sum(abs(coeff[i][0][k]) for i in range(1,10)) for k in range(degree+1)]
    margins=[[lower[k]-q*q*abs(coeff[0][j][k])-q*sum(abs(coeff[i][j][k]) for i in range(1,10))
              for k in range(degree+1)] for j in range(1,10)]
    assert all(c>0 for c in lower)
    assert all(c>=0 for row in margins for c in row)
    print('PASS all-real-n>=51 odd invariant cone, degree',degree,flush=True)
    direct=[]
    for nn in (51,53,101):
        C=Mat([[Q(a(nn),b(nn)) for a,b in row] for row in ENT]);Ci=C.inv()
        G=Mat([[Ci[i,j]*Q((nn+2)**(2*j),nn**(2*i)) for j in range(5)] for i in range(5)])
        actual=-compound(VI*G*V)
        scale=Q(dl*dr*nn**14*detP(nn),content*common(nn)*den(nn)**2)
        assert scale>0
        assert all(T[i][j](nn)==scale*actual[i,j] for i in range(10) for j in range(10))
        direct.append(nn)
    restore_matrix=compound(VI);target=PAIRS.index((3,4))
    restore=[restore_matrix[i,target] for i in range(10)]
    dominance=restore[0]-sum(abs(v) for v in restore[1:])/q
    assert restore[0]>0 and dominance>0
    prefix=[];initial=None
    oldpath=MISSION/'verification/odd-anchor-2026-09-29/certificate.json'
    old=json.loads(oldpath.read_text())
    old_models={int(row['m']):row for row in old['symbolic']}
    for nn in range(1,N+1,2):
        F=raw_matrix(nn);Fi=F.inv()
        delta=Mat([[F[i,j] for j in (1,2,3)] for i in range(3)]).det()
        inverse_minor=Fi[0,3]*Fi[4,4]-Fi[0,4]*Fi[4,3]
        assert delta==-F.det()*inverse_minor
        assert F.det()>0 and (-1)**((nn+1)//2)*delta>0
        model=Q(512,math.factorial(nn)**21)*delta
        if nn in old_models:assert model==Q(old_models[nn]['determinant'])
        prefix.append({'m':nn,'det_Ftilde':str(F.det()),'delta':str(delta),'det_M':str(model),'jacobi_verified':True})
        if nn==N:
            E=Mat([[Fi[i,j]*nn**(2*j) for j in range(5)] for i in (0,4)])*V
            z=[E[0,i]*E[1,j]-E[0,j]*E[1,i] for i,j in PAIRS]
            assert z[0]<0 and all(q*abs(a)<-z[0] for a in z[1:])
            assert sum(z[i]*restore[i] for i in range(10))==nn**14*inverse_minor
            initial={'n':nn,'first_coordinate_sign':-1,'ratios':[str(a/z[0]) for a in z],
                     'max_ratio':str(max(abs(a/z[0]) for a in z[1:]))}
    # Cross-check the 2 and triangular 4^r normalizations against old direct M_m.
    normalization=[]
    for nn in (1,3,5):
        F=raw_matrix(nn)
        triangular=Mat([[Q(math.comb(r,j)*4**j*nn**(2*(r-j))) if j<=r else Q(0) for j in range(3)] for r in range(3)])
        low=Mat([[F[i,j] for j in (1,2,3)] for i in range(3)])
        model=(2/Q(math.factorial(nn)**7))*(triangular*low).transpose()
        expected=Q(512,math.factorial(nn)**21)*low.det()
        assert model.det()==expected
        assert [[str(model[i,j]) for j in range(3)] for i in range(3)]==old_models[nn]['matrix']
        normalization.append({'m':nn,'det_M':str(expected),'matrix':[[str(model[i,j]) for j in range(3)] for i in range(3)]})
    result={'status':'passed','N':N,'epsilon':'1/10000','degree':degree,
        'all_odd_models_nonzero':True,'sign_formula':'sign(det M_m)=(-1)^((m+1)/2)',
        'positive_lower_coefficients':list(map(str,lower)),
        'cone_margin_coefficients':[list(map(str,row)) for row in margins],
        'transformed_numerators':[[[str(c) for c in p] for p in row] for row in T],
        'common_factor':[str(c) for c in common],
        'det_P_coefficients':[str(c) for c in detP],
        'scalar_constants':{'d_left':str(dl),'d_right':str(dr),'content':str(content)},
        'restore_column':list(map(str,restore)),'restore_dominance':str(dominance),
        'initial':initial,'small_models':prefix,'direct_connection_checks':direct,
        'normalization_checks':normalization,
        'old_model_certificate_sha256':hashlib.sha256(oldpath.read_bytes()).hexdigest(),
        'connection_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out=MISSION/'verification/odd-model-connection-2026-09-29'
    (out/'all-odd-models.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS all positive odd M_m nonzero; 26 exact initial/prefix cases and all-parameter cone.',flush=True)

if __name__=='__main__':main()
