"""Finite exact checks of the new candidate route, never a universal Lean proof.

Reuses only the explicitly identified Fraction polynomial helper SOURCE from
the earlier independent mathematical review. Its executable main is not run,
no old report is overwritten, and no prior instance/results are imported.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib,json,sys

OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
HELPER=TASK/'research/review_formal_transport_independent_2026_10_04.py'
EXPECTED='631a3135e4b48f5e90dce060649d7fa343099491040c0f20cc61eb0b77e89093'


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    assert sha(HELPER)==EXPECTED
    original=HELPER.read_text(encoding='utf-8-sig')
    prefix=original.split('\ninputs =')[0]
    assert '\nfor n in ' not in prefix and 'OUT.write_text' not in prefix
    (OUT/'finite-helper-source-prefix.py').write_text(prefix,encoding='utf-8',newline='\n')
    ns={'__file__':str(HELPER),'__name__':'finite_helper_source_only'}
    exec(compile(prefix,str(OUT/'finite-helper-source-prefix.py'),'exec'),ns)
    ns['OUT']=OUT/'unused-legacy-main-output.json'
    checks=ns['checks']
    instances=[]
    def check(name,condition,detail=None):
        checks.append(dict(name=name,pass_=bool(condition),detail=detail))
        assert condition,name
    X=ns['X'];power=ns['power'];jets=ns['jets'];weighted=ns['weighted']
    harmonic=ns['harmonic'];constant=ns['constant'];five=ns['five'];coeff=ns['coeff']
    for n in [1,2,3,6]:
        pairs=ns['solve_connection'](n)
        oldF=[five(jets(n,weighted(n,power(X,l)))) for l in range(5)]
        newF=[five(jets(n+2,weighted(n+2,power(X,r)))) for r in range(5)]
        gamma=[[coeff(p,l) for l in range(5)] for p,q in pairs]
        for r,(p,q) in enumerate(pairs):
            b=jets(n,weighted(n,p))
            a=jets(n+2,weighted(n+2,power(X,r)))
            qtop=ns['mul'](ns['scale'](ns['prod'](
                [[-F(i+2),F(1)] for i in range(n)]+
                [[F(n+i+1),F(1)] for i in range(n)]),F(factorial(n)**7)),
                ns['compose'](q,[F(0),F(n-1),F(1)]))
            shifted=ns['shift'](qtop,F(1))
            c=jets(n+1,shifted)
            check(f'n{n}_r{r}_actual_degrees',len(p)-1<=4 and len(q)-1<=9
                and len(shifted)-1<9*(n+2))
            check(f'n{n}_r{r}_old_PF_at_one_zero',ns['pf'](b,F(1))==ns['actual'](n,p,F(1))==0)
            check(f'n{n}_r{r}_true_shifted_Q_at_one_zero',ns['pf'](c,F(1))==
                ns['evaluate'](shifted,F(1))/ns['evaluate'](ns['pole'](n+1),F(1))**9==0)
            for s in range(1,10):
                def extold(j):return b[j-1][s-1] if 1<=j<=n+1 else F(0)
                def extc(j):return c[j][s-1] if j<=n+1 else F(0)
                def prevc(j):return c[j-1][s-1] if j>=1 else F(0)
                hnew=sum((a[j][s-1]*harmonic(s,j) for j in range(n+3)),F(0))
                hold=sum((b[j][s-1]*harmonic(s,j) for j in range(n+1)),F(0))
                oldpf=sum((b[j][s-1]/F(j+1)**s for j in range(n+1)),F(0))
                qpf=sum((c[j][s-1]/F(j+1)**s for j in range(n+2)),F(0))
                check(f'n{n}_r{r}_s{s}_three_exact_harmonic_extensions',
                    sum((extold(j)*harmonic(s,j) for j in range(n+3)),F(0))==
                        sum((b[j][s-1]*harmonic(s,j+1) for j in range(n+1)),F(0)) and
                    sum((extc(j)*harmonic(s,j) for j in range(n+3)),F(0))==
                        sum((c[j][s-1]*harmonic(s,j) for j in range(n+2)),F(0)) and
                    sum((prevc(j)*harmonic(s,j) for j in range(n+3)),F(0))==
                        sum((c[j][s-1]*harmonic(s,j+1) for j in range(n+2)),F(0)))
                check(f'n{n}_r{r}_s{s}_signed_harmonic_transport',hnew==hold+oldpf-qpf)
            check(f'n{n}_r{r}_B_correction_signs',constant(a)==constant(b)-ns['pf'](b,F(1))+ns['pf'](c,F(1)))
            check(f'n{n}_r{r}_actual_five_output_vector',five(a)==five(b))
            instances.append(dict(n=n,r=r,P=[str(v) for v in p],q=[str(v) for v in q],
                B_new=str(constant(a)),B_old=str(constant(b)),old_at_one=str(ns['pf'](b,F(1))),
                true_Q_at_two=str(ns['pf'](c,F(1)))))
        for r in range(5):
            for i in range(5):
                left=sum((gamma[r][l]*oldF[l][i] for l in range(5)),F(0))
                check(f'n{n}_actual_F_Gamma_F_r{r}_i{i}',newF[r][i]==left)
        wrong_right=[[sum((oldF[r][l]*gamma[l][i] for l in range(5)),F(0)) for i in range(5)] for r in range(5)]
        check(f'n{n}_negative_control_wrong_right_multiplication',wrong_right!=newF)
        print(f'Finite exact n={n}: all five chosen pairs, nine harmonic orders and 25 left-Gamma entries passed.',flush=True)
    check('negative_control_n0_weighted_boundary_not_zero',ns['actual'](0,[F(1)],F(1))==1)
    check('negative_control_n0_Q_degree_nine_not_proper',len(ns['power']([F(0),F(0),F(1)],9))-1==18)
    check('negative_control_n1_R2_not_zero',ns['actual'](1,[F(1)],F(2))==F(4,6**9)!=0)
    check('generic_empty_harmonic_sum',sum((),F(0))==0)
    assert sha(HELPER)==EXPECTED
    normalized=[dict(name=r['name'],passed=r.get('pass_',r.get('pass')),detail=r['detail']) for r in checks]
    assert all(r['passed'] for r in normalized)
    report=dict(status='FINITE_EXACT_PRECHECK_ONLY_NOT_UNIVERSAL_PROOF_OR_KERNEL_PASS',Lean_invocations=0,
        candidate_uncompiled=True,helper_source_reused=True,prior_instances_or_results_reused=False,
        old_helper_main_executed=False,old_files_modified=False,
        helper_source_sha256=EXPECTED,helper_prefix_sha256=sha(OUT/'finite-helper-source-prefix.py'),
        checks=normalized,check_count=len(checks),instances=instances,
        actual_matrix_entry_checks=100,script_sha256=sha(Path(__file__)))
    (OUT/'exact-precheck.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(dict(status=report['status'],checks=len(checks),sha256=sha(OUT/'exact-precheck.json'))))


if __name__=='__main__':main()
