"""Publish compiled analytic children, preserving exact signatures and source."""
import hashlib
import json
import sys
from pathlib import Path
from platform import api, save, p2m

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
manifest=json.loads((HERE/'verification/local-proof-manifest.json').read_text(encoding='utf-8'))
statepath=HERE/'verification/support-nodes.json'
state=json.loads(statepath.read_text(encoding='utf-8')) if statepath.exists() else {}
metadata={
 'quartic_geometry':('Quartic derivative and tangent geometry',
   'For every real t in the closed interval [0,1/2], the exact expansion-232 quartic has derivative strictly between 0 and 9, and its tangent at the fixed rational point 0.17200068185091493 lies below it. Both endpoints are included. The explicit polynomial and derivative are supplied by the shared analytic definitions.',
   'The positive coefficients bound the derivative by its value at the right endpoint. Subtracting the tangent factors as (t-u)^2 times a polynomial with nonnegative coefficients for t,u>=0, establishing the tangent bound.'),
 'log_coefficients':('Exact logarithmic certificate for four switch coefficients',
   'The real natural logarithm of 2 lies between 0.693147180559945 and 0.693147180559946. The four exact rational quartic coefficients obey their respective derivative-series bounds: a1 log(2)<log(231), 2 a2 log(2)<=1+1/231, 3 a3 log(2)<=(1-1/231^2)/2, and 4 a4 log(2)<=(1+1/231^3)/3. These are unconditional exact real inequalities.',
   'Finite atanh Taylor sums and rigorous remainder bounds enclose log(2). Range reduction log(231)=7 log(2)+log(231/128) gives the linear coefficient bound using a second rational atanh point. The remaining three coefficient comparisons follow from the proved log(2) upper bound and exact rational arithmetic.'),
 'tangent_log_bounds':('Exact logarithmic bounds for the entropy supporting line',
   'For the exact rational tangent point u=0.17200068185091493, the two real quantities -log(1-u)/log(2) and [-log(1-u)-log(u)]/[2 log(2)] are strictly below 0.272298515211 and 1.40590616299 respectively. These are the values at 0 and 1/2 of the binary-entropy tangent line, with all logarithms natural.',
   'Positive finite atanh sums bound log(2(1-u)) and log(8u) from below. Range reduction expresses these as log(2)+log(1-u) and 3 log(2)+log(u). The already proved log(2) upper bound and two exact rational comparisons give the two strict endpoint bounds.'),
 'cleared_switch_equivalence':('Integer quartic comparison is exactly the analytic threshold test',
   'For arbitrary natural J,s,j,q with J>0, s>0 and j<J, the published clearedSwitch integer comparison holds if and only if P(q/((J-j)s)) is at least (v+j/J)/(1-j/J), with v=159243801/500000000 and the exact quartic P. There is no restriction on q beyond being a natural number. The positive-depth hypothesis identifies real subtraction with truncated natural subtraction and makes all cleared denominators positive.',
   'Rewrite the threshold as (159243801 J+500000000 j)/(500000000(J-j)) and the quartic as its integer degree-four numerator divided by 100000000 r^4, where r=(J-j)s. Both denominators are positive. Cross multiplication therefore preserves the inequality. The natural-to-real cast of the resulting comparison is precisely the published integer predicate. No approximation, floating-point step or logarithm oracle is involved.'),
 'high_precision_logs':('Six logarithmic intervals with exact 22-digit rational endpoints',
   'Certifies both endpoints of six exact rational intervals for the natural logarithms of 2, 29/16, 232/231, 464/463, 32 theta, and 2(1-theta), where theta=0.040409899 is the published fixed parameter. Every interval has denominator 10^22 and width 10^(-22). The endpoints are exactly those displayed in the formal statement; no rounding or numerical oracle is a hypothesis.',
   'For each positive rational argument y, use z=(y-1)/(y+1), which lies in [0,1). Mathlib bounds log(y) between a finite positive atanh sum and that sum plus a rigorous geometric remainder. Exact rational arithmetic places these endpoints inside the displayed rational interval. The term counts are 26, 24, 5, 5, 18, and 26 respectively. These bounds support the E, kappa, initial-entropy and cost certificates.'),
 'encoding_parameter_bounds':('Strict expansion-232 encoding and collision intervals',
   'The fixed expansion-232 entropy constants obey 4.648781151243719 < E(232) < 4.648781151243720 and 0.001557987216578 < kappa(232) < 0.001557987216579, with E and kappa defined in the shared analytic bundle. All four displayed endpoints are exact rationals with denominator 10^15.',
   'Expand binary entropy and range-reduce log(232) to 7 log(2)+log(29/16). This gives E=(7 log(2)+log(29/16)+231 log(232/231))/(2 log(2)) and kappa=(463 log(464/463)-231 log(232/231))/log(2). The published 22-digit logarithm intervals and exact sign-directed rational comparisons prove the four strict inequalities.'),
 'initial_entropy_bound':('Strict initial-threshold binary entropy cap',
   'At the exact fixed threshold theta=0.040409899, the normalized binary entropy H(theta) is strictly less than 0.244168414687344. The threshold and cap are exact rationals; no approximate evaluation is assumed.',
   'Expand H(theta)=-[theta log(theta)+(1-theta)log(1-theta)]/log(2). Range reduction uses log(theta)=log(32 theta)-5 log(2) and log(1-theta)=log(2(1-theta))-log(2). The published logarithm upper bound for log(2), lower bounds for both reduced arguments, and an exact rational comparison prove the cap.'),
 'executable_scale_rounding':('Exact finite rounding of the executable block and band schedules',
   r'For every natural bit parameter $m$, the executable even microblock size $s(m)$ is divisible by two and the block count $J(m)$ by twenty. Whenever $s(m)>0$, the exact total size obeys $0\le e m-\mu(m)<20s(m)$. For every $m$, including the zero-size fallback, the natural band exponent $a(m)$ obeys $0\le(-b)\mu(m)-a(m)<1$, and the divisor $2^{a(m)}$ is positive. Here $e=0.203889696$ and $b=-0.062656016$ are the fixed exact rational parameters. These are finite statements about actual natural-number quotients, without asymptotic hypotheses.',
   'The divisibility properties follow directly from the two multiplicative constructors. For blocks, Euclidean division of 203889696 m by 20000000000 s gives a remainder between zero and that divisor. Casting and dividing by 10^9 yields the stated error interval. Euclidean division of 62656016 mu by 10^9 gives the band-exponent interval, including mu=0. The band divisor is a positive power of two.'),
 'executable_scale_limits':('Limits of the actual rounded microblock, total size and band divisor',
   r'As the natural bit parameter $m$ tends to infinity, the executable schedules obey $s(m)^2/m\to0$, $\mu(m)/m\to e$, $a(m)/m\to(-b)e$, and $\log(2^{a(m)})/m\to\log(2)(-b)e$. Here $s,\mu,a$ are the actual integer cube-root and quotient schedules, $e=0.203889696$ and $b=-0.062656016$ are exact rationals, and logarithms are natural. The limits incorporate both integer rounding errors. They describe the changed schedule and its overhead scale, while the complete 3SUM program still requires separate operational contracts.',
   'The even microblock grows to infinity and its cube is at most m, so s^2/m is bounded by 1/s and tends to zero. Hence s/m also tends to zero. The published finite block rounding interval squeezes mu/m between e-20 s/m and e. The band rounding interval similarly squeezes a/m between (-b)mu/m-1/m and (-b)mu/m. Finally log(2^a)=a log(2).')}

def persist():
    statepath.write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

for key,(title,nl,explanation) in metadata.items():
    if len(sys.argv)>1 and key not in sys.argv[1:]:
        continue
    proof=ROOT/'Solutions'/('Sol_ThreeSum1960614_'+key+'.lean')
    code=proof.read_text(encoding='utf-8')
    if key=='executable_scale_limits':
        log=(HERE/'verification/scales-limits-build-next.txt').read_text(encoding='utf-8')
        assert 'Build completed successfully' in log
        assert 'Built Solutions.Sol_ThreeSum1960614_executable_scale_limits' in log
        assert 'sorry' not in code and 'axiom ' not in code
        child=api('GET','/theorems/'+state['executable_scale_rounding']['theorem_id'])
        assert child['status']=='Proved',child['status']
    elif key=='executable_scale_rounding':
        log=(HERE/'verification/scales-rounding-build.txt').read_text(encoding='utf-8')
        assert 'Build completed successfully' in log
        assert "Sol_ThreeSum1960614_executable_scale_rounding.lean:51:0: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
        assert 'sorry' not in code and 'axiom ' not in code
        assert json.loads((HERE/'verification/scales-definition-job.json').read_text(encoding='utf-8'))['status']=='PUBLISHED'
    elif key in ('encoding_parameter_bounds','initial_entropy_bound'):
        log=(HERE/'verification/numeric-bounds-build.txt').read_text(encoding='utf-8')
        assert 'Build completed successfully' in log
        assert 'Built Solutions.Sol_ThreeSum1960614_'+key in log
        assert 'sorry' not in code and 'axiom ' not in code
        child=api('GET','/theorems/'+state['high_precision_logs']['theorem_id'])
        assert child['status']=='Proved', child['status']
    elif key=='high_precision_logs':
        log=(HERE/'verification/high-precision-build.txt').read_text(encoding='utf-8')
        assert 'Build completed successfully' in log
        assert "Sol_ThreeSum1960614_high_precision_logs.lean:60:0: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
        assert 'sorry' not in code and 'axiom ' not in code
    elif key=='cleared_switch_equivalence':
        log=(HERE/'verification/integer-schedule-build.txt').read_text(encoding='utf-8')
        assert 'Built Solutions.Sol_ThreeSum1960614_cleared_switch_equivalence' in log
        assert "Sol_ThreeSum1960614_cleared_switch_equivalence.lean:55:0: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
        assert 'sorry' not in code and 'axiom ' not in code
    elif key=='tangent_log_bounds':
        log=(HERE/'verification/tangent-build.txt').read_text(encoding='utf-8')
        assert 'Build completed successfully' in log
        assert 'Built Solutions.Sol_ThreeSum1960614_tangent_log_bounds' in log
        assert 'sorry' not in code and 'axiom ' not in code
        child=api('GET','/theorems/79325a7a-1b88-453b-867d-581dbb95566f')
        assert child['status']=='Proved'
    else:
        rec=next(x for x in manifest['proofs'] if x['name']==key)
        assert hashlib.sha256(proof.read_bytes()).hexdigest()==rec['sha256']
    signature=code[code.index('theorem solution'):].split(':= by',1)[0]
    statement=signature.replace('theorem solution','theorem ThreeSum1960614.'+key,1)+' := by sorry'
    scale_key=key in ('executable_scale_rounding','executable_scale_limits')
    preamble='import Definitions.Def_ThreeSum1960614_'+('Scales' if scale_key else 'Analysis')+'\n\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\nopen ThreeSum1960614'+(' ThreeSum1960614.Schedule' if scale_key else '')+('\nopen Filter\nopen scoped Topology' if key=='executable_scale_limits' else '')
    payload={'theorem_name':'ThreeSum1960614.'+key,'theorem_title':title,
       'formal_statement':statement,'preamble':preamble,'natural_language_statement':nl,
       'source':'Author-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, '+('Section 4.1' if scale_key else 'Section 4.2, comparison (I)' if key=='cleared_switch_equivalence' else 'Sections 5.1 and 8, exact_interval.py' if key in ('high_precision_logs','encoding_parameter_bounds','initial_entropy_bound') else 'Sections 2–3')+'; certificate c232_quartic.json; 14 October 2026.',
       'tags':['3sum','entropy','exact-certificates'],'env':'0df444a360eaa60ab8c11dca51a86af692955474'}
    if key not in state:
        result=api('POST','/submit-problem',payload)
        save(key+'-publish-response.json',result)
        assert not result.get('errors')
        state[key]={'payload':payload,'job_id':result['jobs'][0]['job_id'],'explanation':explanation}
        persist()
    job=api('GET','/publish-jobs/'+state[key]['job_id'])
    save(key+'-publish-job.json',job)
    print(key,'publish',job['status'],flush=True)
    if job['status']=='PUBLISHED':
        tid=job.get('theorem_id') or job.get('result',{}).get('theorem_id')
        assert tid, job
        state[key]['theorem_id']=tid
        (ROOT/'Theorems'/('Thm_ThreeSum1960614_'+key+'.lean')).write_text(preamble+'\n\n'+statement+'\n',encoding='utf-8')
        if not state[key].get('submission_id'):
            fields={'theorem_id':tid,'proof_type':'prove','explanation':explanation}
            body,ctype=p2m._multipart(fields,{'file':(proof.name,code)})
            status,raw=p2m._request('POST','/verify',token=p2m.get_token(),raw_body=body,ctype=ctype)
            assert status==200,(status,raw)
            result=json.loads(raw)
            state[key]['submission_id']=result['submission_id']
            save(key+'-submit-response.json',result)
            print(key,'proof submitted',result['submission_id'],flush=True)
        persist()
    elif job['status'] in ['FAILED','ERROR']:
        raise RuntimeError(job)
