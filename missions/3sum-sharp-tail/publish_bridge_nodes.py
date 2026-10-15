"""Publish checked support lemmas for this task's actual cost bridge."""
import importlib.util
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
STATE = HERE / 'verification/bridge-nodes.json'
spec = importlib.util.spec_from_file_location('p2m', ROOT / 'scripts/p2m_api.py')
p2m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p2m)

DESCRIPTIONS = {
    'pruned_program_solves': (
        'Polynomial native resources for the arbitrary-parameter pruned program',
        'For every rational parameter record G there is a polynomial native '
        'Need which, under CostsWithinP and the native Lop-count task '
        'precondition, guarantees the actual offline32 Meets specification '
        'of program31P G. The conclusion holds for every appended program, '
        'free pointer and sufficiently large word, space and depth limits. '
        'The runtime is the original natural tOffline32P step count.',
        'Generic resource and execution assembly from the accepted pruned '
        'program source. Uses actual Hyp30 below/top bounds and the proved '
        'generic program correctness interface; no fixed numerical parameter '
        'specialization is assumed.'),
    'pruned_lop_detection': (
        'A native global Lop detector from finite sharp-tail cost parameters',
        'Given a finite RatParams record and rational 0<a<1, 0<s<1/2 '
        'with CostsWithinP on every 1<=D<=N^a, the actual light model '
        'has a global Lop detector. On that regime its time is bounded '
        'by a uniform nonnegative constant times preprocessing, all query '
        'costs, and ND+w+1 overhead. Outside the regime an actual finite '
        'program branch supplies correctness through the brute routine.',
        'Native ThinInst/TaskN program assembly using an exact integer-power '
        'regime test, the arbitrary-parameter pruned resource theorem and '
        'actual count-to-detection execution semantics.'),
    'full_d_uniformize': (
        'Thresholded full dimension Exact Triangle time extends to every size',
        'For any 0<=delta<=1, natural logarithmic degree and threshold, '
        'an actual light-model ExplicitAt solver implies ExactTriangleUniform '
        'with the same saving and logarithmic degree. A finite choice program '
        'selects the new solver for large sizes and an existing correct '
        'solver for bounded small sizes, preserving native polynomial '
        'resources and all-size correctness.',
        'Generic ChooseBySize and monotone-time assembly from accepted '
        'Exact Triangle source. The small-size solver is used only on a '
        'fixed bounded domain; the large-size exponent comes from the '
        'supplied new ExplicitAt proof.'),
    'rational_power_representation': (
        'Finite exponent data and an exact integer-power regime test',
        'For rational 0<a<1 and 0<s<1/2 there are natural '
        'A,B,c,e with positive denominators, A<=B, 2c<=e, '
        'A/B=a and c/e=s/2. For every N,D>=1, '
        'D<=N^a holds exactly when D^B<=N^A. This gives finite '
        'integer exponent data both for the host parameters and '
        'for an exact program branch, without numerical approximation.',
        'Elementary rational-arithmetic and real-power interface for '
        'the finite full-D program realization of the sharp-tail certificate.'),
    'full_d_parameter_host': (
        'Full dimension Exact Triangle host for arbitrary rational power parameters',
        'For natural a,b,c,e with b,e>=1, a<=b and 2c<=e, the actual '
        'light-model full dimension host satisfies Theorem 17 for '
        'D(n)=floor(n^(a/b)) and g(n)=ceil(D(n)^(c/e)). The theorem also '
        'supplies these exact floor and ceiling identities. The host is '
        'assembled from finite rational-parameter routines, actual '
        'Exact Triangle program correctness, and polynomial word, cell '
        'and depth needs. No middle-dimension or fixed-parameter result '
        'is assumed.',
        'Generic assembly and parameter-procedure proofs from the accepted '
        'full-D Exact Triangle and claim_aeUniform_mid source snapshots; '
        'uses the existing Proved et17_spec and obeysBound17_hostTime '
        'interfaces, while excluding the fixed numerical conclusions.'),
    'full_d_call_total': (
        'All full dimension oracle calls have the desired saving',
        'Under the full-D parameter bounds and D^(1+s)<=n, a call '
        'with preprocessing n^2(log D+1)^2/D^s, query time '
        'D^(1/2-s)(log D+1), and nD+w+1 overhead, with '
        'w<=n^2/sqrt(D), has total 4ng call-and-answer-reading '
        'cost at most (64C+8Cprime)n^3 D^(-s/2)(log D+1)^2. '
        'Both cost constants are nonnegative and all loop overheads '
        'are counted.',
        'Derived elementary full-D runtime inequality for Xu, same '
        'manuscript, Sections 3-4; uses the proved full_d_call_balance.'),
    'full_d_extra_total': (
        'Full dimension scan, prime and construction costs preserve the saving',
        'For n>=3, 1<=D<=n^a, 0<=s<=1/2, '
        'D^(s/2)<=g<=2D^(s/2), a(1+s)<=1 and '
        'log_2(7)+3a/2<=3-as/2, the actual scan, prime-selection and '
        'instance-construction time functions of the full-D host are '
        'bounded by 4C kappa n^3 D^(-s/2) log^2 n whenever '
        'C>=0 and kappa>=1.',
        'Derived bound for the actual termScans, termPrime and termBuild '
        'functions in the pinned full-D Theorem 17 interface. The '
        'certificate strict prime/build margins imply its hypotheses.'),
    'full_d_explicit_time': (
        'Generic full dimension costs give the explicit Exact Triangle exponent',
        'Let 0<a<=1, 0<=s<=1/2, D(n)=floor(n^a), '
        'g(n)=ceil(D(n)^(s/2)), and suppose the actual model has '
        'the full-D Theorem 17 host and Lop detection with '
        'preprocessing n^2(log D+1)^2/D^s, query '
        'D^(1/2-s)(log D+1), and nD+w+1 overhead on D<=n^a. '
        'If a(1+s)<=1 and log_2(7)+3a/2<=3-as/2, then one '
        'actual Exact Triangle solver has time O(kappa n^(3-as/2) '
        'log^2 n) from some fixed size onward, uniformly in '
        'kappa>=1 and input weight magnitude u<=n^kappa.',
        'Generic full-D Theorem 19 deduction for Xu, same manuscript, '
        'Sections 3-4. Includes floor/ceiling effects and all host '
        'terms; reuses the proved full-D call and extra-cost bounds.'),
    'uniform_three_sum_transfer': (
        'Uniform Exact Triangle exponent transfers to integer 3SUM',
        'For any real saving delta<=1, rational r>2-delta/2, and natural '
        'logarithmic degree e, a uniform Exact Triangle solver in the actual '
        'light model implies EndStatement.ThreeSum.SolvedInTime r. The '
        'conclusion includes the original word-RAM finite-program and '
        'all-sufficient-word-width semantics. The five existing proved '
        'reduction and realization interfaces are actual dependencies.',
        'Generic reduction and asymptotic proof bodies extracted from '
        'ACCEPTED TrulySubquadratic3SUM.threeSum_1999074, submission '
        '7d7091ea-6717-4422-b336-026472ef8a11; the numerical specialization '
        'is excluded. Composes CH20 and VW13 Theorem 4.3 with the actual '
        'light-model realization and shared EndStatement interface.'),
    'full_d_call_balance': (
        'Full dimension host call factors preserve the desired saving',
        'If D,n>=1, 0<=s<=1/2, D^(s/2)<=g<=2D^(s/2), and D^(1+s)<=n, '
        'then the full dimension preprocessing, query, overhead, construction '
        'and scan factors are bounded respectively by 2D^(-s/2), '
        '2D^(-s/2), 2D^(-s/2), 2nD^(-s/2), and D^(-s/2). '
        'This is an elementary real-power balance lemma, without any '
        'additional program or runtime assumption.',
        'Derived auxiliary algebraic bounds for Xu, Deterministic Integer '
        '3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis, '
        'Sections 3-4, composed with the full-D Theorem 17 host.'),
    'pruned_offline_steps': (
        'Uniform bound for the actual pruned offline routine step count',
        'For every rational parameter record G, nonnegative cost constant C, '
        'and fixed setup constants c0,k, there is a uniform constant A '
        'such that CostsWithinP(G,C,N,D,Tp,Tq) implies '
        'tOffline32P(c0,G,N,D,w)+k <= A(Tp+w Tq) for every number w '
        'of queries. The natural step-count function includes preprocessing, '
        'parameter setup and the complete query loop. No additional '
        'asymptotic cost hypothesis is assumed.',
        'Reusable generic cost proof from the ACCEPTED '
        'TrulySubquadratic3SUM.exactTriangleUniform_9261_5000000 source, '
        'submission 45d9b962-dd72-4a1f-a54c-8186be3ae4ec, '
        'ThreeSumApsp/Pruned/CostsP.lean at source commit 27a2fa4bab32. '
        'Actual enumeration and time-function proof bodies are included; '
        'the existing proved enumeration/order statements are reused.'),
    'rational_cost_regime': (
        'Finite rational parameters realizing the sharp-tail cost regime',
        'For integer c>10 and rational eta,a,s satisfying the strict encoding, '
        'preprocessing and query inequalities, with 0<a<1 and 0<s<1/2, '
        'there are a finite rational parameter record G and a uniform '
        'constant C>=0 such that CostsWithinP holds for every '
        '1<=D<=N^a. The preprocessing bound is N^2(log D+1)^2/D^s and '
        'the query bound is D^(1/2-s)(log D+1). The record represents '
        'c exactly and eta by its integer numerator and denominator, '
        'and includes a fixed threshold for the bounded-size cases.',
        'Derived finite-parameter interface for Xu, same manuscript, '
        'Sections 3-4. It consumes the proved pruned cost certificate '
        'and the actual RatParams/CostsWithinP definitions of the '
        'published pruned program.'),
    'pruned_program_correct': (
        'Pruned offline program correctness for arbitrary rational parameters',
        'For every finite rational parameter record G, the published '
        'program31P(G) satisfies OfflineSpec32P at every machine limit. '
        'It executes the specified preprocessing and queries on the actual '
        'stored matrices and selected entries, with the declared step counts. '
        'This is the generic correctness interface of the pruned program; '
        'asymptotic cost regimes, word-size polynomial bounds and the '
        '3SUM reduction are separate conclusions.',
        'Reusable generic portion of the ACCEPTED proof of '
        'Light.Sec4.allInstancesP_programP, submission '
        '50de6837-5a9a-4f1f-ab1f-e9cff8fc270a. '
        'ThreeSumApsp/Pruned/Program31P.lean and related choosing-parameter '
        'specifications at formal-math commit 27a2fa4bab32. '
        'The preprocessing, query and offline procedure proofs are generic '
        'in G; the later fixed-parameter wrapper is excluded.'),
    'cost_regime_solve_3sum': (
        'Finite pruned program cost regime implies the 3SUM exponent',
        'Fix the finite rational parameters G of the published pruned program, '
        'and rational a,s,r with 0<a<1 and 0<s<1/2. Suppose a uniform '
        'CostsWithinP certificate holds whenever 1<=D<=N^a, with '
        'preprocessing bound N^2(log D+1)^2/D^s and query bound '
        'D^(1/2-s)(log D+1). If the prime-selection and instance-construction '
        'exponents are strictly below 3-as/2, then integer 3SUM is solved '
        'on the word RAM in O(n^r) for every r>2-as/4. The conclusion uses '
        'the exact shared EndStatement model, including finite programs '
        'and all sufficiently large word widths.',
        'Algorithmic interface lemma derived from Xu, same manuscript, '
        'Sections 3-4, composed with the verified 3sum-apsp pruned program '
        'and parameterized all-edges/Exact-Triangle/3SUM reductions. '
        'This remaining semantic bridge is a separate open proof obligation, '
        'not an additional runtime hypothesis in the original certificate.'),
    'pruned_cost_certificate': (
        'Sharp-tail certificate bounds the exact pruned preprocessing and query costs',
        'Let c>10 be an integer, theta in (0,9/10), and a>0,s rational. '
        'Under a(A(c)+Gamma(c,theta))<1, s<Gamma(c,theta), and s<1/2-q(theta), '
        'there exist C>=0 and a threshold m0 such that for every D>=2 with '
        'D<=N^a and m=ceil(log_4 D)>=m0 the tile fits, cost8p<=C N^2 '
        '(log D)^2/D^s, and costQuery<=C D^(1/2-s) log D. The quantities '
        'are the existing pruned program cost functions, with the exact '
        'binomial tail retained.',
        'Derived interface transfer for Xu, same manuscript, Sections 3-4. '
        'Uses the existing complete CorollaryP.costs proof in '
        'ThreeSumApsp/Pruned/Costs.lean at commit 27a2fa4bab32 and the '
        'proved pruned encoding comparison. Actual finite program '
        'correctness and reductions remain separate obligations.'),
    'rational_theta_certificate': (
        'Rational switch parameter preserving strict certificate margins',
        'Fix an integer c>10, real theta in (0,9/10), and rational a,s. '
        'If a(A(c)+Gamma(c,theta))<1, s<Gamma(c,theta), and '
        's<1/2-q(theta), then there is a rational eta in (0,9/10) '
        'satisfying the same three strict inequalities. This gives a finite '
        'rational switch parameter for the program while preserving the '
        'encoding, preprocessing and query margins.',
        'Derived parameter selection lemma for Xu, Deterministic Integer 3SUM '
        'in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis, '
        'Sections 3-4. Continuity and rational density justify the finite '
        'program implementation of the real switch parameter.'),
    'pruned_encoding_comparison': (
        'Pruned encoding exponent is bounded by the original encoding exponent',
        'For every real c>1, the exponent ((c/2)H(1/c)+(c-1)log(3))/log(4) '
        'is at most A(c). Consequently the strict thinness assumption in the '
        'sharp-tail certificate also satisfies the encoding assumption of the '
        'parameterized pruned program interface. This comparison follows from '
        'the weighted log inequality H(p)+(1-p)log(9)<=log(10).',
        'Derived auxiliary inequality for Xu, same manuscript, Section 4, '
        'encodingbound; the pruned exponent Apruned is defined in the existing '
        'platform module APSP299791_Defs4, source ThreeSumApsp/Pruned/Costs.lean '
        'at formal-math commit 27a2fa4bab32. It is not an additional theorem '
        'claimed in the manuscript.'),
    'encoding_bound': (
        'Encoding cost bound from the binomial entropy certificate',
        'For every integer c>10 and m>=1, the encoding factor 10^(cm)/sqrt(M) '
        'is at most sqrt(cm+1) times (4^m)^A(c), where M is the exact baseline '
        'box count choose(cm,m)*9^(cm-m). This is the pointwise encoding '
        'inequality used to show eventual tile fit and absorb preprocessing '
        'overheads. The proof uses the lower binomial entropy bound and exact '
        'exponential algebra; it makes no program-runtime conclusion by itself.',
        'Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper '
        'Binomial-Tail Analysis (13 October 2026), Section 4, equation encodingbound.'),
    'retained_tiles_cost': (
        'Sharp-tail bound for the actual all-tiles routine step count',
        'Bounds the published natural-number time function tAllTiles at L=cm and '
        't=ceil(theta*m). The bound counts the lengths of the star-box lists '
        'actually traversed by the routine, uses their exact binomial enumeration '
        'formula, and applies the sharp normalized tail. The bound holds for '
        'every number of bands, with explicit constant 1600 and all loop '
        'overheads included. Tile-fit, encoding, compiler and reduction costs '
        'must still be composed before claiming the final word-RAM runtime.',
        'Yuxuan Xu, same manuscript, Sections 2.1 and 4, equations unrelaxed and '
        'boxcost; actual tTile/tAllTiles time functions from anthropics/formal-math '
        '3sum-apsp, commit e1a4e6508154ea59f030480661590a9fe3018011, '
        'ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean and '
        'ThreeSumApsp/Spec/Sec4/Theorem30/StarBoxes.lean.'),
}


def save(state):
    STATE.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def api(method, path, data=None):
    status, raw = p2m._request(method, path, token=p2m.get_token(), data=data)
    if status not in (200, 202):
        raise RuntimeError(f'{path}: HTTP {status}: {raw[:1000]}')
    return json.loads(raw)


def main():
    state = json.loads(STATE.read_text(encoding='utf-8')) if STATE.exists() else {}
    for suffix in sys.argv[1:]:
        if suffix in ('uniform_three_sum_transfer', 'full_d_call_balance',
                      'full_d_call_total', 'full_d_extra_total',
                      'full_d_parameter_host', 'full_d_explicit_time',
                      'rational_power_representation', 'pruned_program_solves',
                      'pruned_lop_detection', 'full_d_uniformize'):
            validation = json.loads((HERE / 'verification/new-support-validation.json').read_text(encoding='utf-8'))[suffix]
            proof = (ROOT / f'Solutions/Sol_ThreeSumSharpTail_{suffix}.lean').read_text(encoding='utf-8').encode('utf-8')
            assert validation['lean_exit_code'] == 0
            assert validation['sha256'] == hashlib.sha256(proof).hexdigest()
            assert all(child['status'] == 'Proved' for child in validation['current_proved_children'])
            print(suffix + ': checked complete proof; publish declaration as Open, then verify proof', flush=True)
        title, description, source = DESCRIPTIONS[suffix]
        record = state.setdefault(suffix, {})
        if record.get('status') == 'REQUEST_PREPARED' and not record.get('job_id'):
            raise RuntimeError('Recover uncertain prior creation before retrying ' + suffix)
        if record.get('job_id'):
            job = api('GET', '/publish-jobs/' + record['job_id'])
            record.update(status=job['status'], theorem_id=job.get('theorem_id'), job=job)
            save(state)
            print(suffix + ': ' + job['status'], flush=True)
            continue
        name = 'ThreeSumSharpTail.' + suffix
        text = (ROOT / f'Theorems/Thm_ThreeSumSharpTail_{suffix}.lean').read_text(encoding='utf-8')
        marker = 'theorem ' + name
        assert text.count(marker) == 1
        preamble, statement = text.split(marker, 1)
        payload = {'theorem_name': name, 'theorem_title': title,
            'preamble': preamble.strip(), 'formal_statement': (marker + statement).strip(),
            'natural_language_statement': description, 'source': source,
            'tags': ['3sum', 'sharp-tail', 'word-ram-costs']}
        record.update(status='REQUEST_PREPARED', payload=payload)
        save(state)
        response = api('POST', '/submit-problem', {'problems': [payload],
            'env': '0df444a360eaa60ab8c11dca51a86af692955474'})
        record['response'] = response
        assert not response.get('errors'), response
        assert len(response['jobs']) == 1, response
        record.update(status='PENDING', job_id=response['jobs'][0]['job_id'])
        save(state)
        print(suffix + ': queued ' + record['job_id'], flush=True)


if __name__ == '__main__':
    main()
