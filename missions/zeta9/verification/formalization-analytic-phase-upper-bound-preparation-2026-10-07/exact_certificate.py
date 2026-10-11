"""Reproduce rational arithmetic behind the UNCOMPILED actual phase candidate.

No floats, no Lean/API subprocess, no rewriting the older preparation.
The finite logarithm inequalities come from the actual pinned Mathlib source.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, re, fnmatch

OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
BASE=TASK/'formalization/AnalyticPhase.lean'
CANDIDATE=TASK/'formalization/AnalyticPhaseUpperBound.lean'
BASE_SHA='475f95ba7e9c977a78b6efa8e0f1599d2ec32fcc20e46bfb1bfb3b5e309ea38c'

def binding(path):
    return dict(root_relative=path.relative_to(ROOT).as_posix(),bytes=path.stat().st_size,
        sha256=hashlib.sha256(path.read_bytes()).hexdigest())

def pair(x):return dict(numerator=str(x.numerator),denominator=str(x.denominator))
def partial(y,n):return sum((y**(2*k+1)/Q(2*k+1) for k in range(n)),Q(0))
def proved_mathlib_tail(y,n):return y**(2*n+1)/(1-y*y)

def main():
    assert hashlib.sha256(BASE.read_bytes()).hexdigest()==BASE_SHA
    l2_partial=partial(Q(1,3),6)
    l2_lower=2*l2_partial
    l3_partial=partial(Q(1,2),11)
    l3_tail=proved_mathlib_tail(Q(1,2),11)
    l3_upper=2*(l3_partial+l3_tail)
    A=Q(301,100)*Q(101,201)**10
    assert l2_partial==Q(7878956,22733865)
    assert l3_partial==Q(16760750996903,30512586424320)
    assert l3_tail==Q(1,6291456)
    assert l2_lower>Q(693147,1000000)
    assert l3_upper<Q(1098613,1000000)
    assert 0<A<Q(309,100000)<Q(1,100)
    endpoint_cap=3*Q(1098613,1000000)-20*Q(693147,1000000)+Q(309,100000)
    assert endpoint_cap==Q(-10564011,1000000)<Q(-2641,250)
    # Coarse and exact sums bound the constants, not sampled phase values.
    exact_log_cap=3*l3_upper-20*l2_lower+A
    assert exact_log_cap<endpoint_cap
    deriv_path=ROOT/'.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean'
    mean_path=ROOT/'.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean'
    basic_path=ROOT/'.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean'
    deriv=deriv_path.read_text(encoding='utf-8-sig')
    mean=mean_path.read_text(encoding='utf-8-sig')
    basic=basic_path.read_text(encoding='utf-8-sig')
    assert 'lemma sum_range_le_log_div' in deriv and 'lemma log_div_le_sum_range_add' in deriv
    assert 'lemma antitoneOn_of_hasDerivWithinAt_nonpos' in mean
    assert 'theorem log_le_sub_one_of_pos' in basic
    source=CANDIDATE.read_text(encoding='utf-8-sig')
    comments_removed=re.sub(r'/\-.*?\-/','',source,flags=re.S)
    assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',comments_removed)
    assert source.count('UNCOMPILED')>=2
    assert '∀ x : ℝ, 1 < x → phase x ≤ (-2641 / 250 : ℝ)' in source
    assert 'phase_global_le_one_add_constant (x : ℝ) (hx : 1 < x)' in source
    assert 'smoothPhaseGap_hasDerivAt (x : ℝ) (hx : 1 ≤ x)' in source
    assert 'AntitoneOn smoothPhaseGap (Icc (1 : ℝ) (101 / 100 : ℝ))' in source
    assert 'Real.log_le_sub_one_of_pos (div_pos ha hu)' in source
    candidate_rel=CANDIDATE.relative_to(ROOT).as_posix()
    scope=json.loads((TASK/'scope.json').read_text(encoding='utf-8-sig'))
    owned=any(fnmatch.fnmatch(candidate_rel,pattern) for pattern in scope['sources'])
    assert owned
    preparation_owned=all(any(fnmatch.fnmatch(path.relative_to(ROOT).as_posix(),pattern)
        for pattern in scope['sources']) for path in [Path(__file__),OUT/'README.md',OUT/'preparation-audit.json'])
    assert preparation_owned
    report=dict(status='UNCOMPILED_SOURCE_PREPARATION_EXACT_RATIONAL_ARITHMETIC_PASS',
        role='independent mathematical and Lean-source candidate author; not a kernel audit',
        Lean_executed=False,API_executed=False,proof_objects_borrowed=False,
        old_15_lemma_source_unchanged=True,actual_function='ZetaNine.AnalyticPhase.phase',
        candidate_theorems=re.findall(r'^theorem (\w+)',source,re.M),
        candidate_definitions=re.findall(r'^def (\w+)',source,re.M),
        exact_domain='forall real x, 1 < x',exact_requested_bound='-2641/250',
        certified_stronger_cap='-10564011/1000000',strict_cap_margin=pair(Q(-2641,250)-endpoint_cap),
        exact_rational_checks=dict(
          log2_argument='1/3',log2_terms=6,log2_partial=pair(l2_partial),log2_lower_margin=pair(l2_lower-Q(693147,1000000)),
          log3_argument='1/2',log3_terms=11,log3_partial=pair(l3_partial),proved_Mathlib_log3_tail=pair(l3_tail),
          log3_upper_margin=pair(Q(1098613,1000000)-l3_upper),actual_A=pair(A),
          A_upper_margin=pair(Q(309,100000)-A),exact_log_cap=pair(exact_log_cap)),
        mathematical_chain=[
          'Actual smooth G(1)=0; its derivative is log((x+2)*(x/(x+1))^10)-log(A).',
          'On the closed interval [1,101/100], x/(x+1)<=101/201 and x+2<=301/100, hence the derivative is nonpositive.',
          'Continuity is proved only for smooth G; no continuity of u log(u) at zero is assumed.',
          'Antitonicity gives G(1+u)<=0 for 0<u<=1/100.',
          'Actual phase(1+u)=phase(1)+u*(1+log(A/u))+G(1+u).',
          'log z<=z-1 gives u*(1+log(A/u))<=A for every positive u.',
          'The existing actual strictAntiOn right component controls all x>=101/100.',
          'Actual phase(1)=3log3-20log2; certified rational log bounds and A<309/100000 close the global strict cap.'],
        source_contract=dict(no_desired_bound_or_derivative_hypothesis=True,no_sorry_axiom_native_decide=True,
            imports_unchanged_uncompiled_base=True,whole_open_domain_preserved=True,
            candidate_already_owned_by_scope_glob=owned,official_build_target_added=False,
            preparation_directory_owned=preparation_owned,
            compiled_or_registered_proof_claimed=False),
        exact_open_obligations=['Fresh compilation of the unchanged 15-lemma base and this complete candidate.',
          'Explicit full-type/standard-axiom checks after a new Root Lean lane grant.',
          'Moment asymptotics, infinite tails and uniform o(1) are separate parts of Z9.A and are not proved here.'],
        stable_inputs=[binding(p) for p in [BASE,CANDIDATE,Path(__file__),OUT/'README.md',deriv_path,mean_path,basic_path]])
    (OUT/'preparation-audit.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:report[k] for k in ['status','Lean_executed','old_15_lemma_source_unchanged','exact_domain','exact_requested_bound','certified_stronger_cap','strict_cap_margin']},ensure_ascii=False))

if __name__=='__main__':main()
