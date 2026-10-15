"""Generate the faithful statement bundle and register this task. Offline only."""
import json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = 'User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md (14 October 2026)'
UPSTREAM = 'https://github.com/c0ldzy17/three-sum-lean/tree/2b639655e07421b9ac743de9090459bab473a7c0'
defs = '''import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ThreeSum1960614

noncomputable def entropy (t : ℝ) : ℝ := Real.binEntropy t / Real.log 2
noncomputable def E (c : ℕ) : ℝ := (c : ℝ) / 2 * entropy (1 / c)
noncomputable def kappa (c : ℕ) : ℝ :=
  2 * c * entropy (1 / (2 * c)) - c * entropy (1 / c) - 1
noncomputable def gamma (c : ℕ) (t : ℝ) : ℝ :=
  c * entropy (1 / c) - c * entropy ((1 - t) / c)
def phi (t : ℝ) : ℝ :=
  (785174904 * t + 72447023 * t ^ 2 + 24044466 * t ^ 3 + 12022459 * t ^ 4) / 100000000
def phiDeriv (t : ℝ) : ℝ :=
  (785174904 + 2 * 72447023 * t + 3 * 24044466 * t ^ 2 + 4 * 12022459 * t ^ 3) / 100000000
def epsilon : ℝ := 203889696 / 1000000000
def beta : ℝ := -(62656016 / 1000000000)
def saving : ℝ := 193175570 / 1000000000
def theta : ℝ := 40409899 / 1000000000
def tau : ℝ := 13 / 20
def rho : ℝ := 2790503 / 10000000
def tangentPoint : ℝ := 17200068185091493 / 100000000000000000
def principal : ℝ := 196061388 / 100000000
def target : ℚ := 1960614 / 1000000
def v : ℝ := saving - 2 * beta
def threshold (a : ℝ) : ℝ := (v + a) / (1 - a)
def ledger (e b S terminal ratio EE kk hh : ℝ) : List ℝ :=
  [2 * e * EE,
   1 + e * (EE - b),
   2 - e * S,
   2 - e * (1 / 2 + b - hh),
   2 - e * (1 / 2 - b - kk - ratio * (1 + S - 2 * b)),
   2 - e * (terminal - 1 / 2 - b - kk),
   e * (8 / 5) * (EE + 1 / 2),
   2 + e * (4 / 5 - (2 / 5) * EE - 2 * b),
   1 + e * (1 / 2 - b),
   2 - e * (EE + b),
   2 - 2 * e * (EE + b), 1]
noncomputable def costs : List ℝ :=
  ledger epsilon beta saving tau rho (E 232) (kappa 232) (entropy theta)
def clearedSwitch (J s j q : ℕ) : Prop :=
  let r := (J - j) * s
  500000000 * (J - j) *
    (785174904 * q * r ^ 3 + 72447023 * q ^ 2 * r ^ 2 +
     24044466 * q ^ 3 * r + 12022459 * q ^ 4) ≥
    100000000 * (159243801 * J + 500000000 * j) * r ^ 4
noncomputable def ModelFeasible (c : ℕ) (e b S th terminal ratio R : ℝ) : Prop :=
  0 < e ∧ e < 1 ∧ b < 0 ∧ 0 < S ∧
  0 ≤ th ∧ th ≤ 1 / 2 ∧ 0 ≤ terminal ∧ terminal < 1 ∧
  0 < ratio ∧ S - 2 * b ≤ gamma c th ∧
  (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), entropy t ≤ ratio * (1 + gamma c t)) ∧
  ∀ z ∈ ledger e b S terminal ratio (E c) (kappa c) (entropy th), z ≤ R

end ThreeSum1960614
'''
pre = '''import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614
'''
items = [dict(kind='definition', definition_name='ThreeSum1960614_Analysis',
  definition_title='Entropy, quartic integer switch, twelve costs and fixed-expansion model',
  definition=defs, source=SOURCE+'; Sections 1–5 and 7; upstream '+UPSTREAM,
  natural_language_statement=r'''Defines binary entropy in bits $H(t)$, $E_c=(c/2)H(1/c)$, $\kappa_c=2cH(1/(2c))-cH(1/c)-1$, and $\gamma_c(t)=cH(1/c)-cH((1-t)/c)$ for natural expansion $c$. The quartic is $P(t)=7.85174904t+0.72447023t^2+0.24044466t^3+0.12022459t^4$, with its polynomial derivative. The fixed rational parameters are $e=0.203889696$, $b=-0.062656016$, $S=0.193175570$, $\theta=0.040409899$, $\tau=13/20$, $\rho=0.27905030$, and $u=0.17200068185091493$. The principal cost cap is $1.96061388$ and the campaign target is the rational $1.960614$.

The ledger lists all twelve source costs in their source order. `costs` instantiates them at the fixed parameters and $c=232$. The natural-number predicate `clearedSwitch` is the degree-four integer comparison of Section 4.2, with $v=S-2b=159243801/500000000$. `ModelFeasible` describes the relaxed fixed-expansion real cost model, including its whole-interval entropy inequality and all twelve charges. It is not a model of arbitrary 3SUM algorithms. Total logarithms, division and natural subtraction are unrestricted in these definitions; theorem hypotheses delimit the intended domains. The shared machine and decision-problem definitions are imported unchanged.''',
  tags=['3sum','entropy','word-ram','exact-certificates'])]

def add(key, title, binders, nl, loc, milestone=True):
    item = dict(kind='theorem', theorem_name='ThreeSum1960614.'+key, theorem_title=title,
      formal_statement='theorem ThreeSum1960614.'+key+binders+' := by sorry', preamble=pre,
      natural_language_statement=nl, source=SOURCE+'; '+loc+'; upstream '+UPSTREAM,
      tags=['3sum','algorithms','entropy','word-ram'])
    if milestone:
        item['milestone_title']=loc+' — '+title
        item['milestone_description']=nl
    items.append(item)

add('quartic_switch_bounds', 'Quartic switch validity on the full half interval', ''' (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    phi t ≤ gamma 232 t ∧ 0 < phiDeriv t ∧ phiDeriv t < 9 ∧
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t''',
  r'''For every real $0\le t\le1/2$, the exact quartic satisfies $P(t)\le\gamma_{232}(t)$ and $0<P'(t)<9$. Its tangent at $u=0.17200068185091493$ lies below $P(t)$ throughout the same interval. Both endpoints are included; the conclusion concerns the whole continuum.''', 'Sections 2–3')
add('uniform_entropy_bound', 'A uniform entropy bound for the quartic switch', ''' (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    entropy t < rho * (1 + phi t)''',
  r'''For every $0\le t\le1/2$, including the entropy endpoints, $H(t)<0.27905030(1+P(t))$. The coefficient is exact and the statement covers the full interval, not a finite set of samples.''', 'Section 3')
add('quartic_parameter_certificate', 'Exact parameters and all twelve cost caps', ''' :
    4648781151243719 / 1000000000000000 < E 232 ∧
    E 232 < 4648781151243720 / 1000000000000000 ∧
    1557987216578 / 1000000000000000 < kappa 232 ∧
    kappa 232 < 1557987216579 / 1000000000000000 ∧
    entropy theta < 244168414687344 / 1000000000000000 ∧
    v < phi theta ∧ threshold tau < phi (1 / 2) ∧
    0 < epsilon * (E 232 + beta) ∧ epsilon * (E 232 + beta) < 1 ∧
    (∀ z ∈ costs, z < principal) ∧ principal < (target : ℝ)''',
  r'''The expansion-232 entropy and multiplicity constants satisfy $4.648781151243719<E_{232}<4.648781151243720$ and $0.001557987216578<\kappa_{232}<0.001557987216579$, while $H(\theta)<0.244168414687344$. The initial threshold is below $P(\theta)$, the terminal threshold is below $P(1/2)$, and $0<e(E_{232}+b)<1$. Every one of the twelve exact real costs is strictly below $1.96061388<1.960614$. These inequalities assert an analytic certificate and do not themselves assert a machine runtime.''', 'Section 5.1')
add('integer_schedule', 'Least integer quartic switch and uniform rounding bounds', ''' (J s j : ℕ)
    (hJ : 0 < J) (hs : 0 < s) (heven : Even s) (hj : j < J)
    (hlevel : (j : ℝ) / J ≤ tau) :
    ∃ q : ℕ, 0 < q ∧ q ≤ ((J - j) * s) / 2 ∧ clearedSwitch J s j q ∧
      (∀ k < q, ¬ clearedSwitch J s j k) ∧
      threshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / ((J - j) * s)) ∧
      phi ((q : ℝ) / ((J - j) * s)) <
        threshold ((j : ℝ) / J) + 9 / ((J - j) * s) ∧
      saving ≤ 2 * beta - (j : ℝ) / J +
        (1 - (j : ℝ) / J) * gamma 232 ((q : ℝ) / ((J - j) * s)) ∧
      (1 - (j : ℝ) / J) * entropy ((q : ℝ) / ((J - j) * s)) <
        rho * (1 + v) + 9 * rho / (J * s)''',
  r'''For arbitrary positive natural block count $J$, positive even microblock size $s$, and level $0\le j<J$ with $j/J\le13/20$, let $r=(J-j)s$ and $\mu=Js$. There exists a positive least integer $q\le r/2$ satisfying the cleared integer comparison, and every smaller natural number fails it. This same $q$ satisfies $K\le P(q/r)<K+9/r$ for $K=(v+j/J)/(1-j/J)$. It also satisfies $S\le2b-j/J+(1-j/J)\gamma_{232}(q/r)$ and $(1-j/J)H(q/r)<\rho(1+v)+9\rho/\mu$. No divisibility of $J$ is needed for these per-level bounds; positivity and evenness make $r/2$ an integer and every real denominator nonzero.''', 'Section 4.2–4.3')
add('local_cover_bounds', 'Local-cover incidence and degree bounds for general expansion', ''' (c h : ℕ)
    (hc : 3 ≤ c) (hh : 0 < h) :
    Nat.choose (c * (2 * h)) h * Nat.choose (c * (2 * h) - h) h =
      Nat.choose (c * (2 * h)) (2 * h) * Nat.choose (2 * h) h ∧
    Nat.choose (c * (2 * h) - h) h ≤ Nat.choose (c * (2 * h)) h ∧
    Nat.choose (2 * h) h < 2 ^ (2 * h) ∧
    2 ^ (2 * h) < Nat.choose (c * (2 * h)) (2 * h) ∧
    Nat.choose (c * (2 * h) - h) h ^ 2 <
      Nat.choose (c * (2 * h)) (2 * h) * 2 ^ (2 * h)''',
  r'''For natural $c\ge3$ and $h>0$, set $s=2h$, $L=cs$, $M=\binom Ls$, $V=\binom Lh$, $\Delta=\binom{L-h}h$, and $G=\binom sh$. Then $V\Delta=MG$, $\Delta\le V$, $G<2^s<M$, and $\Delta^2<M2^s$. This finite statement permits expansion 232; it does not by itself establish the global encoding or machine cost.''', 'Section 6')
add('fixed_model_lower_bound', 'Lower bound for the relaxed fixed-expansion cost model', '''
    (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R) :
    (196061349120 / 100000000000 : ℝ) < R''',
  r'''For every real tuple $(e,b,S,\theta,\tau,\rho,R)$ satisfying the explicitly defined relaxed twelve-cost model at $c=232$, its common cost upper bound satisfies $R>1.96061349120$. The model requires $0<e<1$, $b<0$, $S>0$, $0\le\theta\le1/2$, $0\le\tau<1$, $\rho>0$, $S-2b\le\gamma_{232}(\theta)$, the whole-interval bound $H(t)\le\rho(1+\gamma_{232}(t))$, and each ledger charge at most $R$. The quantification covers all such parameter choices. This is only a lower bound for that fixed model, not for 3SUM algorithms or other expansions.''', 'Section 7')
add('costs_solve_3sum', 'Complete expansion-232 program and runtime bridge', ''' (r : ℚ)
    (hr : 0 < r) (hcost : ∀ z ∈ costs, z < (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r''',
  r'''For every positive rational $r$ strictly above all twelve costs of the fixed expansion-232 quartic parameter choice, deterministic integer 3SUM satisfies the campaign's exact shared word-RAM specification in $O(n^r)$ time. The theorem must construct a finite program for each fixed integer-size exponent, preserve distinct input positions and repetitions, reject sizes below three, and establish correctness for every sufficiently large word width together with instruction, addressing and memory costs. No solver oracle or assumed program-correctness contract is a hypothesis. This is the remaining algorithmic extension sought by this mission: the source package explicitly leaves it unproved.''', 'Sections 0, 4–6: outstanding algorithmic extension')
add('threeSum_1960614', '3SUM in O(n^1.960614) word-RAM steps', ''' :
    EndStatement.ThreeSum.SolvedInTime 1.960614''',
  r'''For every fixed natural integer-size exponent $\kappa$, there exist a finite deterministic word-RAM program $P$, a natural word-width constant $b$, and a natural-valued time function $T$. For every input size $n$, every list of $n$ integers of absolute value at most $n^\kappa$, and every word width $W\ge b(\lfloor\log_2n\rfloor+1)$, the program halts within $T(n)$ steps and accepts exactly when three pairwise distinct positions sum to zero. Repeated values at different positions are allowed. For the reduced rational $1.960614=980307/500000$, there is a natural $K$ such that $T(n)^{500000}\le K n^{980307}$ for every $n\ge2$. This exact campaign goal remains unproved until the modified complete program and runtime bridge are closed; it is not asserted to follow from numeric checks alone.''', 'Section 0: intended machine target', False)

def main():
    (ROOT / 'Definitions/Def_ThreeSum1960614_Analysis.lean').write_text(defs, encoding='utf-8')
    (HERE / 'payloads.json').write_text(json.dumps(items, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    (ROOT / 'Theorems/Thm_ThreeSum1960614_Draft.lean').write_text(pre+'\n'+
      '\n\n'.join(x['formal_statement'] for x in items[1:])+'\n', encoding='utf-8')
    blind = HERE / 'blind'
    blind.mkdir(exist_ok=True)
    for item in items:
        key=item.get('theorem_name', item.get('definition_name')).split('.')[-1]
        text=item.get('definition') or defs+'\n'+(ROOT/'Definitions/Def_TrulySubcubicAPSP_SourceSpecification.lean').read_text(encoding='utf-8')+'\n'+item['formal_statement']
        (blind / (key+'.lean')).write_text(text, encoding='utf-8')
    indexpath=ROOT/'missions/index.json'
    index=json.loads(indexpath.read_text(encoding='utf-8'))
    if not any(m['slug']=='3sum-1960614' for m in index['missions']):
        index['missions'].append(dict(slug='3sum-1960614', title='3SUM: quartic switch and exponent 1.960614',
          family='algorithms',handoff='missions/3sum-1960614/status.md',scratch=None))
        indexpath.write_bytes((json.dumps(index, ensure_ascii=False, indent=2)+'\n').encode('utf-8'))
    scope=json.loads((HERE/'scope.json').read_text(encoding='utf-8'))
    if list((ROOT/'Solutions').glob('Sol_ThreeSum1960614_*.lean')):
        if 'Solutions/Sol_ThreeSum1960614_*.lean' not in scope['sources']:
            scope['sources'].append('Solutions/Sol_ThreeSum1960614_*.lean')
    scope.pop('build_modules',None)
    scope['build']=['Theorems/Thm_ThreeSum1960614_Draft.lean']
    if list((ROOT/'Solutions').glob('Sol_ThreeSum1960614_*.lean')):
        scope['build'].append('Solutions/Sol_ThreeSum1960614_*.lean')
    scope['module_target_syntax']=True
    (HERE/'scope.json').write_text(json.dumps(scope,indent=2)+'\n',encoding='utf-8')
    print('Prepared',len(items),'draft items,',sum('milestone_title' in x for x in items),'milestones')

if __name__=='__main__':
    main()
