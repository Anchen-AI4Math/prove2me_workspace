import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
before = json.loads((HERE/'verification/proposal-before.json').read_text(encoding='utf-8-sig'))
source = 'Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), '
source += 'Hexagon submission https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3'
foundation = before['items'][0]['definition']
(ROOT/'Definitions/Def_TrulySubcubicAPSP_SourceSpecification.lean').write_text(foundation, encoding='utf-8')
defs = '''import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ThreeSumSharpTail

noncomputable def entropy (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

noncomputable def oldSaving (c θ : ℝ) : ℝ :=
  θ * Real.log ((c - 1) / 9) / Real.log 4

noncomputable def sharpSaving (c θ : ℝ) : ℝ :=
  (c * entropy (1 / c) - c * entropy ((1 - θ) / c) - θ * Real.log 9) / Real.log 4

noncomputable def queryExponent (θ : ℝ) : ℝ :=
  (entropy θ + θ * Real.log 9) / Real.log 4

noncomputable def encodingExponent (c : ℝ) : ℝ :=
  (c * Real.log 10 - c * entropy (1 / c) / 2 - (c - 1) * Real.log 3) / Real.log 4

def boxCount (c m d : ℕ) : ℕ :=
  Nat.choose (c * m) (m - d) * 9 ^ (c * m - m + d)

end ThreeSumSharpTail
'''
(ROOT/'Definitions/Def_ThreeSumSharpTail_Analysis.lean').write_text(defs, encoding='utf-8')
pre = 'import Definitions.Def_ThreeSumSharpTail_Analysis\nimport Definitions.Def_TrulySubcubicAPSP_SourceSpecification\n\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\nopen scoped BigOperators\n'
items = [dict(kind='definition', definition_name='ThreeSumSharpTail_Analysis', definition_title='Entropy, box counts, and cost exponents for the sharp-tail analysis', definition=defs,
 natural_language_statement=r'''Defines $H(x)=-x\log x-(1-x)\log(1-x)$ (so $H(0)=H(1)=0$), the old preprocessing saving $\gamma(c,\theta)=\theta\log((c-1)/9)/\log4$, the sharp saving $\gamma_*(c,\theta)=[cH(1/c)-cH((1-\theta)/c)-\theta\log9]/\log4$, the query exponent $q(\theta)=[H(\theta)+\theta\log9]/\log4$, and the encoding exponent $A(c)=[c\log10-cH(1/c)/2-(c-1)\log3]/\log4$. For natural numbers $c,m,d$, defines $\beta_d=\binom{cm}{m-d}9^{cm-m+d}$; later lemmas restrict to $c>10$, $m\ge1$ and $d\le m$. These are auxiliary analytic quantities, not a replacement for the campaign's shared word-RAM or 3SUM definitions. Real logarithms and division are total in Lean; intended domains are supplied by theorem hypotheses.''', source=source+'; Sections 2 and 3.',tags=['3sum','binomial-tails','entropy','complexity'])]

def add(key,title,binders,nl,loc,milestone=True):
    item=dict(kind='theorem',theorem_name='ThreeSumSharpTail.'+key,theorem_title=title,
       formal_statement='theorem ThreeSumSharpTail.'+key+binders+' := by sorry',preamble=pre,
       natural_language_statement=nl,source=source+'; '+loc,tags=['3sum','algorithms','fine-grained-complexity','word-ram'])
    if milestone:
        item['milestone_title']=loc.split(';')[0]+' — '+title
        item['milestone_description']=nl
    items.append(item)

add('binomial_entropy_bounds','Two-sided binomial entropy bounds', ''' (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ r) :
    Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r)) / (r + 1) ≤ (Nat.choose r k : ℝ) ∧
    (Nat.choose r k : ℝ) ≤ Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r))''',
 r'For integers $r\ge1$ and $0\le k\le r$, let $p=k/r$. Then $$\frac{e^{rH(p)}}{r+1}\le\binom rk\le e^{rH(p)}.$$ The endpoints $k=0,r$ are included. This is a standard estimate used by the manuscript, not a novelty claim.', 'Lemma 3.1')
add('sharp_normalized_tail','Sharp normalized binomial tail', ''' (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    ((∑ d ∈ Finset.Icc (⌈θ * (m : ℝ)⌉₊) m, ThreeSumSharpTail.boxCount c m d : ℕ) : ℝ) /
        (ThreeSumSharpTail.boxCount c m 0 : ℝ) ≤
      ((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
        Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ)''',
 r'Let $c>10$ and $m\ge1$ be integers, $0<\theta<0.9$, $L=cm$, $D=4^m$, $t=\lceil\theta m\rceil$, $\beta_d=\binom L{m-d}9^{L-m+d}$ and $M=\beta_0$. Then $$\frac1M\sum_{d=t}^{m}\beta_d\le\frac{cm+1}{1-9/(c-1)}D^{-\gamma_*(c,\theta)}.$$ The ceiling is part of the statement; $t=m$ is included.', 'Lemma 3.2')
add('sharp_saving_strict','Strict improvement of the preprocessing saving', ''' (c θ : ℝ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    0 < ThreeSumSharpTail.oldSaving c θ ∧
    ThreeSumSharpTail.oldSaving c θ < ThreeSumSharpTail.sharpSaving c θ''',
 r'For every real $c>10$ and $0<\theta<0.9$, $$\gamma_*(c,\theta)>\gamma(c,\theta)>0.$$ This compares preprocessing savings at the same parameters. It does not by itself establish a smaller 3SUM running-time exponent.', 'Proposition 3.3')
add('admissible_parameters_solve_3sum','From admissible sharp-tail parameters to the shared 3SUM specification', '''
    (c : ℕ) (θ : ℝ) (a s r : ℚ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (henc : (a : ℝ) * (ThreeSumSharpTail.encodingExponent c + ThreeSumSharpTail.sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < ThreeSumSharpTail.sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent θ)
    (hprime : Real.log 7 / Real.log 2 + 3 * (a : ℝ) / 2 < 3 - (a : ℝ) * s / 2)
    (hbuild : 2 + (a : ℝ) * (1 + (s : ℝ) / 2) < 3 - (a : ℝ) * s / 2)
    (hr : 2 - a * s / 4 < r) :
    EndStatement.ThreeSum.SolvedInTime r''',
 r'''Let $c>10$ be an integer, $0<\theta<0.9$, and let $a,s,r$ be rational with $0<a<1$ and $0<s<1$. Suppose
$$a(A(c)+\gamma_*(c,\theta))<1,\qquad s<\gamma_*(c,\theta),\qquad s<\tfrac12-q(\theta),$$
$$\log_2 7+\tfrac32a<3-as/2,\qquad 2+a(1+s/2)<3-as/2,\qquad r>2-as/4.$$
Then deterministic integer 3SUM satisfies the campaign's exact shared predicate `EndStatement.ThreeSum.SolvedInTime r`. This is the combined consequence of Propositions 4.1 and 5.1, not a verbatim separate proposition in the manuscript. Its proof must construct the word-RAM program and establish correctness and all costs using the inherited algorithms and reductions. No inner-algorithm oracle or correctness assumption is supplied as a hypothesis. The uniform word-width requirement in the shared specification is part of the formalization obligation.''', 'Propositions 4.1 and 5.1; combined consequence')
add('explicit_parameter_certificate','Exact parameter inequalities for exponent 1.999017', ''' :
    (0.05665 : ℝ) * (ThreeSumSharpTail.encodingExponent 21 + ThreeSumSharpTail.sharpSaving 21 0.11202) < 1 ∧
    (0.06945 : ℝ) < ThreeSumSharpTail.sharpSaving 21 0.11202 ∧
    (0.06945 : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent 0.11202 ∧
    Real.log 7 / Real.log 2 + 3 * (0.05665 : ℝ) / 2 < 3 - 0.05665 * 0.06945 / 2 ∧
    2 + (0.05665 : ℝ) * (1 + 0.06945 / 2) < 3 - 0.05665 * 0.06945 / 2 ∧
    (2 - (0.05665 : ℚ) * 0.06945 / 4) = 1.999016414375 ∧
    (1.999017 : ℚ) - (2 - 0.05665 * 0.06945 / 4) = 0.000000585625''',
 r'''For the exact rational parameters $c=21$, $\theta=0.11202$, $a=0.05665$, $s=0.06945$, establish $a(A+\gamma_*)<1$, $s<\gamma_*$, $s<1/2-q$, $\log_2 7+3a/2<3-as/2$, and $2+a(1+s/2)<3-as/2$. Also establish the exact equalities $$2-as/4=1.999016414375,\qquad 1.999017-(2-as/4)=0.000000585625.$$ All decimal constants denote exact rationals (coerced to reals in the analytic inequalities). The source's rational interval checks are reproducible evidence; proving this Lean statement remains a formalization task.''', 'Section 6.2; parameter certificate used in Theorem 1.1')
add('threeSum_1999017','Deterministic integer 3SUM in O(n^1.999017) word-RAM steps', ''' :
    EndStatement.ThreeSum.SolvedInTime 1.999017''',
 r'''For each fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural number $b$, and a step bound $T:\mathbb N\to\mathbb N$. For every $n$, input $x:\{0,\ldots,n-1\}\to\mathbb Z$ with $|x_i|\le n^\kappa$, and every $W\ge b(\operatorname{Nat.log2}(n)+1)$, the program halts within $T(n)$ steps and accepts exactly when three pairwise distinct indices have sum zero. Equal values at distinct indices are allowed; no witness is required; inputs of size less than three are rejected.

The exact time requirement is $\exists K\in\mathbb N\;\forall n\ge2,\ T(n)^{1000000}\le K n^{1999017}$, equivalent to $T(n)=O(n^{1.999017})$. The target instantiates the campaign template without changing its definitions.

Source: Theorem 1.1 of Xu's sharp-tail manuscript. The manuscript states $\kappa\ge1$ and a sufficiently large logarithmic word width; the campaign additionally makes uniformity over all larger widths explicit. The case $\kappa=0$ follows from the $\kappa=1$ bound for $n\ge1$, with $n=0$ handled separately. The formal development must justify this interface adaptation. The improved bound is a proposed formalization target, not an already Lean-certified result.''', 'Theorem 1.1; shared campaign interface adaptation',False)
items[-1]['preamble']=before['items'][1]['preamble']
(HERE/'items.json').write_text(json.dumps(items,ensure_ascii=False,indent=2),encoding='utf-8')
combined = pre+'\n\n'.join(i['formal_statement'] for i in items if i['kind']=='theorem')+'\n'
(ROOT/'Theorems/Thm_ThreeSumSharpTail_Draft.lean').write_text(combined,encoding='utf-8')
# Only code and imports for independent read-back; no source or intended meaning.
(HERE/'audit-code.json').write_text(json.dumps([{'key': i.get('definition_name',i.get('theorem_name')), 'code':i.get('definition',i.get('formal_statement')), 'preamble':i.get('preamble','')} for i in items],ensure_ascii=False,indent=2),encoding='utf-8')
indexfile=ROOT/'missions/index.json'
index=json.loads(indexfile.read_text(encoding='utf-8'))
if not any(m['slug']=='3sum-sharp-tail' for m in index['missions']):
    index['missions'].append(dict(slug='3sum-sharp-tail',title='3SUM: sharp binomial tail and exponent 1.999017',family='algorithms',handoff='missions/3sum-sharp-tail/status.md',scratch=None))
    indexfile.write_text(json.dumps(index,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
readme=ROOT/'missions/README.md'
text=readme.read_text(encoding='utf-8')
if '(3sum-sharp-tail/status.md)' not in text:
    readme.write_text(text+'\n- [3SUM sharp-tail draft](3sum-sharp-tail/status.md) — [agent instructions](3sum-sharp-tail/AGENTS.md)\n',encoding='utf-8')
print(f'Prepared {len(items)} draft items; existing foundation reference retained.')
