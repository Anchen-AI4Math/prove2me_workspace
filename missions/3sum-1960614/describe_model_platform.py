"""Academic metadata for the two reusable model lemmas and existing root proof."""
import json
from pathlib import Path
VER=Path(__file__).resolve().parent/'verification'
path=VER/'model-platform-manifest.json'
manifest=json.loads(path.read_text(encoding='utf-8'))
metadata={
 'bound_of_witnesses':(
  'Four-charge elimination for the expansion-232 analytic model',
  r'''Let $e>0$ be the block fraction, $b$ the band exponent, $S$ the saving, $t$ the switch point, $\tau$ the terminal threshold, $\rho$ the ratio parameter, and $R$ a common upper bound on the model charges. Assume the published predicate $\operatorname{ModelFeasible}(232,e,b,S,t,\tau,\rho,R)$.

Let $E_0,\kappa_0,\rho_0,s,G,H$ be the exact rational witnesses in the shared definitions. Suppose $E_0\le E(232)$, $\kappa_0\le\kappa(232)$, $\rho_0\le\rho$, and that the two sides of the switch obey
$$t\le s\Longrightarrow\gamma(232,t)\le G,\qquad s\le t\Longrightarrow H\le h(t),$$
where $h$ is binary entropy in base two. Then
$$R>1.96061349120.$$
Only the fixed analytic model is bounded; this is not a lower bound for arbitrary 3SUM algorithms.''',
  r'''Put $\delta=2-R$. If $R\ge2$, the conclusion is immediate. Otherwise extract the box, encoding, initial-cover and recursive-filter charges from the model. The lower witnesses for $E$, $\kappa$ and $\rho$ give a linear constraint on $e b$ and $\delta$.

Split at $t=s$. On the left use the upper bound on $\gamma$ and the switch constraint; on the right use the lower entropy bound and the initial-cover charge. Both yield $\delta\le Ue$ for the exact rational saving cap $U$. Combining this with the encoding charge eliminates $e$ through the positive coefficient $C=(1-2\rho_0)E_0-(1/2-\kappa_0-\rho_0)$. An exact rational comparison gives the displayed strict endpoint.'''),
 'witness_logs':(
  'Six exact logarithmic intervals at the model witnesses',
  r'''Fix
$$s=\frac{252561863698173}{6250000000000000},\qquad u=\frac{859960785302793}{5000000000000000}.$$
For the six positive rational arguments
$$32s,\quad2(1-s),\quad1+s/231,\quad8u,\quad2(1-u),\quad1+u/231,$$
the natural logarithm lies in each corresponding exact closed rational interval stated in the theorem. All endpoints are fixed rationals; the intervals have width $10^{-22}$. There are no numerical-oracle or rounding hypotheses. These enclosures supply the split-point entropy and collision bounds and the ratio witness used in the model lower bound.''',
  r'''For each rational argument $y$, set $z=(y-1)/(y+1)$ and use Mathlib's rigorous finite-series enclosure
$$2\sum_{i<n}\frac{z^{2i+1}}{2i+1}\le\log y\le2\left(\sum_{i<n}\frac{z^{2i+1}}{2i+1}+\frac{z^{2n+1}}{1-z^2}\right).$$
All six points satisfy $0\le z<1$. The respective term counts are $18,26,4,18,24,5$. Exact rational arithmetic compares both enclosure endpoints with the displayed target endpoints, so no floating-point calculation enters the proof.'''),
 'complete_lower_bound':(
  '', '',
  r'''The accepted encoding certificate gives the required lower bounds for $E(232)$ and $\kappa(232)$. At the fixed ratio point $u$, the six new logarithm intervals and the accepted base logarithm intervals prove
$$\rho_0(1+\gamma(232,u))<h(u).$$
The model's uniform entropy constraint and positivity of $1+\gamma$ therefore force $\rho_0\le\rho$.

The same exact intervals bound $\gamma(232,s)$ from above and $h(s)$ from below. Monotonicity of the two functions on $[0,1/2]$ extends those point bounds to the two sides of the split. The four-charge elimination theorem then gives $R>1.96061349120$. The source abbreviation lowerTarget is definitionally the literal rational endpoint in the existing platform goal; a separate local Lean check verifies that unchanged contract.''')}
for record in manifest['theorems']:
    key=record['name'].rsplit('.',1)[1]
    title,natural,explanation=metadata[key]
    record['explanation']=explanation
    if not record.get('existing_theorem_id'):
        record['payload']={'theorem_name':record['name'],'theorem_title':title,
          'preamble':record['preamble'],'formal_statement':record['formal_statement'],
          'natural_language_statement':natural,'source':record['source'],
          'tags':[manifest['project_tag'],'3sum','exact-certificates'],'env':manifest['environment']}
manifest['validation_complete']=False
path.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('Prepared metadata for two support nodes and the existing model root.')
