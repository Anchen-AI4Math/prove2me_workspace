## Motivation and history

The **Riemann zeta function** at a real number $s>1$ is the convergent
series $\zeta(s)=\sum_{k=1}^{\infty}k^{-s}$. This mission asks whether the
specified value $\zeta(9)$ is irrational. For number theorists studying
special values, the distinction between proving that some member of a
family is irrational and identifying one particular member is substantial.
Rivoal proved that infinitely many odd zeta values are irrational
([Rivoal, 2000](https://arxiv.org/abs/math/0008051)). Zudilin proved that at
least one of $\zeta(5),\zeta(7),\zeta(9),\zeta(11)$ is irrational
([Zudilin, 2004](https://arxiv.org/abs/math/0206176)). Neither statement
isolates $\zeta(9)$. The present mission remains unfinished; its research
reductions and verified finite computations are not a proof of the target.

## Setting

An **integer linear form** in the target value is $b+a\zeta(9)$, with
$a,b\in\mathbb Z$. A pair is **primitive** when $\gcd(|a|,|b|)=1$; its
direction identifies $(b,a)$ and $(-b,-a)$.

The main construction is indexed by even integers $n\ge2$. Its rational
summation functional sends a quartic polynomial $W$ to a coefficient row
in the ordered basis $(1,\zeta(3),\zeta(5),\zeta(7),\zeta(9))$. The fixed,
invertible rational matrix $F_n$ records this coefficient map. Exact
formulas for the summand and matrix are part of the
[research release](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02);
$F_n$ is this concrete map, not an arbitrary matrix chosen for a theorem.
The **integer-output lattice** is

$$\mathcal L_n=\{(b,0,0,0,a)F_n^{-1}:a,b\in\mathbb Z\}.$$

Its **weighted norm** is the ordinary Euclidean norm after multiplying
the five polynomial-coefficient coordinates by
$(1,n^2,n^4,n^6,n^8)$. A shortest nonzero vector has a primitive output
pair; a fixed choice resolves any ties.

For the arithmetic diagnostics, let $K_n$ be an integer row basis of the
**saturated kernel** where the three lower odd-zeta coefficients vanish.
Choose a positive common denominator $D_n$ of $F_n$, and let $J_n$ be
the two-column integer image of $D_nK_nF_n$ in its first and last
coordinates. Write its **Smith factors** as $s_{1,n}\mid s_{2,n}$, set
$d_n=\operatorname{lcm}(1,\ldots,n)$ and
$g_n=\gcd(s_{2,n}/s_{1,n},d_n^2)$. The **congruence lattice** consists of
$zK_n$ with $z\in\mathbb Z^2$ and $z(J_n/s_{1,n})\equiv0\pmod{g_n}$.
Let $\Delta_n$ be the weighted area of $K_n$ and $\mu_n>0$ the shortest
nonzero weighted length in this congruence lattice.

## Formalization targets

The stable goal is

$$\boxed{\zeta(9)\notin\mathbb Q.}$$

The main research exit is to exclude eventual fixation of the shortest
primitive output direction. Define the diagnostics

$$B_n=\frac{\log(D_n/s_{1,n})+\tfrac12\log\Delta_n-\tfrac12\log g_n}{n},
\qquad
\sigma_n=\frac{\tfrac12\log(g_n\Delta_n)-\log\mu_n}{n}.$$

The **joint-margin condition J** asserts that some $\varepsilon>0$ gives
$B_n+\sigma_n\le\tau-\varepsilon$ for infinitely many even $n$, with the
existing analytic threshold $\tau=2641/250=10.564$. The **volume condition
V**, $\limsup B_n<\tau$ along even $n$, now has a written proof. Under
this result and the current written transport results, the target, J, and failure of
eventual direction fixation are equivalent. This equivalence identifies
the unresolved step; it does not solve it. The stronger **shape condition
S**, $\sigma_n\to0$ along even $n$, is sufficient together with V,
and is not a separate necessary hurdle. The exact
statements and their dependencies are in the
[release](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02).

## Significance

A complete proof would identify the arithmetic nature of one specified
odd zeta value, rather than another disjunction. A faithful formal
development would also make the passage between rational coefficient
maps, primitive integer outputs, lattice minima, and nonzero linear forms
explicit. These components can support other special-value constructions.

The recent research has established written bounds for the actual volume,
arithmetic budget, and transport, as well as new all-parameter identities
and exclusion ranges for alternative positive-moment constructions.
Independent mathematical review and exact offline certificates support
these results; the recent proofs have not been checked in Lean. Their
statements, complete source, counterexamples, and reproducible verification
records are collected in the
[dated release](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02).
Formal acceptance of general supporting lemmas does not establish their
concrete infinite hypotheses.

## Difficulty

The analytic construction supplies very small real values, but a small
value does not suffice if its integer form is zero. Under a rationality
assumption, the shortest primitive direction can eventually become the
exact integer zero relation. Current approximation and volume estimates
are compatible with that possibility. A lower bound or transport identity
must therefore exclude this behavior for the actual arithmetic sequence.
Finite direction changes, narrow rational intervals, and large determinant
heights do not prove the required infinite assertion. The new least-
denominator projection improves certified samples, but its needed parent-
denominator growth is itself equivalent to irrationality
([current progress](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02)).

Alternative routes have their own distinct gaps. A growing-dimensional
positive Gram construction gives a strictly positive isolated linear form
with exponentially decreasing real error, but its full reduced denominator
is uncontrolled. A differentiated Apéry-type rational sum isolates
$\zeta(9)$ and has a proved positive polynomial endpoint asymptotic; an
eightfold-zero variant removes that leakage but still needs asymptotic
nonvanishing, analytic decay, and primitive-content estimates. These are
alternative approaches, not conditions that must all be solved. Any valid
construction of nonzero integer forms tending to zero would suffice
([proofs and precise boundaries](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02)).

## Formalization scope

The Lean target applies `Irrational` to the real part of Mathlib's complex
`riemannZeta` at $9$. The real part agrees with the positive real series
above. Integer pairs, positive denominators, primitive normalization,
even indices, and shortest nonzero vectors must retain the stated
conventions; zero witnesses or an arbitrary replacement coefficient map
cannot discharge the concrete goal.

The current formal record reports 44 milestones, 15 theorem links, and
13 completed entries. These counts describe the recorded supporting
scope, not a completed irrationality proof. The root target remains open.
The concrete matrix, saturated kernel, Smith data, weighted minima, and
their asymptotic statements still require faithful Lean definitions and
proofs. Needed infrastructure includes rational matrices, integer modules,
Smith normal form, summable series, asymptotic estimates, and real or
complex special functions. Reusable contributions to these foundations,
audits of the exact constructions, and independent mathematical approaches
are welcome. The release distinguishes mathematical proof, finite exact
certification, and formal theorem status.

## Selected references

- T. Rivoal, *La fonction zêta de Riemann prend une infinité de valeurs
  irrationnelles aux entiers impairs*, C. R. Acad. Sci. Paris Sér. I Math.
  331 (2000), 267–270. [arXiv:math/0008051](https://arxiv.org/abs/math/0008051).
- W. Zudilin, *Arithmetic of linear forms involving odd zeta values*,
  Journal de Théorie des Nombres de Bordeaux 16 (2004), 251–291.
  [arXiv:math/0206176](https://arxiv.org/abs/math/0206176).
- Zeta(9) research mission, *Research notes, source, and verification
  records*, public research archive, 2 October 2026.
  [Dated release](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02).
