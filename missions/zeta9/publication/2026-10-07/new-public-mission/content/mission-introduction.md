## Motivation and history

The **Riemann zeta function** at a real number $s>1$ is the convergent series
$\zeta(s)=\sum_{k=1}^{\infty}k^{-s}$. Number theorists studying its special values
distinguish between proving that a family contains irrational numbers and
determining the arithmetic nature of one specified member. This mission asks
for a proof that $\zeta(9)$ is irrational. The target remains unproved in this
development; the supporting results below do not close it.

Two landmarks explain the distinction:

- **2000:** Rivoal proved that infinitely many odd zeta values are irrational,
  through a dimension bound for their rational span.
  [Rivoal's paper](https://arxiv.org/abs/math/0008051).
- **2002; published 2004:** Zudilin proved that at least one of
  $\zeta(5),\zeta(7),\zeta(9),\zeta(11)$ is irrational. This disjunction does
  not identify $\zeta(9)$.
  [Zudilin's paper](https://arxiv.org/abs/math/0206176).
- **2026, this development:** explicit coefficient maps, weighted lattices,
  arithmetic estimates, and alternative constructions were assembled in
  [research notes and source supplements](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02).
  Separately, a saved 4 October audit recorded 51 supporting proofs as
  Accepted and public Proved. This is a dated supporting checkpoint, not an
  irrationality proof.

## Setting

An **integer linear form** in the target value is $b+a\zeta(9)$, where
$a,b\in\mathbb Z$. It is useful for irrationality only when its actual value
is nonzero and tends to zero along an infinite sequence. A pair is
**primitive** when $\gcd(|a|,|b|)=1$; its direction identifies $(b,a)$ with
$(-b,-a)$.

The principal construction uses even integers $n\ge2$ and the rational function

$$R_n(t)=(n!)^7
  \frac{\prod_{i=1}^{n}(t-i)(t+n+i)}
       {\prod_{j=0}^{n}(t+j)^9}.$$

For a polynomial $W(X)=\sum_{r=0}^{4}w_rX^r$ with rational coefficients, set
$u_n(t)=t(t+n)$ and $L_n(W)=\sum_{k=1}^{\infty}R_n(k)W(u_n(k))$.
Its actual **partial fractions** and **harmonic sums** determine rational coefficients
in the exact identity

$$L_n(W)=B_n(W)+\rho_{3,n}(W)\zeta(3)+\rho_{5,n}(W)\zeta(5)
                   +\rho_{7,n}(W)\zeta(7)+\rho_{9,n}(W)\zeta(9).$$

The **coefficient map** sends $W$ to this ordered row of five rational
coefficients. The **matrix** $F_n$ has row $r$ equal to the coefficient row of
$X^r$, for $0\le r\le4$. These are coefficients constructed from the actual
rational function; their definition does not assume independence of odd zeta
values. The map is bijective over $\mathbb Q$ for every even $n\ge2$ in the
completed supporting theorem *The actual five-dimensional rational coefficient
map is bijective*. This later theorem is separate from the dated source
packages.

The **integer-output lattice** consists of the rational polynomial-coordinate
rows

$$\mathcal L_n=\{(b,0,0,0,a)F_n^{-1}:a,b\in\mathbb Z\}.$$

Its **weighted norm** is the Euclidean norm after multiplying coordinates by
$(1,n^2,n^4,n^6,n^8)$. A shortest nonzero row has a primitive integer output;
a fixed convention resolves ties. An integer output can have a rational
polynomial preimage. Integer polynomial coefficients and their denominator
cost require additional arithmetic statements.

## Formalization targets

The stable goal is

$$\boxed{\zeta(9)\notin\mathbb Q.}$$

The goal imposes no chosen decay constant or prescribed construction. The
coefficient-map route supplies supporting targets; a complete independent
construction of nonzero integer linear forms tending to zero would also
settle the goal.

The **joint-margin condition J** in the research notes asks for a fixed
positive exponent margin on infinitely many even indices in the actual
weighted-lattice and arithmetic diagnostics. It remains mathematically open.
Under the written volume and transport results, it is an equivalent exit to
the target and to failure of eventual fixation of the shortest primitive
output direction. The stronger **shape condition S** is sufficient with the
written volume estimate; it is not an additional necessary hurdle.
[Precise conditions and dependencies](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02).

## Significance

A complete proof would determine the arithmetic nature of one specified odd
zeta value. The formal development also produces reusable links between
rational-function coefficients, absolutely convergent series, polynomial
inverse images, and primitive integer outputs.

Completed machine-checked supporting stages include harmonic-denominator
clearing and stability, finite-prime arithmetic, the actual short-zero
coefficient's signed lower bound and nonvanishing, and unconditional harmonic
denominator rates using an actual prime-number-theorem dependency.
The coefficient route has complete proofs of highest-pole identities, all
nine local orders, full local-array injectivity, global partial fractions,
reflection and cancellation, finite harmonic identities, absolute summability,
and the exact infinite linear form. Its genuine aggregate map is bijective
over rational quartics for even $n\ge2$, with a unique rational preimage of
every rational target. The actual fifteen-coordinate connection system also
has unique polynomial solutions for every $n\ge1$. The supporting results
*The actual inverse multiplier has its prescribed sum and absolute convergence*
and *The five original connection systems have unique bounded rational solutions*
state these later conclusions with their exact domains.

The 7 October 2026 authenticated readback reconfirmed the 51 complete accepted
supporting proofs and their public Proved statements. The irrationality goal
remained Open. The three separately published explicit-matrix statements were
also Open; local Matrix proofs and completed kernel-and-inverse results do not
imply platform acceptance of those separate statements. These are statuses of
existing supporting results, not a completion count for this new mission.

Public supplements provide independently rebuilt sources for nine complete
proofs and for the later coefficient-sign and unconditional denominator-rate
developments. Each package records its precise scope and standard foundational
axioms. They do not contain a proof of the root goal.
[Nine-proof supplement](https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/zeta9-formal-proofs-2026-10-02.zip),
[advanced source supplement](https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/zeta9-advanced-proofs-2026-10-02.zip),
[independent source-package review](https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/ADVANCED-PROOFS-INDEPENDENT-REVIEW.json).

## Difficulty

Small real values alone do not settle irrationality: an integer form may be
exactly zero. Under a rationality assumption, the shortest primitive output
can eventually follow the unique integer zero relation. The existing volume
and approximation estimates do not exclude that behavior. Finite changes of
direction, large matrix determinants, or a few certified small nonzero forms
do not establish the required infinite assertion.
[Direction frontier and boundaries](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02).

Alternative routes retain different gaps. Growing-dimensional positive Gram
constructions have positive exponentially decreasing real errors but lack
control of the full reduced denominators. A differentiated rational-sum
construction isolates $\zeta(9)$ but has polynomial endpoint leakage; its
eightfold-zero repair removes that leakage and still needs eventual
nonvanishing, the actual analytic rate, and primitive-content estimates.
These are alternatives, not conditions that must all be solved.
[Alternative constructions and exact boundaries](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02).

## Formalization scope

The Lean goal applies `Irrational` to the real part of Mathlib's complex
`riemannZeta` at $9$. The coefficient construction fixes rational quartics,
the output order $(B,\rho_3,\rho_5,\rho_7,\rho_9)$, and even $n\ge2$ for
the inverse and infinite identity. Connection results retain their own
$n\ge1$ domain and regular-point hypotheses. Saturated integer kernels,
positive common denominators, **Smith factors**, primitive normalization, weighted
norms, and shortest nonzero vectors must use the actual objects in the notes.
An arbitrary replacement map, zero witness, or hypothesis already asserting
the required transport or infinite margin cannot discharge these targets.

Four principal formalization work packages remain:

1. **Parameter transport:** complete the genuine five-output and infinite-sum
   transport. Proved polynomial connection systems and rational-function
   differences do not alone constitute this result; the proposed full output
   assembly is not yet a verified theorem.
2. **Integer normalization, heights, and content:** prove the actual integral
   structures and denominator bounds. Rational bijectivity of $F_n$ does not
   supply those arithmetic bounds.
3. **Uniform analytic estimates A:** formalize the written moment asymptotics,
   infinite-tail bounds, and error estimates uniform in varying quartic
   coefficients. Elementary phase lemmas alone do not establish this package.
4. **Arithmetic volume estimates V:** formalize the written prime budgets,
   Smith data, saturated-kernel geometry, and resulting volume asymptotics.
   The written volume proof does not establish J.

These four packages distinguish remaining Lean work from the separate missing
mathematical input for J. Rational matrices, integer modules, formal power
series, summability, asymptotic analysis, and geometry of numbers are reusable
infrastructure. Faithful formalizations, independent audits, and new
mathematical approaches are welcome.
[Written research record](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02).

## Selected references

- T. Rivoal, *La fonction zêta de Riemann prend une infinité de valeurs
  irrationnelles aux entiers impairs*, C. R. Acad. Sci. Paris Sér. I Math.
  331 (2000), 267–270. [arXiv:math/0008051](https://arxiv.org/abs/math/0008051).
- W. Zudilin, *Arithmetic of linear forms involving odd zeta values*,
  Journal de Théorie des Nombres de Bordeaux 16 (2004), 251–291;
  preprint 2002. [arXiv:math/0206176](https://arxiv.org/abs/math/0206176).
- *Zeta(9) research notes, source, and verification records*, research archive,
  2 October 2026, with separately dated formal proof supplements.
  [Public release](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02).
