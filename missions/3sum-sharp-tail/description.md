## Why sharpen the integer 3SUM exponent?

**3SUM** asks whether an input sequence contains three entries at different positions whose sum is zero. The classical quadratic running time makes it a benchmark for fine-grained algorithm design: even a small fixed improvement in the exponent changes its asymptotic complexity. The setting here is polynomially bounded integers and a deterministic word RAM; the input-size exponent, rather than an experimental speedup, is the quantity being studied.

[Alman and Vassilevska Williams (2026)](https://arxiv.org/abs/2610.06783v1) give a deterministic truly subquadratic integer 3SUM algorithm through thin matrix products and reductions involving Exact Triangle. [Xu's manuscript, *Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis*](https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3), dated 13 October 2026, refines the analysis of that framework. Its claimed bound is the formalization target here. The Hexagon link identifies the author's submission page, which may require authentication; it is not presented as a public article identifier or evidence of peer review.

## Inputs, machine model, and analytic quantities

An input of size $n$ is a function $x:\{0,\ldots,n-1\}\to\mathbb Z$. For a fixed natural number $\kappa$, every entry obeys $|x_i|\le n^\kappa$. Acceptance means that there are pairwise distinct indices $i,j,k$ with $x_i+x_j+x_k=0$. Repeated values at different positions are allowed. This is a decision problem, so the algorithm need not return a witness triple.

The **word-RAM specification** is the campaign's existing `EndStatement` definition, imported from its [foundation mission](https://prove2.me/missions/487064c8-0ffb-4779-802b-6824b289a73c). For each fixed $\kappa$, one finite deterministic program, one word-width threshold constant, and one time-bound function must work for all input sizes and all word widths above that threshold. Words have finite signed interpretations; arithmetic, indirect memory access, branching, acceptance, and rejection are defined operationally. The result concerns this exact model.

For the supporting analysis, let $H(u)=-u\log u-(1-u)\log(1-u)$, with endpoint values $H(0)=H(1)=0$. All logarithms are natural. For an integer $c>10$, a positive integer $m$, and $0<\theta<0.9$, set $L=cm$, $D=4^m$, $t=\lceil\theta m\rceil$, and

$$\beta_d=\binom L{m-d}9^{L-m+d},\qquad M=\beta_0.$$

The **sharp preprocessing saving**, **query exponent**, and **encoding exponent** are

$$\gamma_*(c,\theta)=\frac{cH(1/c)-cH((1-\theta)/c)-\theta\log9}{\log4},$$
$$q(\theta)=\frac{H(\theta)+\theta\log9}{\log4},\qquad A(c)=\frac{c\log10-cH(1/c)/2-(c-1)\log3}{\log4}.$$

These auxiliary definitions describe costs; they neither redefine 3SUM nor assume the existence of a fast algorithm.

## Formalization targets

The campaign goal is the exact fixed bound

$$\texttt{EndStatement.ThreeSum.SolvedInTime}\;1.999017.$$

The first supporting milestone is the two-sided binomial entropy estimate. The second is the manuscript's normalized tail bound

$$\frac1M\sum_{d=t}^m\beta_d\le\frac{cm+1}{1-9/(c-1)}D^{-\gamma_*(c,\theta)}.$$

A further milestone establishes strict improvement over the earlier preprocessing saving $\gamma(c,\theta)=\theta\log((c-1)/9)/\log4$ at fixed parameters. The algorithmic milestone combines the manuscript's Propositions 4.1 and 5.1: admissible sharp-tail parameters must yield a program satisfying the shared 3SUM specification, not merely a numerical inequality.

The final supporting milestone certifies the exact choice

$$c=21,\qquad\theta=0.11202,\qquad a=0.05665,\qquad s=0.06945.$$

It includes the preprocessing, query, encoding, prime-selection, and instance-construction inequalities, together with

$$2-as/4=1.999016414375,\qquad1.999017-(2-as/4)=0.000000585625>0.$$

Every terminating decimal denotes an exact rational number. The target is the fixed big-$O$ exponent 1.999017; the smaller cutoff is accompanied by residual asymptotic losses in the manuscript and is not asserted as the same fixed bound.

## What completing this mission would establish

A complete proof would certify the manuscript's improved integer 3SUM bound in the campaign's common machine model. The gain is an analysis refinement of the inherited algorithm and reductions. It does not claim a new algorithmic framework, optimal parameters, global optimality, or priority over all other work.

The manuscript also gives an auxiliary $O(n^{1.999073})$ bound by retuning the previous estimate. That weaker result is background, not this mission's campaign value. The existing upstream formalization is prior work; it does not automatically certify either refinement. The supplied rational interval verifier checks the parameter inequalities, but those checks alone do not prove a word-RAM running-time theorem. The main goal and the newly drafted supporting statements remain open Lean proof obligations.

## Where the difficulty lies

A better tail estimate is insufficient unless every other cost remains within the final budget. Shared encoding work, all queries, deterministic prime selection, witness scanning, and instance construction must be included. The word-size and address bounds must remain valid after changing parameters. Ceiling operations, restricting $D$ to powers of four, and bounded-size exceptions must also be handled.

The central formalization burden is the connection between the analytic estimates and an actual deterministic program. Assuming an oracle with the desired running time would remove that burden and would not establish the stated target. Likewise, checking a finite range of sizes or a floating-point optimizer's output cannot establish the universal algorithmic statement.

## Formalization scope and conventions

The environment is Lean 4.33.1 with Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The foundation reference and the campaign goal's import are retained. Supporting definitions use real logarithms, real powers, natural binomial coefficients, finite sums, and a natural ceiling. Domain hypotheses exclude invalid entropy-tail regimes; endpoint binomial cases are included explicitly.

For $r=1999017/1000000$, the shared time predicate means that there exists $K\in\mathbb N$ such that $T(n)^{1000000}\le K n^{1999017}$ for every $n\ge2$. Correctness and termination still cover every input size, including $n<3$. The manuscript's $\kappa\ge1$ convention must be extended to the campaign's $\kappa=0$ case, and its word-size analysis must justify uniform correctness at every sufficiently large word width. Both are explicit interface obligations.

Reusable contributions include entropy and tail estimates, rigorous logarithm enclosures, and parameterized cost-to-program results. Existing compatible library results should be reused where available. The manuscript and metadata were prepared with AI assistance; this mission makes no claim of completed human review or completed formal verification of the improved bound.

## Selected references

- Yuxuan Xu, *Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis*, manuscript, 13 October 2026. [Author-supplied Hexagon submission page](https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3). Target: Theorem 1.1; supporting analysis: Sections 3–6.
- Josh Alman and Virginia Vassilevska Williams, *Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*, arXiv preprint, 2026. [arXiv:2610.06783v1](https://arxiv.org/abs/2610.06783v1). Inherited ingredients: Section 4, Lemma 29, Theorem 30, Corollary 31, and the deterministic reductions cited in Xu's Section 2.
- Anthropic, *Truly Subquadratic 3SUM and Truly Subcubic APSP: a Lean 4 formalization*, source repository, 2026. [Pinned source at commit e1a4e6508154ea59f030480661590a9fe3018011](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp). Its `EndStatement.lean` supplies the shared specification, not a proof of this mission's new exponent.
