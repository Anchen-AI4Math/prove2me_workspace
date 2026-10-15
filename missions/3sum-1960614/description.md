## Why improve the deterministic integer 3SUM exponent?

**3SUM** asks whether three entries at distinct positions in an integer input sum to zero. Its familiar quadratic algorithm makes it a benchmark for studying how much arithmetic structure can reduce the cost of an exhaustive search. The relevant comparison is the exponent of input size in a precisely specified machine model. An improvement to that exponent is an asymptotic statement; it need not provide better measured running times at accessible input sizes.

[Alman and Vassilevska Williams, 2026](https://arxiv.org/abs/2610.06783v1) developed a deterministic truly subquadratic framework for polynomially bounded integer 3SUM. The [c0ldzy17 source snapshot](https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/METHOD.md), dated 11 October 2026, develops a subsequent deterministic construction with a formally stated 1.962 target. The author-supplied certificate package `3sum_certificate_1p960614_v3`, dated 14 October 2026, studies a further parameter and switch refinement. It contains mathematical arguments and exact rational checks, and explicitly leaves the complete modified machine-program theorem unproved. This mission studies that remaining extension together with its supporting certificates.

## Inputs, word instructions and analytic quantities

An input of size $n$ is an integer-valued function on the positions $0,\ldots,n-1$. For each fixed natural number $\kappa$, every value has absolute value at most $n^\kappa$. A YES instance has pairwise distinct positions $i,j,k$ satisfying $x_i+x_j+x_k=0$. Equal values at different positions are allowed. The problem asks for a decision, so a successful algorithm need not return the positions. Inputs of size less than three are NO instances.

The **word RAM** is the existing [campaign foundation specification](https://prove2.me/missions/487064c8-0ffb-4779-802b-6824b289a73c). A program is a finite list of instructions for constants, arithmetic, direct and indirect memory access, branching, acceptance and rejection. Words have a fixed width and a signed integer interpretation. For each fixed $\kappa$, one program, one word-width constant and one time function must work for every input size and every sufficiently large word width. The mission retains that specification without introducing an alternative computation model.

The supporting **binary entropy** is measured in bits:

$$H(t)=\frac{-t\log t-(1-t)\log(1-t)}{\log2},\qquad H(0)=H(1)=0.$$

For an integer expansion $c\ge3$, write

$$E_c=\frac c2H(1/c),\quad \kappa_c=2cH(1/(2c))-cH(1/c)-1,\quad \gamma_c(t)=cH(1/c)-cH((1-t)/c).$$

These are analytic quantities used to describe local encoding and reporting costs. The source's twelve charges also depend on a representation-scale parameter $e$, a band shift $b$, a box saving $S$, an initial threshold $\theta$, a terminal fraction $\tau$, and a uniform entropy coefficient $\rho$.

## Formalization targets

The campaign goal is the exact proposition

$$\texttt{EndStatement.ThreeSum.SolvedInTime}\;(1.960614).$$

For $1.960614=980307/500000$, its time requirement is

$$\exists K\in\mathbb N\;\forall n\ge2,\quad T(n)^{500000}\le K n^{980307}.$$

Correctness and termination still cover all input sizes. The integer-size exponent includes $\kappa=0$, and the same program must be correct for every word width above its specified threshold.

The primary certificate uses $c=232$ and the rational quartic

$$P(t)=7.85174904t+0.72447023t^2+0.24044466t^3+0.12022459t^4.$$

Supporting targets establish its validity on $[0,1/2]$, its derivative and tangent bounds, and the uniform inequality $H(t)<0.27905030(1+P(t))$. The fixed parameters are $e=0.203889696$, $b=-0.062656016$, $S=0.193175570$, $\theta=0.040409899$, and $\tau=13/20$. The parameter theorem bounds every one of the twelve costs strictly below $1.96061388<1.960614$. Integer scheduling and general local-cover identities are separate milestones. A further independent milestone proves $R>1.96061349120$ for the explicitly defined relaxed fixed-expansion cost model. That model bound concerns its admissible parameter tuples; it is not a lower bound for 3SUM itself.

## What these results establish

The supplied certificate demonstrates that a quartic switch already suffices for the proposed 1.960614 cost target. It also separates a uniform analytic inequality from a numerical experiment: the statement quantifies over the full closed interval. Its finite scheduling statement uses integer comparisons and accounts for the rounding error at every admissible level, rather than requiring executable logarithms.

Formalization adds checked statements about these continuous and finite objects and a reusable dependency structure. The full campaign goal requires an additional result: the actual modified program must obey the certified costs, and its operational correctness must reach the foundation specification. The [upstream parameter certificate](https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Parameters.lean) likewise distinguishes its exponent ledger from its separate implementation obligations. An exact rational checker passing is evidence for the numerical certificates; it does not establish the full new machine theorem.

## Why the program extension remains substantive

Changing expansion from 256 to 232 changes the local universe and the vertex, output and degree counts together. The representation scale, band denominator and polynomial switch also change. Consequently, the original fixed-parameter runtime result cannot simply be invoked after replacing a few numerical constants. The new local construction, global encoding, sparse queries, reporting and arithmetic operations must share consistent parameters and a complete cost account.

The small gap between the principal cost cap and the target must absorb the proved subpolynomial overheads, including exceptional-size handling and the conversion to word instructions. The **machine bridge** is therefore an open theorem in this mission. Its statement has no assumed solver callback or unproved runtime contract. The fixed-model lower-bound milestone is an independent analytic root, and is not used to justify a faster algorithm.

## Formalization scope and source boundaries

The campaign pins Lean 4.33.1 and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. Entropy and its derived quantities are real-valued; the final exponent is rational; finite subset counts and cleared switch comparisons use natural numbers. Theorems explicitly restrict logarithmic arguments and denominators to their intended domains. Natural-number subtraction in the switch is used only below the final level, with positive even microblock size.

The local-cover milestone covers every natural $c\ge3$ and positive half-block size. The cost-model milestone quantifies over all tuples satisfying its written assumptions and includes a whole-interval entropy constraint. Neither finite testing nor a floating-point optimizer substitutes for these universal statements. The initial package includes no Lean proof of the new machine goal, and the mission does not represent it as an established record.

The underlying algorithms and formal infrastructure retain their attribution to Alman and Vassilevska Williams; Björklund, Husfeldt, Kaski and Koivisto; Swapnil Jain; c0ldzy17; Anthropic; Jihoon Hyun; and Lean/Mathlib, as documented by the upstream source. The certificate development and this formalization use AI assistance. Scientific priority and global optimality are outside the mission's claims.

## Selected references

- Author-supplied *3SUM: Positive-Coefficient Entropy Switch, 1.960614 Cost Certificate and Fixed-Model Lower Bound*, certificate package v3, 14 October 2026. Exact source: `3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md`, Sections 0–8; `certificates/c232_quartic.json`; `verify_certificate.py`. This is a supplied research artifact, not a claimed public publication.
- c0ldzy17, *Deterministic 3SUM in O(n^1.962): method and proof*, source documentation, 2026. [Pinned METHOD.md](https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/METHOD.md), [Parameters.lean](https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Parameters.lean), and [LocalCoverBounds.lean](https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalCoverBounds.lean).
- Josh Alman and Virginia Vassilevska Williams, *Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*, arXiv preprint, 2026. [arXiv:2610.06783v1](https://arxiv.org/abs/2610.06783v1).
- Anthropic, *Truly Subquadratic 3SUM and Truly Subcubic APSP*, Lean formalization, 2026. [Pinned formal-math source](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp). The campaign imports its shared word-RAM statement.
