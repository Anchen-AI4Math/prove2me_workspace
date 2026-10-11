# Independent graph topology review — 2026-10-08

This is a pure, source-level review: no Lean invocation, API call, credential access,
shared-module change, mission mutation, or scope change was performed for this report.

The saved authenticated v0.12.2 readback records the new public mission
`5eb457c6-bc3b-4f51-852a-c5d29fb77c53`, root
`523f37b8-ae98-406c-a3f7-43aa8e002dd7`, 69 milestones / 67 completed, and a graph of
five theorems, two sketches, and six edges. Both Open frontier nodes have no
decompositions. The evidence is
`formalization/platform/readback-2026-10-08/graph-diagnosis-125218/`.

## Minimal faithful next layer

For the existing two-form obligation
`ZetaNine.exponentially_small_independent_forms_of_zeta_nine`, use three genuine
ingredients: the exact selected integer-output HasSum identity, the uniform
weighted quartic bound, and an Open shortness obligation for the **actual**
`selectedIntegerMultiplier`.

The shortness child should assert that there is a fixed delta > 0 and, for every
N, an even n >= max(N,2) and two integer pairs (b_i,a_i), with nonzero determinant,
such that both actual selected inverse-image polynomials have weighted coefficient
height <= exp((2641/250-delta)*n). It must not assume the linear forms themselves
are small. This child retains the mathematical J/height difficulty and identifies
the precise construction used by the analytic estimate.

The existing exact identity is
`ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute`.
Its `zetaReal 9` is definitionally `(riemannZeta (9 : Complex)).re`, so no synthetic
new zeta-identity child is needed. The actual weighted sequences in the analytic
and summation definitions are likewise definitionally identical.

The selected multiplier degree <= 4 has a complete proof at lines 2082–2084 of
the frozen Matrix full Solution. It may be re-proved structurally in the bridge,
or published as a meaningful reusable lemma; it is not currently a separate
milestone theorem in this readback.

The uniform bound supplies an error epsilon_n -> 0. Choose n after the threshold
where epsilon_n < delta/2, then multiply the two exponentials to obtain
exp(-delta*n/2). The existing target is stated at all sufficiently large natural
scales, whereas the source construction is cofinal along even n. Its existential
integer outputs allow choosing a construction parameter n >= the requested
target scale and the error threshold. This reindexing must be proved explicitly;
do not silently replace a cofinal even subsequence by an all-n construction.

For the single-form alternative, a similarly explicit selected inverse-image
shortness-plus-sign obligation must be combined with the exact HasSum identity,
the uniform bound, and genuine nonvanishing. The general Taylor sign criterion
alone does not prove that the actual moving shortest outputs have that sign.

## Limits and exclusions

The unrestricted existential exponentially-small-form targets have no coefficient
or denominator-height upper bound. Their natural-language claim of being strictly
stronger than irrationality is unsupported: arbitrary irrational reals admit
arbitrarily small nonzero integer linear forms when arbitrarily large coefficients
are allowed. Creating another unrestricted existential reformulation is not a
faithful construction-level decomposition.

Do not import unrelated solved milestones merely to create graph nodes. Zudilin's
four-value disjunction does not imply the single-value goal. The published volume
cancellation and finite-prime budget lemmas are abstract conditional cores, not
proofs of the actual asymptotic V or J sequences. The local DAG explicitly marks
research-input arrows separately from sufficient proof arrows.

Keep root, actual shortness/J, moving sign/direction, and any genuine asymptotic
height obligation Open. Exact rational inverse-image existence is already proved;
do not conflate it with a useful asymptotic height bound.

Official v0.12.2 `prove.md` requires meaningful reductions (line 285), a sorry-free
top-level `solution` of the exact parent type, no own-target import, public imports
for public targets, and the same Mathlib environment for every dependency
(lines 305–307). The environment is
`0df444a360eaa60ab8c11dca51a86af692955474`.

## Frozen package readiness at this review

The complete analytic-uniform platform AUTHOR report exists at
`formalization/platform/analytic-uniform-weighted/platform-author-complete-audit.json`,
SHA256 `031f62b8d0966df6484e78072a74b8bb08a9a76a8c892c6d396c3c5a080e0b91`.
It records 24 actual calls, 24 successes, complete original 122 proof bodies in each
of three separate Solution contexts, 29 distinct whole functions (the 13 new ones
are a subset), and complete typed boundaries and helper/kernel controls. It
explicitly states independent transplantation review pending and uploaded false.
The native analytic A independent PASS is a different checkpoint and cannot stand
in for the missing platform independent review.

The three frozen candidate Solutions have SHA256:

- moment: `a1da7bed13446009607ddaab446ed2731233b79fd1ef52f4a87c3d12d67c2248`
- changing: `cd1ce8aaabea27391e0e0d92644e73cef6ee1e450ad7c0faefc0b5e113be1d19`
- uniform: `e4d580204f188ade1eda30a5bb05476eac11462399186887d87bf97ded33c52a`

The Outputs transport package has an execution receipt but no top-level complete
audit in the inspected directory. Its receipt currently contains 130 actual
successes, two actual failures, and two other records without terminal-state
fields. It must not be presented as a completed platform package.

## Publication safeguards

The Phase business journal still has an UNKNOWN first problem POST
`problem_ZetaNine.AnalyticPhase.phase_strictAntiOn_right`, dated
2026-10-07T12:27:50.402283+00:00, with receipt_saved false. Resolve that request by
documented read-only own publish-job history/detail before any subsequent business
POST. Preserve exact wire and the before-reconciliation journal. Never blind retry.

Use only the new public mission. Do not write the old mission or frozen proposal.
Create real missing definitions/problems before proofs that import them. Before
every outgoing write, bind exact complete SOURCE bytes, name/type/preamble/env and
public visibility. Use a durable WAL and exclusive writer lock. A missing response
must stop all subsequent business writes until read-only reconciliation. After
acceptance, read back decomposition children, public visibility, exact statements,
and root Open; only actual observed edges support graph-completion claims.
