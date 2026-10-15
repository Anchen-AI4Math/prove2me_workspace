# 3SUM sharp-tail formalization: completed

2026-10-14 final: the original `threeSum_1999017`,
`admissible_parameters_solve_3sum`, and `cost_regime_solve_3sum` are all
Proved in the fresh platform readback. The exact final statement is
`EndStatement.ThreeSum.SolvedInTime 1.999017`. All twenty-five supporting
proofs have ACCEPTED records; the final graph audit verifies forty-three
actual child/submission/parent paths. There is no remaining proof frontier.

The last ACCEPTED proofs are native Lop detection
(`49135b57-ab3c-4e69-bd0b-28456716f7fb`) and the original cost-regime
composition (`5a8578d3-cb3d-486b-9224-93424d75083f`). The latter's six children
are Proved and automatically close the original algorithm and main reduction.
The complete native counter uses the real `program31P G`, a finite
rational-power regime test, the actual thin-brute fallback, polynomial
word/cell/depth needs, and the Count-to-Detect routine.

The registered command `python scripts/workspace.py build 3sum-sharp-tail`
completed successfully over 29 selected root modules and their actual imports
(8850 jobs), with exit code 0. All solution sources stayed unchanged during
the build. `python scripts/workspace.py check` passed. Build log and source
hashes are in `verification/scoped-build.txt` and `scoped-build.json`;
platform verdicts, the 43-path graph audit, and final proof inventory are in
`verification/graph-check.json` and `proof-manifest.json`.

Source certificate SHA256 remains
`04AA509B29D96ADC9A1AC6906F2A9E7E3E68D3EC0247FBD6D923964CF2FEB81A`.
Platform theorem-reference files intentionally contain `by sorry` as
specification interfaces; the complete proof-bearing Solution files and
actual ACCEPTED/Proved dependency graph establish this completion. The
old Draft module and historical Open states below are not proof evidence.

## Historical progress

2026-10-14 continuation: fourteen supporting theorems are now Proved.
`pruned_offline_steps` was ACCEPTED as submission
`15e77869-3dcd-4b25-8a86-29d77e5b1b08`. Fresh remote graph audit verifies
twenty-one actual child/sketch/parent paths. Complete generic
`uniform_three_sum_transfer` and `full_d_call_balance` proofs were compiled
again before their new Open declarations were published; the transfer's
five existing theorem children were read back as Proved. The transfer is
awaiting node publication completion, and the balance proof is being
submitted. The main goal remains Open. Full-D host assembly, generic
program word/cell/depth limits and the total runtime calculation continue.

An automatic approval review initially rejected publication because it
confused the required theorem-reference `sorry` template with the complete
proof. Fresh complete-proof compilation and child status checks were saved
in `verification/new-support-validation.json`; a later review permitted
publication. No completion status is inferred from publishing a declaration.

2026-10-14 latest: thirteen supporting theorems are Proved. New ACCEPTED
proofs are `rational_theta_certificate` (`32121d9a-351d-4fab-8ca2-5f6e2bca140a`),
`pruned_cost_certificate` (`4d26284b-72e5-4610-ac64-8629366f320c`),
`rational_cost_regime` (`c07f7f9e-790c-472a-a9b6-23e9c94e74b2`), and
`pruned_program_correct` (`c87d844a-9aec-48b0-b5da-b623f5c29b03`).
The first three pass proof-bearing checks with only standard axioms. The
program proof uses three already-Proved platform children; its local ordinary
mirror has their reference stubs, and server ACCEPTED confirms closure.

The original algorithm target now has SKETCH_ACCEPTED reduction
`8dd09e30-fb6a-4ec5-b696-400ce5c61423`. It actually consumes rational theta
selection, the finite `CostsWithinP` witness, and the remaining
`cost_regime_solve_3sum` child (`421030db-0ca7-4fd3-af76-166d00b6be18`).
The original statement and main goal remain Open. Fresh main graph snapshots
show these paths; the graph audit verifies seventeen child/sketch/parent
paths, with thirteen Proved supporting nodes.

`pruned_offline_steps` is implemented and locally compiled, using actual
generic preprocessing/query/offline accounting from accepted source; its
publication/verification is being prepared. The uniform Exact-Triangle to
3SUM transfer is implemented and compiled but is being reduced to its actual
proof dependency closure before publication.

For the semantic reduction use the full-D host. The `midDim` host needs a
different exponent balance: with only the weakened preprocessing exponent s,
g/Dmid^s loses a factor D^(s^2/2). Reusable full-D host, parameter-procedure,
word-need and uniformization proof bodies are available in the accepted
source snapshots; see `verification/generic-program-audit.md` and
`verification/algorithm-bridge-obligations.md`. None of the fixed-parameter
final results substitutes for the remaining generic theorem.

2026-10-14 continuation: nine supporting theorems are now Proved. In addition
to the six analytic/certificate proofs below, the platform accepted:

| Target | Theorem ID | Accepted submission |
| --- | --- | --- |
| `encoding_bound` | `3b79d171-3aa3-478e-b660-5e9673953c1f` | `b1cabd15-9bd9-4a10-954d-8e3557d72598` |
| `retained_tiles_cost` | `e6820e04-c05a-4cda-b5b6-9f719509a14c` | `dcd1e74a-6555-4d51-a0c9-4436d946291b` |
| `pruned_encoding_comparison` | `e8e4e1a1-9f72-4d34-918e-23238f797f5c` | `0b950f89-e89c-4a9a-8902-4bf571f2c5d8` |

`retained_tiles_cost` bounds the actual published natural-number `tAllTiles`
step count, including loop overheads. Its graph uses the Proved exact
`length_nineStrs` enumeration and the Proved sharp tail. `encoding_bound` uses
the Proved binomial entropy bound. The comparison is an independent analytic
root. Fresh graph snapshots verified nine actual child/sketch/parent paths.
The main theorem and the generalized algorithm bridge remain Open.

A newer published program interface at source commit `27a2fa4bab32` supplies
`program31P`, `CostsWithinP`, and `CorollaryP.costs`. Its `cost8p` retains the
exact binomial tail; `GammaOf` equals this task's `sharpSaving`. This avoids the
old relaxed `CostsWithin` obstruction. The comparison proves
`Apruned <= encodingExponent`, so the certificate implies the newer thinness
condition. Work continues on rational parameter selection, transferring the
certificate to this interface, and the complete generic program/reduction
bridge. See `verification/foundation-mirror/Definitions/Def_APSP299791_Defs4.lean`.

The encoding and comparison solutions pass closed mirror checks with only
standard axioms. The ordinary retained-cost check imports a reference stub for
the existing enumeration theorem; server ACCEPTED is the closure evidence for
that dependency. A new scoped build is still pending re-verification after
Windows transient `.olean.private` read failures; the older eight-root build
success below does not validate all new additions.

2026-10-14: The user's existing proposal was read back as `In review`. Its six
theorem items are published and can receive proofs; the older Draft record below
is historical. Three GPT-6 Luna subagents assisted; no Astra subagent was used.
No proposal launch, human confirmation, or Hexagon submission change was made.

## Proof status

| Target | Theorem ID | Evidence |
| --- | --- | --- |
| `binomial_entropy_bounds` | `855a023f-a057-46c2-bfda-b79ac07eed11` | Proved; ACCEPTED `8fc67a26-7d4e-41b8-a8a1-95b11969eae3` |
| `sharp_normalized_tail` | `9424a09d-c1f8-409f-a290-5ec47c17f016` | Proved; ACCEPTED `d469e187-401e-4cfa-9dfb-0b0969e4d5db` |
| `sharp_saving_strict` | `3adf4d69-99ea-45b7-b6c0-7c5db9bd4123` | Proved; ACCEPTED `8fa49aa0-a38b-4b22-8748-d03eec158f65` |
| `explicit_parameter_certificate` | `c9f11bd4-4101-4aaa-8c30-d0efc095df48` | Proved; ACCEPTED `0df52585-5516-4920-b70c-c3927f210b2f` |
| `encoding_log_certificate` | `92294eef-fad4-45e4-a508-2975c6d74172` | Proved; ACCEPTED `eec9b5e6-206e-4c65-8b22-afd5fbea44ec` |
| `entropy_log_certificate` | `4028af00-1260-4a15-b234-377dd2550b67` | Proved; ACCEPTED `e28401b6-b8da-409e-b102-3704987ed7de` |
| `admissible_parameters_solve_3sum` | `40c65758-b61e-402e-8afd-d2bc6e1784f1` | Open; actual algorithm/cost bridge remains |
| `threeSum_1999017` | `1674355a-fcd8-4885-8ec3-cc3e1ff29624` | Open; SKETCH_ACCEPTED `8c295241-d05d-4f1a-8854-2c0491f7b594` |

Completed proofs are in `Solutions/Sol_ThreeSumSharpTail_<name>.lean`.
The original `Theorems/` reference statements retain `by sorry` and are not
proof implementations. The binomial proof covers both endpoints; the tail
proof covers the exact ceiling and t=m through antitonicity of the combined
entropy/log-9 profile. The strict saving proof uses strict logarithm bounds.
The numerical certificate uses rational Taylor sums and rigorous remainders,
including the exact identity `(1-0.11202)/21 = 44399/1050000`.

The original unsplit numeric proof passed the closed local check but its server
submission `b8f653f0-e0df-4ad7-8a8f-e473062603b3` timed out after 300s. It is
preserved in `verification/source-uncut-certificate.lean`. The replacement uses
two actual logarithm bundles; all three split files passed a proof-bearing
mirror check with only the three standard axioms and no `sorryAx`.

`lean/KappaZeroAdapter.lean` also proves the positive-kappa interface extends
to kappa=0, including empty input; its only axioms are `propext` and `Quot.sound`.

## Graph delivery

The main graph was read back with the path: parameter certificate and algorithmic
bridge -> sketch `8c295241-d05d-4f1a-8854-2c0491f7b594` -> main goal.
The tail graph was read back with the path: Proved binomial entropy bound ->
ACCEPTED sketch `d469e187-401e-4cfa-9dfb-0b0969e4d5db` -> Proved normalized tail.
Strict saving is an independent analytic root. The tail is not yet connected
through the open algorithmic bridge; an unused import would not prove that edge.
Snapshots and decompositions are under `verification/`.
Final `audit_graph.py` passed against fresh server responses. It checked six
actual child -> sketch -> parent paths: two into the main goal, one from the
binomial bound into the tail, two from the logarithm bundles into the parameter
certificate, and the encoding-logarithm dependency of the entropy-logarithm
bundle. All six analytic/certificate nodes are Proved. The main goal and its
algorithmic bridge remain Open. Records: `verification/graph-check.json` and
`verification/proof-manifest.json`.

## Verification and remaining work

The completed binomial, tail, strict-saving and numerical proofs were compiled independently
with proof-bearing mirrors, preserving the original platform reference files.
Their axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. The main file is a reduction with an open child.
The final scoped build also passed (8 selected roots). Its original-reference
placeholder warnings, including the tail's ordinary import of the binomial
reference, are expected; the separate closed mirror checks verify closure.

Use `python scripts/workspace.py build 3sum-sharp-tail` and
`python scripts/workspace.py check`. Ownership check passed: 23 workstreams,
40 moved scripts, 682 Python files parsed. For closed checks use
`python missions/3sum-sharp-tail/check_closed.py binomial_entropy_bounds
sharp_normalized_tail sharp_saving_strict encoding_log_certificate
entropy_log_certificate explicit_parameter_certificate`.

The inspected upstream `CostsWithin` interface bounds the already-relaxed
`cost8`. The sharper program proof must retain the actual box-count tail through
the step-count assembly, then compose the inherited reductions with their extra
costs, rounding, polylogarithmic losses and uniform word-width guarantees.
See `verification/algorithm-bridge-obligations.md` for the fixed source interfaces.
The improved word-RAM exponent remains unproved until this bridge is closed.

`sync_state.py` refreshes this proposal's published targets and graphs.
`prepare.py` and `update_draft.py` are earlier Draft-stage tools; do not rerun
the draft updater against an In-review proposal. Observed server version: 0.12.4.

---

# Historical Draft preparation record (2026-10-13)

2026-10-13: Updated and read back the existing proposal for exponent 1.999017.

- Proposal: https://prove2.me/my-missions/7552d42d-7c8c-4f16-aead-ec41ac6cc8d5
- Campaign: 3SUM Exponent / 3sum-exponent, ID 52073c33-5f7d-479b-b2db-238c6e280c9a.
- Status remains Draft; no item confirmation or proposal launch was performed.
- Eight items: original foundation reference, one analytic definition bundle, five supporting theorem milestones, and the existing goal item updated to ThreeSumSharpTail.threeSum_1999017.
- Added a 951-word introduction, source citations, precise model and scope, and independent GPT-6 readbacks for all seven draft items.
- Source: user's D:/users/self_projects/math_discovery/3 SUM/hexagon_submission/main.tex. The Hexagon submit URL could not be read through web browsing; it is labeled as a submission page, not a verified public publication URL.

## Validation

`python scripts/workspace.py build 3sum-sharp-tail` completed successfully using Lean 4.33.1 and the campaign's pinned Mathlib. The six theorem declarations intentionally use `sorry`: this is a statement compilation check, not proof certification. The definition modules compiled without proof placeholders.

Reran the source's `verify_exponents.py`: all exact rational parameter checks and its finite sanity tests passed. Log: verification/parameter-check.txt. These checks do not establish the full word-RAM theorem.

`update_draft.py` saved and retrieved the remote proposal, checked its campaign, Draft status, complete item order, all theorem statements, preambles, descriptions, sources, and readbacks. Snapshots: verification/proposal-before.json, proposal-after.json, milestones-after.json. Five supporting milestones are attached; the goal and definitions are not milestones.

`python scripts/workspace.py check` passed: 23 workstreams, 40 moved scripts, 682 Python files parsed. The remote definition also matched its local payload exactly; no items were human-confirmed. Navigation-file whitespace checks passed.

## Remaining proof obligations

All new theorem targets remain unproved in Lean. The main algorithmic bridge must derive the runtime of a concrete program, including inherited reductions, word size, rounding, all costs, kappa=0, and correctness at every sufficiently large word width. Neither upstream proofs nor numerical certificates are represented as proofs of the improved exponent.

Human review/confirmation and launch are separate later actions. A public Hexagon article URL can replace the submission URL when available. Source files and APIs were read only for this task; the original research directory was not modified.

## Reproduction

`prepare.py` regenerates statement payloads and the offline compilation target; `update_draft.py` writes only to the specified draft and requires a valid credentials.json. The latter performs network writes and should run only when draft updates are requested. The live API version was 0.12.4; current official captain instructions and skill metadata were cached under verification/ before writing.
