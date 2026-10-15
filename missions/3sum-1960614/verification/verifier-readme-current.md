# Big O Speedrun verifier

Submit a Lean proof of a bound for Fourier transform, 3SUM, or APSP.
The verifier checks the proof against our fixed statement on GitHub Actions.
A passing submission appears as **Lean Verified** on bigospeedrun.com.
An open submission without a passing check appears as **Claimed**.

## Submit

Choose either route. Both use the same statement, record gate, and proof checks.

- **Pull request:** add a new folder under
  `submissions/<problem>/<github-login>-<short-name>/` in this repository.
  Include `Submission.lean`, any extra Lean files under `Submission/`, and
  `manifest.json` containing only `{"problem":"3sum","bound":"1999/1000"}`
  with the problem and bound changed to match the proof. Open a PR that adds
  only that folder. Export `Race.bound` and keep source credits in the Lean files.
- **Issue:** keep the proof in a public repository and
  [open a submission issue](https://github.com/bigospeedrun/verifier/issues/new/choose).
  The form takes the problem, repository URL, complete commit SHA, and reduced
  exact rational bound. Put `Submission.lean` at that repository's root and
  extra Lean files under `Submission/`.

See [the problem guide](docs/targets.md) for the exact target and Lean version.

Use `dft`, `3sum`, or `apsp` for `problem`. Use an exact nonnegative rational
for `bound`. For DFT, the bound is the saving s in O(n (log n)^(1-s)); a larger
saving is better. For 3SUM and APSP, it is the exponent r in O(n^r); smaller
is better. The ranges are 0 ≤ s ≤ 1, 0 ≤ r ≤ 2 for 3SUM, and 0 ≤ r ≤ 3 for APSP.

The verifier runs up to nine public submissions and one maintainer test in parallel,
with one queued public run per GitHub account. A run starts only if the bound matches or beats the current record;
otherwise, the bot replies that the submission is listed as Claimed.
The bot posts a receipt on the issue or PR. For PRs, a Lean pass causes an
automatic merge. A real Lean or axiom failure, or a real nanoda rejection,
causes an automatic close. A timeout, resource limit, or infrastructure failure
leaves the PR open with a review label and a maintainer mention. A below-record
PR stays open as Claimed. Scheduled checks pick up new PR commits.

Before merging, the bot checks that the PR adds only its own new submission
folder and that its head is the verified commit. An unsafe diff is closed with a reason.
If the head changed, the bot skips the merge and leaves the PR open for the new check. A check does not transfer another author's credit.

## What Lean Verified means

The proof establishes the submitted bound in our fixed computational model.
Comparator checks the statement and definitions against our trusted copy,
checks allowed axioms, and replays the proof with Lean and nanoda. The Lean kernel
and the axiom audit must pass. The bot posts this result immediately. Nanoda
runs afterward as an advisory check and updates the receipt. A nanoda timeout or resource limit does not prevent
Lean Verified; a real nanoda rejection blocks the row for maintainer review.
An ambiguous failure stays pending review. Only `propext`, `Quot.sound`, and `Classical.choice`
are allowed. A normal Lean build alone does not pass this gate.

Lean Verified does not establish novelty, priority, authorship, or practical
speed. A passing check does not by itself mean that the bound is a new record.
The source commit, exact bound, and receipt remain part of the result.

OpenAI wrote the trusted DFT model. Anthropic wrote the trusted 3SUM and APSP
statements, based on the paper by Josh Alman and Virginia Vassilevska Williams.
The [Anthropic statement](challenges/3sum-apsp/EndStatement.lean) is copied
without changes from `anthropics/formal-math` commit
`e1a4e6508154ea59f030480661590a9fe3018011`. Author credits and notices remain
with the source. See [NOTICE](NOTICE).

Proofs run offline on fresh standard GitHub runners, with fixed dependencies,
resource limits, and no access to the token that posts results.
See [issue security and layout](docs/direct-submissions.md),
[PR security and receipt contract](docs/pr-submissions.md),
[execution details](docs/execution.md), and [AGENTS.md](AGENTS.md).

To propose a trusted statement for a problem that has none, see
[the statement contribution guide](docs/new-statements.md).

For research that is not a proof submission (statements, formalization,
audits, tooling and negative results), see [auto-research.md](auto-research.md).

