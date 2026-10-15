# Direct submissions: local review, 2026-10-10

## Repository choice and input

Use issues or proof-file PRs in `bigospeedrun/verifier`. One repository owns the
statement, workflow, receipt, and discussion. This document describes the issue
route. See [PR submissions](pr-submissions.md) for the second route and its
version 2 receipt contract. All changes remain local.

The issue form has exactly four fields, in this order: Problem, Repository
URL, Commit SHA, Bound. `scripts/submissions.py` accepts only the exact generated
headings and one-line values. Unknown, duplicate, missing, multiline, or prose
fields fail validation. Bound strings must already be reduced exact rationals.
The parser always selects `Race.bound`; users cannot select a toolchain,
challenge, theorem, dependency, author credit, or verification policy.

The normalized object has `schema_version: 1`, `problem` (`dft|3sum|apsp`),
`repo_url`, `commit`, `bound`, and `authors: []`. No author credit is inferred
from the authenticated issue submitter. Source credit needs separate evidence.
The historical `dft233` entry point is only a local receipt-test/manual profile.

## Record and account gates

The selector reads `data/{problem}.json` from `bigospeedrun/site`, at a resolved
immutable main-branch commit. It checks the same problem/model and exact score
order. It excludes the candidate issue itself, classical-baseline, and rows with
`record_metadata[id].reproduction_of`. It includes open claims regardless of
`eligible_for_record`, matching the site board filter.
The receipt records the board commit, data hash, leader IDs, verified-tie evidence, score, relation, and
observation time. The proposed policy uses the current eligible board leader
across evidence levels. A failed lookup stops selection instead of guessing.

A bound that matches or beats the leader gets a proof job. A tie is skipped
when any tied leader is already Lean Verified: metadata `site_tier: verified`,
`rerun_status.state: passed`, and a nonempty `receipt_path`. Numeric ranking
does not otherwise depend on evidence. The snapshot records all `leader_ids`
and `any_lean_verified_at_bound`. A passing equal-bound proof creates its own
row; it never changes credit or evidence on another author’s row. An attained saving at the same
value as a strict frontier compares according to the site's score relation.
A lower-ranked bound or an already verified tie receives a bot reply and remains Claimed. The verifier
checks the board and unchanged issue body again immediately before compilation.
If either changed, no Lean run starts and the result remains Claimed.

Issue batches select at most nine public requests and one per authenticated login.
Both routes share a trusted Git-ref lease that admits one batch at a time.
The manual verifier uses the same lease. Thus at most ten proof/report branches
run together on standard runners. Additional submissions remain Claimed for a
later scan. The scan has entry, API and time budgets, persists its page cursor,
and writes selections incrementally. See the PR design for lease and scan details.

The schedule rescans open issues. The trusted state ref reserves each issue
number with its normalized submission hash and raw issue body hash before
dispatch. A direct bounded file lookup prevents repeat proof jobs, regardless
of comment count. Comment markers are display data, not deduplication authority.
Reservations remain after proof or infrastructure failure; review handles an
interrupted admission without an automatic retry loop.

## Security boundary

Every job runs trusted default-branch code at the event SHA. No job checks out
a PR branch. User values enter no shell script or executable path.

The select job has contents write permission for the state-only admission lease
and issue write permission for gate replies. It parses data only and executes no submitted code. The proof job has
only contents/issue read permission. Its preflight token is scoped to the
trusted data-reading step. The source fetch pins the complete public commit;
trusted setup builds reviewed tools and fixed dependencies.

Proof elaboration, export, kernels, and axiom audit run offline inside the
existing bubblewrap plus landrun sandbox. That environment cannot read the
GitHub token, host process tree, controller checkout, or receipt, and cannot
write trusted source or dependency files. Submitted Lake files and hooks do
not run. Existing timeout, memory, CPU, and disk limits remain in force.

The report job runs on a fresh VM with issue write permission. It reads only
request/receipt artifacts from the same run and issue branch. It executes no
submitted code. It validates the source request, generated target hash, theorem
names, Lean result, reported axiom sets, and run/commit binding. It stores the
result, and then posts the receipt link. Review outcomes tag the maintainer.
No repository secrets are referenced. Checkout retains no credentials, and
actions use full commit SHA pins.

GitHub's [secure use guidance](https://docs.github.com/en/actions/reference/security/secure-use)
describes least privilege, script injection, and privileged workflow risks.

## Lean Verified policy

Lead policy, 2026-10-10: Comparator must accept the exact trusted target with
the Lean kernel. The axiom audit must pass and report every target, using only
`propext`, `Classical.choice`, and `Quot.sound`. A claimed audit status alone is
insufficient. The gate does not require workflow success or nanoda success.

Nanoda runs after the first Lean-and-axiom receipt is published. An explicit
`verification_stage: lean` checkpoint with `pending/advisory_queued` qualifies
while that advisory check is pending. See the PR design for early artifacts. Its receipt outcome
has an explicit `status` and `reason`. A pass is `passed/comparator_acceptance`.
A timeout, OOM, disk limit, or total deadline is `incomplete` with the specific
reason. Resource classification uses the host service manager or controller;
proof log text cannot fabricate an OOM or timeout. These resource outcomes do
not prevent admission after the Lean and axiom checks pass.

A confirmed nanoda type-check rejection is `rejected` and blocks the row.
Other nonzero exits, generic rejection messages, crashes, and missing acceptance
output remain `pending_review/ambiguous_failure` (or `missing_acceptance`).
They cannot be treated as incomplete passes. Both blocked and ambiguous outcomes
require maintainer review. The comment tags `@nmamano`; the full receipt keeps
the Lean result, nanoda result, exit code, host service result, and logs.

## Import contract

Result artifact name: `direct-submission-RUN_ID-RUN_ATTEMPT-ISSUE_NUMBER`.
It contains `direct-submission.json`, schema version 1:

- `submission`: normalized fields described above.
- `submission_sha256`: SHA-256 of the normalized object's UTF-8 JSON, keys sorted,
  separators `,` and `:`, ASCII escapes enabled, no whitespace or trailing newline.
  This is Python `json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)`.
- `issue_body_sha256`: SHA-256 of the exact UTF-8 body returned by GitHub, before
  newline normalization. `issue_submitter_login` comes from GitHub issue metadata.
- `issue_number`, `issue_url`, `issue_created_at`, `issue_updated_at`.
- `problem_id`: `exact-dft/uniform-exact-arithmetic`, `3sum/word-ram`, or `apsp/word-ram`.
  `score_relation` is always `attained`; strict-frontier submissions are unsupported.
- `model_revision` and `model_sha256`: upstream definition pin and fixed statement hash.
  `challenge` also gives file, upstream commit, base hash, and exact generated hash.
- `theorem_names`, UTC `checked_at`, and `source_published_at` (null unless separately
  established; neither issue creation nor check time is a publication date).
- `run_id`, `run_attempt`, `run_url`, `verifier_commit`, `receipt_url`.
- `receipt_artifact`: GitHub artifact ID, name, digest, and URL; `receipt_sha256`
  hashes the downloaded receipt bytes. Log hashes remain in `receipt.artifact_sha256`.
- `status` and `verification_status`: `passed`, `not_verified`, `blocked`, or
  `pending_review`, with `reason`. Test envelopes instead use `status: fixture_only`.
- `test_only` and `importable` are explicit booleans. Production requests require
  `test_only: false`; fixtures set `test_only: true` and `importable: false`.
- `workflow_conclusion` is null in the producer envelope. The importer gets the
  final workflow conclusion from GitHub API metadata and keeps it separate.
- `receipt`: full verifier receipt, with separate kernel outcomes, axiom sets,
  theorem results, source/tool hashes, resource measurements, and finish time.
- `record_gate`: the current record snapshot used for the admission-to-run check.

The importer independently binds repository, approved verifier revision, workflow
`.github/workflows/submissions.yml` and its reusable `submission-check.yml`, run,
attempt, issue, source SHA, model, score, current body hash, and artifact identity.
Issue-provided links and bot comments are not trust anchors. Imports are idempotent
by issue/request and pinned result. Open unmatched claims stay Claimed. Fixtures
must never enter production records. Accepted receipt evidence must be retained
because GitHub artifacts expire after 90 days.

## Layout and local validation

The README and AGENTS.md explain submission. `docs/targets.md` gives exact targets.
`.github/ISSUE_TEMPLATE/lean-submission.yml` supplies the four-field form.
`submissions.yml` selects the matrix; `submission-check.yml` separates proof and
publication jobs. `scripts/submissions.py` parses, queues, generates targets, and
publishes; `scripts/verdicts.py` contains the independent evidence policy.
The existing controller and sandbox entry support each profile's Lean version.

`challenges/3sum-apsp/EndStatement.lean` matches the official Anthropic pin byte
for byte. SHA-256: `4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987`.
Both upstream notices remain beside the statement. `profiles/direct.json` binds
the three models; the Anthropic manifest/tool files pin the Lean 4.33 environment.

The test-only legacy DFT fixture pins `837dc3130adc79f7b7ab4ddd56c15576bbd766b0`
and saving `47171/62500000`. Its unchanged real receipt comes from
[run 38050668997](https://github.com/bigospeedrun/verifier/actions/runs/38050668997),
artifact 11672731981, verifier `6551945e441b57c1b14f9ad8942ee5db1e05eb96`.
The replay checks the original request and challenge before adding fixture-only
metadata. It cannot start a production run, and its tied bound fails the record
gate when the matching leader is already Lean Verified. `generic-envelope.json` is a synthetic contract fixture, not a proof check.

On 2026-10-10, source fetch/staging for the historical pin passed: 396 sources,
82 chains, expected challenge hash, no Lean execution. Python tests cover input
injection, exact targets, bound/account/concurrency caps, raw/canonical binding,
axiom sets, resource evidence, nanoda policy, stale issues, and fixture rejection.
Workflow lint passes. No new GitHub workflow or generic profile has run. Hosted
end-to-end validation still requires publication approval. Nothing was pushed,
no public issue was opened, and no Lean ran on the office box.

