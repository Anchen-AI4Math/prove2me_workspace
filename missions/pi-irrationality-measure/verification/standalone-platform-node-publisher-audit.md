# Standalone node publisher audit — 2026-10-08

Implemented `scripts/publish_standalone_platform_node.py`. Default execution and
`--prepare-only` are offline: no API module import, credential read, GET, POST,
or token refresh. Only explicit `--advance` enters the network branch. This
agent did not execute that branch or run Lean.

The publication gate reuses `check_stage` and `strict_inputs`, requires the
standalone validator's current exact certificate and implementation pins, and
checks all four preflights, their saved records and log hashes, original and
generated JSON hashes, source/target/solution kernel types and standard axiom
audits. Definitions, children, renames and other unsupported cases remain
rejected by the standalone gate. Standard axiom log parsing accepts only the
three exact standard names and the own-single-universe-parameter display of
`Classical.choice` or `Quot.sound`, not arbitrary stripped suffixes.

Preparation produces canonical `publish-payload.json`,
`verification-payload.json`, and `preparation.json` binding metadata, manifest,
certificate, publisher, API-client and both payload hashes. The theorem
publication payload is the exact HTTP JSON body. The verification JSON is an
offline descriptor containing the exact UTF-8 proof bytes and explanation:
`/verify` uses multipart and its new theorem ID is not known offline. Only that
ID is late-bound from an exact server name/environment/text/visibility
readback. The exact multipart body and its hash are saved before the verify
POST.

`--advance` requires already-existing, byte-identical prepared payloads. It
does not silently regenerate changed review material. Its state file records
intent before POST and result/job/submission IDs after POST; an uncertain POST
is never retried automatically. Exact-name searches paginate to completion;
existing exact proved content is reused. Publish jobs and verification jobs
are polled on later invocations. No mission-proposal submission is performed;
proposal status remains Draft, and no full-tree readiness is asserted.

The strict extraction-state pin applies during publication as well as
compilation. Keep the extraction hold until this node's network workflow has
reached the required verdict; appending global state invalidates the current
prepared certificate and payload bindings.

Collision metadata was written for
`OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le`. Its natural-language
statement includes nonnegative cutoff and weights, the low-count hypothesis,
the weighted-sum conclusion, and correctly permits arbitrary real eta. The
explanation partitions low/high indices, obtains a high-count lower bound,
multiplies by the nonnegative cutoff and invokes the full inline helper proof.
The source witness was derived from the authoritative AST range, lines
137–154, and the original source lines were checked against the port declaration
bytes with only CRLF normalization. Commit:
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Pure Python checks passed for script syntax, metadata/source witness, canonical
payload determinism, exact statement concatenation and exact solution bytes.
Expected payload hashes for the current metadata:

- publish: `875f252d9446933e6f06f122c8155377f01036e7105763eab33e8aca9cd5fa57`
- verification descriptor: `48e60a328b0883b7cde08ca970a4a651e0f1f46756903deb187c1f3d53611a33`

The real `--prepare-only` invocation correctly refused before writing payloads
while Collision's four-file local validation certificate was still pending.
After root completes that certificate, rerun preparation to obtain the actual
review artifacts; no bypass was used.
