# Separate public provider snapshot resolver

`scripts/prepare_fast_provider_snapshot.py` stages only new generated snapshots.
It does not edit the frozen provider generator, ordinary snapshots, provider
certificates, source extraction, or runtime pins. Existing ordinary generated
JSONL, preflight sidecar, or provider certificate causes explicit rejection.

The helper reconstructs the original generated snapshot from the frozen
producer, exact request list and TypeOnlyTheoremSnapshotCore, then replaces
exactly two unique byte anchors: the complete resolver command and the output
JSONL literal. Reversing those edits must reproduce every original byte. The
new source is `SnapshotGeneratedFast.lean`; its output is `fast-generated.jsonl`.
The source line-ending style is preserved; mixed LF/CRLF or bare CR is rejected.

Eligible requests are ordinary public theorem/definition Names with exact ASCII
dotted identifier spelling. Private, quoted, numeric, empty-segment and Unicode
spellings are rejected. The public resolver folds exact components using
`Name.str` from `Name.anonymous`, checks `name.toString` round-trip, `env.find?`,
`privateToUserName?.isNone`, and the actual imported owning module. It performs
no full-environment scan per public request. The old private resolver branch is
preserved but is ineligible for authenticated fast stages. All CI exporter
fields, closed-type/full-definition-value checks, null theorem values and
axiom exports remain byte-identical. Exact structural type/value and Std3
comparison in the provider validator remains mandatory.

`--prepare-only` may stage a pending source before its provider is compiled;
such a stage has no runnable imports manifest. `--bind-provider` requires the
actual successful bounded bundle preflight, exact source/runtime/log/manifest
hashes, emitted provider OLean, and first ordered search-path resolution to
that same OLean. The runnable `fast-imports.json` certifies only the actual
`Lean` and provider imports, using the runner's existing generic `output`
source-certificate rule. No frozen runner change is needed for the new filename.

The Python API returns the ordinary runner stage dictionary with module
`SnapshotGeneratedFast`, plus `generated_jsonl` and provenance path/SHA. Its
default requires actual provider evidence; `require_provider_evidence=False`
permits explicit pending staging. All source, input, provenance and runnable
manifest bytes are reconstructed and compared exactly before reuse.

The Arithmetic two-request candidate has a pending fast source; no Lean
process was started. Offline QA validates exact reconstruction, eleven negative
cases, the existing NefAmple/QuotientLengthEquivalence evidence refusal, and
actual first-path OLean evidence from the existing Quota bundle without
staging a replacement for it. See `fast-provider-snapshot-python-qa.json` for
the helper/source hashes and fixture outcomes. Performance improvement has not
been measured; root's later serial preflight must remain within 300 seconds.

Optional validator integration must select the fast source/output explicitly,
record its provenance in the new certificate, and retain the same structural
kernel comparison. Default ordinary certificate fields must remain unchanged.
All prepare-only stage validation/submission flags remain false.
