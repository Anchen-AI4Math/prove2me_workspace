# Isolated FormalLogJet namespace-context extension

The new `scripts/generate_namespace_context_providers.py` preserves the frozen
provider generator and shared global plans. Its output is exclusively under
`verification/providers-context-preview`; the existing 29 provider sources,
manifests, ordinary snapshots, source catalog and source174 certificate are
unchanged. No Lean or network operation was started.

The sole overlay edge is **FormalLogJet -> FormalJetDerivatives**. Authority is
the unique complete Stage2 `Lean.Parser.Command.open` fact at bytes 274--310,
with identifier bytes 279--310. Its exact bytes are
`open PiExponent.FormalJetDerivatives`. The AST scope inventory records that
command as active context for all nine selected FormalLogJet commands. The
source Graph resolves `OAI.PiExponent.FormalJetDerivatives` to exactly one owner
module, and that provider actually retains these public constants:

* `jetFrame`
* `jetFrameWord`
* `pderiv_mem_rationalWeightedIdeal`

The owner provider imports JetGeometry. The process-local overlay adds the real
owner import, checks that the Definition DAG remains acyclic, and reruns the
existing boundary guard. It does not invent a namespace command or promote
units. The original `open`, namespaces, sections, variables, notation, attributes
and all selected proof bodies remain in the copied skeleton. Project import
edits use the same authority and engine as existing provider generation.

Four unvalidated stages are generated in `namespace-context/Definitions`:

| Module suffix | Selected commands / CI requests | Body bytes |
|---|---:|---:|
| Polynomials.PolynomialFrame | 11 | 3,524 |
| Jets.JetGeometry | 11 | 4,896 |
| Jets.FormalJetDerivatives | 3 | 11,409 |
| Jets.FormalLogJet | 9 | 12,779 |

All four have no renames or additional elaboration-only helpers. The selected
domains contain public ordinary theorem/def CIs only. Every original and
generated request binds the exact source Name, module, graph kind, command unit,
raw graph-row hash, source hash, source range and facts hash from the complete
6148-owner catalog. Owner metadata is not an actual kernel certificate.
Source comparison outside the certified174 subset remains explicitly pending.

Each module has its own exact original/generated snapshot request file and
type/value comparison plan, plus `source-catalog-bindings.json`. The generated
provider import OLeans, source/generated structural CI comparison, Std3 audit
and actual whole-import-closure collision check remain pending. These files
cannot be treated as validated dependency providers.

The isolated source snapshot `source-snapshot/ContextSourceSnapshot.lean`
imports Lean and the four **original** source modules. Its 34 requests use direct
public Name construction, exact round-trip, env lookup, private-name rejection,
and actual imported module owner checks. The exporter checks closed types,
complete ordinary definition values and Std3; theorem values remain null. Five
actual first-path original OLean witnesses and all input/source hashes are
bound in `source-imports.json`. Root may run this one file serially with the
existing staged runner and a 300-second timeout; its future actual source
certificate still does not establish any generated provider availability.

Offline QA checks the exact four output/source/catalog/overlay hashes, original
open bytes, real provider import, source-fast exact header, all manifest input
pins and current source OLean bytes. Wrong source owner, truncated request
domain, duplicate Names and empty namespace provider are rejected. See
`pure-python-qa.json` and `context-overlay.json` for complete witnesses.

The isolated variant is frozen at SHA
`5887e585b899b4a3c07499f55e4766a2694ad6c279ae70b2138e885b6e6dbead`.
The source-fast file is
`54d1488e58d88f37cf1d3616d34c14474e108bef68c9bd51e0b3b0a529959f6a`.
All validation, full-tree readiness and submission flags remain false.
