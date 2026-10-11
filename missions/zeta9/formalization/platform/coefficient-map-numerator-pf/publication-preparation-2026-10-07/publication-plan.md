# Generic numerator PF: global publication plan, 2026-10-07

The authoritative preparation is `prepared-publication-v2.json`, SHA256
`21c284e27f371f790726c10d9a8dc9f7190235ffb01e98aa0a0df4a2aca4e6b6`.
Its status is **PURE_PREPARATION_WAITING_FOR_ROOT_INDEPENDENT_PIN_NOT_PUBLICATION_PASS**.
This document and both preparation drivers perform no API or Lean call.
The v1 prose and manifest are retained; v2 changes only inline mathematical
delimiters to the official `$...$` syntax. All seven Lean payloads are unchanged.

## Target, visibility, and counting boundary

The only project target is proposal `19653cff-d481-498a-a717-10630d1ca1b7`.
Compare its title with `Irrationality of ζ（9）` after NFKC normalization;
the normalized exact title is `Irrationality of ζ(9)`. Read it only with
`GET /mission-proposals/19653cff-d481-498a-a717-10630d1ca1b7`.

The new public proposal is In review and frozen. Do not update its items,
milestones, description or title. No mission or proposal mutation endpoint
is allowed in this plan, including linking these PF items. Both previous
identities are forbidden in outbound paths or bodies:

- Old mission: `8195d8fe-059f-4515-92b4-57b585e2bac6`.
- Old proposal: `06faf23f-00c2-4edf-92ab-1212cdb7d7d6`.

Register one new definition and three new theorems globally with `private=false`
and explicit environment `0df444a360eaa60ab8c11dca51a86af692955474`.
After acceptance, these are global public results, **not references of the
new proposal**. Its checkpoint stays 88 references, 18 definitions,
69 milestones and 67 supporting Proved statements. Three additional saved
complete ACCEPTED proofs would bring the global saved-proof count from 54
to 57, with **three PF proofs not referenced by the proposal**. Do not report
70 proposal Proved items or 91 proposal references. Preserve the existing
post-Matrix 54/67 audit. Linking requires a later, separately prepared
operation against an actual writable new live mission.

## Exact SOURCE and review gate

Use the copies under `payloads/`, copied directly from the seven `staged/`
files. These total 61,210 bytes. Definition bytes are decoded and re-encoded
as UTF-8 without newline conversion or trimming; proof uploads use raw bytes.
Never read a publication payload from a compiled object, Root module or cache.

| File | Bytes | SHA256 |
|---|---:|---|
| Definitions/Def_ZetaNine_CoefficientMapNumeratorPF.lean | 2387 | 2781de146990caba0ae3fc1e913dfdfb65e40b3dc06a87628d597c86fa81f42e |
| Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_polynomial.lean | 529 | bef2c154fbb15ea53831a0e1d4c536b4298129cfb90f9537780d30a15388bb9b |
| Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_global.lean | 712 | 2755f905ce4978453a4aa07f72df62e435c11319f824dbc0421c1b1773319115 |
| Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_injective.lean | 663 | dda392c7e58ebd1e325e17da75fe3354d13ae663f4d0e22dacef2b63becd72c5 |
| Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_polynomial.lean | 18873 | 90eefdfcd2d8fd4a5dcff75df8b378ae3b97d80346245a2df380468adc31d551 |
| Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_global.lean | 19051 | a76fb8426da6ede692f2a8628bc91eab6ed3408aa55d653159fe60af597b6965 |
| Solutions/Sol_ZetaNine_CoefficientMapNumeratorPF_injective.lean | 18995 | 968e382bcee06b9c13431fc7beebb68d715608fb311258c140ed8df80b301c69 |

The three reference files are exactly the frozen request preamble, one newline,
the complete frozen formal statement, and one newline. Registration preserves
the preamble and formal statement verbatim. The reference placeholders are not
uploaded as proof files. The three Solutions contain the complete direct proofs
and do not import their own target or any platform theorem module.

The platform AUTHOR report remains
`5a9491c73cbbb980b411a3389a4c5acd6f0e5ceb71149c8a508f9553660f0ebf`:
24 passed checks and 1441 bound files, with the original failures excluded and
retained. The genuine native SOURCE is
`2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77`.
`author-evidence-contract-v2.json` connects these bindings to the actual native
reachable control SOURCE/log/exit and the full native/staged expression records.
It records 11 native complete definition types/values, 34 complete named theorem
types, one generated helper, three staged environments, five complete new
definition values and whole-function rfl checks per environment, all three
complete forall endpoints per environment, nine boundaries per environment,
private-helper coverage, and 292 actual Std3 reports. It does not manufacture an
independent report or reinterpret author work as independent work.

Before the first business POST, Root must finish and freeze the platform
independent report, personally rehash its bindings, and create a real pin.
The pin contract is in `required-future-Root-pin.json`; it is a schema/contract,
**not a pin or a PASS**. It has no invented independent hash. It must bind the
actual report, the seven exact payloads, this final preparation manifest, and
actual source-graph/reachable/full-type/whole-value/Std3/boundary/resolver evidence.
`prepare_publication_v2.py --check-root-pin <actual-pin-path>` rehashes all 1441
author bindings and every future independent binding, fail-closed. A missing,
unknown or mismatched report is an error before any client is constructed.

## Official client and endpoint boundary

First check all six local v0.12.1 document hashes recorded in the manifest.
Do not call the existing `docs_gate.docs()` helper: it can fetch extra files and
write outside this preparation. The offline `docs_gate()` checks just the six
fixed local files. Only after these checks and the independent gate may Root
load the existing official Client SOURCE and set that isolated runtime module's
VERSION to `0.12.1`. Do not edit the old client file or its VERSION on disk.
Preserve its official redirect boundary, health-version guard, refresh-version
guard, secret handling and single-attempt POST behavior.

Use a guarded client: allow documented read-only health, environments, this
exact proposal, canonical theorems, publish jobs and own submission history.
Allow only the three business POST paths below, plus unauthenticated token
refresh. Refuse every PATCH, DELETE, `/missions/` endpoint, make-public endpoint,
proposal write, milestone write and link operation. The multipart `/verify`
path must pass the same guard; bypassing Client.call for multipart must not
bypass the journal or identity checks.

| Step | Endpoint | Exact input / required readback |
|---|---|---|
| 1 | POST /submit-definition | `requests-v2/01-definition.json`; explicit ENV/public; full staged definition body. |
| 2 | GET /publish-jobs/{job_id} | Wait for exact `PUBLISHED`, with kind/name/full `definitions` bytes matching; retain every raw readback. |
| 3 | GET /theorems/{theorem_id} | Canonical public Definition, correct identity, ENV and full definition body. |
| 4 | POST /submit-problem, one theorem per transaction | The three `requests-v2/02-…`, `03-…`, `04-…` files. Preserve the complete formal statement and preamble. |
| 5 | GET /publish-jobs/{job_id}, then GET /theorems/{theorem_id} | Exact `PUBLISHED`; canonical public identity/ENV, full formal statement and preamble, with no unreviewed import. |
| 6 | POST /verify, one theorem per transaction | Actual canonical theorem_id, proof_type=prove, the exact corresponding Solutions bytes, and its complete `proof-explanations-v2/` text. Do not send an env field; the target supplies the environment. |
| 7 | GET /verify?submission_id={id}, then GET /theorems/{id} | Require exact `ACCEPTED`, matching target, then public `Proved`, matching ENV/formal statement/preamble. A `SKETCH_ACCEPTED` result is not counted as a complete proof. |

There are seven planned business POSTs if none of these exact global items
already exists: one definition, three problems, three proofs. Existing matching
canonical items may be reused after complete readback; a same-name mismatch
must stop, never be patched or replaced. The definition is not a proof target.

The publish-job schema documents `definitions` as the full submitted definition
body (or problem preamble). The two reviewed endpoint documents do not fully
specify which canonical GET field contains a definition's full body. Root must
bind the actual canonical schema from a real readback and require that complete
body to match exactly. If it is missing, stop the canonical-body gate; do not
invent a field or claim full canonical readback from the publish job alone.

## Durable write-ahead journal and resume rules

Root implements the network transaction driver; this preparation deliberately
has no remotely executing mode. The existing Matrix script is a SOURCE example
for single-attempt proof writes, but its mission-reference assertions and
root-installed proof paths must not be copied for PF.

Hold one exclusive local publication-writer lock. Before each business POST,
perform the source/pin/version/identity gates again and persist:

1. The exact wire request body and Content-Type. JSON bodies are already encoded
   with the existing official Client.call settings. For multipart, choose the
   boundary once, append the raw proof bytes, and persist those exact bytes.
2. A journal intent containing a new operation UUID, UTC time, method/path,
   ENV, exact target name or canonical ID, new proposal context, source/proof
   hashes, body hash/length, and the complete independent-pin hash. Do not store
   authorization headers, tokens or credentials.
3. The pre-POST own-history snapshot and its hash, including known matching job
   or submission IDs, and the canonical target readback for proof submissions.

Write body and intent to new files, flush and fsync them, then atomically replace
the journal state. Send the POST only after this durable intent exists. Save the
full response before recording its job/submission ID. A crash between any of
these writes leaves a recoverable intent. A POST exception, malformed response,
missing ID, lost response or interrupted receipt write becomes
`UNKNOWN_REMOTE_OUTCOME`; never delete or clear the intent to permit a retry.

For unknown definition/problem writes, paginate the documented
`GET /publish-jobs?limit=...&offset=...` own history, including pending, published,
failed and error jobs. Inspect matching jobs with `GET /publish-jobs/{id}`.
Match kind, exact environment-scoped name, the complete definition or formal
statement/preamble, source metadata, and the intent/baseline interval. If ENV is
not exposed on a pending job, wait for its canonical terminal readback rather
than guessing its environment. Restore a receipt only from a unique exact
match; ambiguity or absence stays unresolved. Absence from a history page is
not proof that the POST did not reach the server.

For unknown proof writes, paginate documented `GET /submissions?page=N`,
100 per page, through its full `total`; retain pages and query each candidate
with `GET /verify?submission_id={id}`. Match the actual target, proof_type,
intent/baseline interval and any exact file identity the real history exposes.
The reviewed prove document does not promise returned proof bytes or their
hash. Therefore theorem ID plus timestamp or canonical Proved status alone
does not automatically prove that a candidate is this exact upload. If exact
file identity cannot be established, require an explicit Root recovery receipt
binding the real history/verdict evidence to the known upload hash; otherwise
keep the operation unresolved and do not automatically resubmit.

Known terminal FAILED/CE/WA/SORRY/ERROR results remain preserved as failures.
Although the docs allow retrying a confirmed infrastructure ERROR, this driver
must start a new explicitly authorized journal attempt referring to the known
terminal result; it must not auto-retry or reinterpret an unknown outcome as
ERROR. Poll pending jobs/submissions with bounded waits and no new POST.

After all three proofs are ACCEPTED, save a separate global-PF audit with the
three canonical IDs, exact statements/preambles/ENV, proof submission IDs and
payload hashes. Record `referenced_by_new_proposal=false`, no mission links,
the unchanged 88/18/69/67 proposal checkpoint, and Root's still-Open irrationality
goal. These finite PF results do not prove J, asymptotic heights or irrationality.

## Pure command and later gate

The final offline preparation has already run successfully. Its preserved
manifest prevents accidental regeneration. To check a future actual pin only:

```powershell
& 'C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe' `
  formalization/platform/coefficient-map-numerator-pf/publication-preparation-2026-10-07/prepare_publication_v2.py `
  --check-root-pin '<actual Root pin path>'
```

This is a pure file-hash gate, not a publish command. Root implements and reviews
the guarded, journaled network driver before any business POST.
