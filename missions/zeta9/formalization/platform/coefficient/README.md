# C3 coefficient platform transplant, 2026-10-02

This batch contains one lightweight definition bundle and two complete local
solutions for the actual finite short-zero coefficient. It has not been
submitted by this preparation workflow and makes no platform acceptance claim.
The main irrationality mission remains open.

The original source is `missions/zeta9/formalization/ShortZeroCoefficient.lean`,
SHA256 `9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc`.
The dated research note in `research/short-zero-coefficient-nonvanishing.md`
still describes its 2026-09-28 pre-formalization state; the separate current
compile receipt records the new complete proof.

## Mathematical boundary

For all natural numbers `d,m`, the first solution proves

```
28 * choose(2*d,d) * choose(3*d,d) * choose(d+m,m)^14
  <= (-1)^(m+d) * A(2*d,m).
```

For all natural numbers `n,m` with `Even n`, the second solution proves
`A(n,m) != 0`. The definitions are the original natural binomial weight and
the original integer finite sum `28 * sum (-1)^(m+j) * weight(n,m,3,7,j)`.
The results include degree zero and every `m`; the paper's analytic domain
`n>=2`, even `n`, and `14*m<=3*n+1` is a subset. This concerns coefficient
nonvanishing only. It proves neither nonvanishing of `A*zeta(9)+B` nor its
primitive decay nor irrationality.

The complete helper proofs, including the actual cubic Franel polynomial
identity, its differential-operator certificate, gamma positivity and exact
factorial-normalized weight blocks, are retained in each solution. No Franel,
positivity, lower-bound, or coefficient nonvanishing hypothesis is added.

## Real Lean extraction and exact comparison

The official `scripts/extract_decl_graph.lean` and
`scripts/extract_sketch_info.lean` were copied into this task directory and
actually executed under Lean 4.33.1. Stage 1 reports 145 declarations and
Stage 2 reports 104 declaration facts and 578 reference facts. Every source
cut, proof boundary, documentation cut, and target rename uses these facts.
No regular expression is used to locate mathematical declarations or references.

Stage 1 was configured with the source module import and module-name prefix
and a task-local output path. Stage 2's extraction logic is unchanged; its
only instrumentation persists `Parser.mkInputContext.inputString` with
`IO.FS.writeBinFile`. Lean's parser defaults to `normalizeLineEndings=true`:
it converts the original 882 CRLF pairs to LF. Thus offsets address the exact
42,783-byte `oracle-input.lean`; the 43,665-byte original source is unchanged.

Each full solution is that actual parser input minus only the two definition
spans, with the target's binding/reference spans renamed to `checked_*`,
followed by a top-level `solution` with the exact original signature. The
registered `Theorems/` files are intentional compiling problem stubs. The
full `Solutions/` files import only the real shared definition and Mathlib,
and never import those stubs.

Six separate `run_meta` reports pretty-print the elaborated original types,
definition types and values, two reference types, and two solution types.
All comparisons are exactly equal, with universes hidden consistently.
The first report attempt used `TermElabM` where `run_meta` requires `MetaM`;
that auxiliary collector was corrected and its failed diagnostics are
preserved in `type-report-initial/`. No proof was changed for this repair.

`staged-build.log` records the actual five-module build and both final
`#print axioms solution` reports: only `propext`, `Classical.choice`, and
`Quot.sound`. `integration-audit.json` is the author-side audit;
`independent-integration-review.json` is supplied separately by an independent
reviewer. The parent task owns scope registration and the final scoped build.

## Offline replay

Run from the workspace root with the existing pinned Lean/Mathlib environment:

```powershell
$env:LEAN_PATH = (Get-Location).Path
lake env lean -o missions/zeta9/formalization/ShortZeroCoefficient.olean missions/zeta9/formalization/ShortZeroCoefficient.lean
lake env lean missions/zeta9/formalization/platform/coefficient/extract_decl_graph.lean
lake env lean --run missions/zeta9/formalization/platform/coefficient/extract_sketch_info.lean missions/zeta9/formalization/ShortZeroCoefficient.lean ZetaNine > missions/zeta9/formalization/platform/coefficient/sketch_info.jsonl
python missions/zeta9/formalization/platform/coefficient/prepare_coefficient.py
lake build Definitions.Def_ZetaNine_ShortZeroCoefficient Theorems.Thm_ZetaNine_ShortZeroCoefficient_A_even_signed_lower Theorems.Thm_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even Solutions.Sol_ZetaNine_ShortZeroCoefficient_A_even_signed_lower Solutions.Sol_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even
```

The six `types_*.lean` report sources can then be compiled separately with
`lake env lean`; their recorded JSONL reports and exit codes are retained.
`audit_coefficient.py` checks exact reconstructed proof bytes, payload/file
identity, types, definition values, real axiom reports, and the hashes of the
previous two frozen batches and nine-proof attachment. `SHA256SUMS.txt`
records the prepared payloads, shared modules, original source, oracle facts,
and verification inputs. No credentials, API, or network operations are used.
