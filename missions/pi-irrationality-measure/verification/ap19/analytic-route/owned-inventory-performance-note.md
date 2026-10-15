# AP19 owned-CI snapshot performance (read-only diagnosis)

The frozen five-context analytic reduction passed. Its generated metadata
snapshot took **269.422 s** of the 300 s file budget, while the source
snapshot took **30.406 s** and the emitted solution took **42.906 s**.
The generated raw-owned inventory contains exactly three CIs (the two Open
children and `solution`). A separate four-Definition provider showed the same
pattern: its generated snapshot took **286.438 s**, while its source snapshot
took **31.047 s**. These are actual bounded sidecar timings, not a profiler
breakdown.

The strongest code-level explanation is the generated inventory's full
`env.constants.toList` traversal in
`scripts/finalize_analytic_aggregate_two_child_reduction.py`. For every
constant in the imported Mathlib environment it calls
`env.getModuleIdxFor?`, looks up and stringifies its owner, then tests
membership in three target modules. It resolves owners again for the three
matches. The full enumeration and per-constant owner work are unique to the
slow generated snapshot; the small output and nearby source/solution timings
make them the likely bottleneck. `Lean.collectAxioms` and expression export for
the three matches may contribute, but no timing probe separates those costs.

For a **future isolated stage only**, retain a complete scan of actual
constants but resolve the three target module names to module indices once.
Compare `getModuleIdxFor?` indices during the scan, keep each matched
`(name, CI, owner)` tuple, and build JSON only after the scan. This removes
per-constant module-name conversion and the second owner lookup without
assuming any declaration prefix or suffix. If the Lean environment supports
a streaming constant-map fold, it can additionally avoid materializing
`env.constants.toList`; that API must be checked before use. Preserve the
sorted full owned-name list and reject every unexpected public or private CI
in the consumer. A prefix-only filter would be faster but would not establish
completeness for private names or compiler-generated caches.

The expected speedup is **unmeasured**. A new isolated, <=300 s metadata
preflight must compare its complete owned-CI names and full rows with the
frozen AP19 inventory before relying on the optimization. The existing AP19
five inputs, sidecars, certificate, and original source files remain
unchanged.
