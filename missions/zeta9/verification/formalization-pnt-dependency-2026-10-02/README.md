# Actual fixed-source PNT kernel replay — 2026-10-02

This directory records an actual local replay of the upstream
`PrimeNumberTheoremAnd.MediumPNT` import closure, rather than a PNT axiom,
copied sorry target, or uncompiled source claim.

The mathematical source is fixed at PNT commit
`55270df807213fc3584523d09e0311d7dc073ff5`: fourteen source modules.
Its blueprint tool is fixed at LeanArchitect commit
`0f5bc0209ae02a7fb0cfe7d113d4094542cee221`: nine actual imported modules.
The isolated project uses Lean **4.33.1** and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, exactly matching the mission's
existing verified environment.

All twenty-three source files are byte-for-byte identical to the recorded
fixed upstream snapshots. Blueprint attributes, comments, and their real
Architect implementation are retained. There are no mathematical proof edits,
custom axioms, or introduced sorry placeholders. The source and dependency
manifests record every file hash. Upstream licenses are copied separately.

`kernel-build.log` records the actual command

```text
lake --no-cache build PrimeNumberTheoremAnd.MediumPNT
```

It completed successfully. The original source prints the actual axiom
dependencies of `MediumPNT`. `PNTKernelAudit.lean` independently imports the
built theorem and verifies an explicit closed statement:

`∃ c > 0, psi(x) - x = O(x exp(-c (log x)^(1/10)))`.

No additional assumption supplies this statement. The separate audit prints
both the upstream theorem's and wrapper theorem's axiom dependencies.
`kernel-replay-receipt.json` summarizes the checked build exit, source fidelity,
closed statement, standard axiom reports and evidence hashes.

The first attempt exposed an isolated Lake configuration omission:
`.submodules Architect` excludes the root `Architect` module. The correction
adds the explicit `.one Architect` glob, with the failed-attempt log preserved.
It changes package registration only. All original mathematical and Architect
sources remain unchanged. The Architect snapshot's own toolchain says 4.33.0;
its compatibility with the required 4.33.1 is established by this actual build.

The isolated project reuses only already installed exact pinned dependencies
through a checked `.lake/packages` junction. Build-cache downloads were
disabled; no network or platform call and no shared environment upgrade occurs
in this replay. Upstream deprecated-lemma warnings are preserved.

This verifies the genuine external PNT input needed by the harmonic denominator
route. Transfer from its psi-error theorem to theta/LCM rates and then the
actual harmonic baseline is a separate checked bridge. This local replay does
not itself claim platform acceptance or close the zeta(9) irrationality goal.
