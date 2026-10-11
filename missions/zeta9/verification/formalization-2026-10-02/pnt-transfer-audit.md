# Actual PNT to harmonic denominator growth: verified unconditional endpoint

Date: 2026-10-02.

Source: `../../formalization/PNTTransfer.lean`.
SHA-256: `6c56d052ae48b44e76d40e7a08fcfd6ca8d232b5bc7882430bfbf48b85bb2c8b`.
Imported task source: `../../formalization/HarmonicAsymptotic.lean`,
SHA-256 `d5de9615948820367823fed4128cbf7aedea75b3c42b1a1134cc6c4213a30fca`.

The original definitions `ThetaPNT` and `LcmPNT` are imported unchanged.
No substitute PNT objects, project axioms, or denominator-rate premises
are introduced.

The file now genuinely imports `PrimeNumberTheoremAnd.MediumPNT` from
the separately kernel-replayed original dependency, repository
`https://github.com/AlexKontorovich/PrimeNumberTheoremAnd`, fixed commit
`55270df807213fc3584523d09e0311d7dc073ff5`. The original theorem is used
as an actual compiled theorem, never as a hypothesis or a statement stub.

The actual compilation command, from the workspace root, was:

```
lake env pwsh -NoProfile -Command '$env:LEAN_PATH = $env:LEAN_PATH + [IO.Path]::PathSeparator + "D:\users\self_projects\prove2me_workspace" + [IO.Path]::PathSeparator + "D:\users\self_projects\prove2me_workspace\missions\zeta9\verification\formalization-pnt-dependency-2026-10-02\project\.lake\build\lib\lean"; lean -o missions/zeta9/formalization/PNTTransfer.olean missions/zeta9/formalization/PNTTransfer.lean'
```

Final exit code: **0**, with no warnings or errors. Actual compiler output
is saved in `pnt-transfer-final-lean.log`; all thirteen printed theorems depend only
on `propext`, `Classical.choice`, and `Quot.sound`.
The machine-readable final command/hash/axiom receipt is
`pnt-transfer-final-receipt.json`.

The source proves:

1. Unconditionally, `(Chebyshev.psi x - Chebyshev.theta x)/x → 0`.
   Mathlib supplies the actual bound `psi-theta = O(sqrt x)`. The source
   proves `sqrt x / x → 0` from the exact reciprocal square-root identity,
   converts it to little-o, and composes the proved bounds.
2. If the actual `Chebyshev.psi x / x → 1`, then the existing `ThetaPNT`
   follows by subtraction of that normalized error.
3. Under the same actual psi rate, the existing `LcmPNT` follows by natural
   endpoint reindexing and Mathlib's exact equality
   `Chebyshev.psi (N : ℝ) = Real.log (Nat.lcmUpto N : ℝ)`.
4. The imported original `MediumPNT` theorem supplies a positive `c` and
   the actual error bound
   `psi-id = O(x exp(-c(log x)^(1/10)))`. The source proves that the
   relative exponential factor tends to zero, composes this bound with
   little-o, and derives the literal actual `psi x / x → 1`.
5. Consequently both original PNT inputs are proved without hypotheses.
   Applying the already proved finite arithmetic and fixed-exception
   argument gives the unconditional original full-sequence baseline
   `log den(H_N^(s))/N → s` for every fixed positive natural `s`.
6. The original rational perturbation corollary is unconditional on PNT
   and the harmonic baseline. Only its necessary, genuine hypothesis
   `log den(r_N)/N → 0` remains.
7. The original order-nine double-endpoint rate tends to **18**, now
   with no PNT or harmonic-baseline premise at all.

This closes the original harmonic denominator theorem and perturbation
corollary at the local Lean-kernel level. Platform integration and its
acceptance are separate root tasks. The source does not establish that
every Mellin perturbation satisfies the required small-denominator
condition, and does not prove J/S or the irrationality of zeta(9).

Import handling: task `.olean` files were generated only under this task.
The workspace root is appended after Lake's build-library paths, so the
already built shared `Definitions` and `Solutions` modules take precedence.
No frozen source, platform request, scope file, or shared source was changed.
