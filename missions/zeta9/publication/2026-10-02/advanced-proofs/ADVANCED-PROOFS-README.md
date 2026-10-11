# Zeta(9): advanced complete proof supplement, 2026-10-02

This is an independent, minimal Lean source project containing the complete
all-parameter C3 coefficient proof and the genuine PNT proof supporting three
unconditional harmonic-denominator endpoints. It supplements the earlier
nine-proof archive. Both that archive and the dated research ZIP are unchanged.
The original irrationality mission, its linear-form nonvanishing obligations,
and the required primitive decay remain open. This offline package makes no
claim about platform acceptance or publication of these new endpoints.

## What is proved

The finite coefficient is exactly

```
A(n,m) = 28 * sum(j=0..n, (-1)^(m+j)
  * choose(n,j)^3 * (choose(j+m,m)*choose(n-j+m,m))^7).
```

For every natural `d,m`, the checked lower bound is

```
28 * choose(2*d,d) * choose(3*d,d) * choose(d+m,m)^14
  <= (-1)^(m+d) * A(2*d,m).
```

For every even natural `n` and every natural `m`, the actual `A(n,m)` is nonzero.
This includes degree zero. The paper's even `n>=2` and `14*m<=3*n+1` domain
is a subset. It does not imply `A(n,m)*zeta(9)+B(n,m) != 0`.

For the actual rational harmonic sum `H(s,N)=sum(k=1..N, 1/k^s)` and actual
reduced rational denominator `den`, the three checked endpoints are:

1. For every fixed positive natural `s`, `log(den(H(s,N)))/N` tends to `s`.
2. If `log(den(r(N)))/N` tends to zero, then
   `log(den(H(s,N)+r(N)))/N` tends to the same `s`.
3. `log(den(H(9,2*M)))/M` tends to `18`.

The positive-order condition and the genuine sublinear perturbation-denominator
condition remain visible. No PNT hypothesis, lcm-rate hypothesis, harmonic
denominator baseline, or substitute positive coefficient is assumed by these
final endpoints. Whether a particular Mellin perturbation satisfies the small
denominator condition is a separate obligation.

## Source and trust boundary

`missions/zeta9/formalization/PNTTransfer.lean` is the finalized native source,
SHA256 `6c56d052ae48b44e76d40e7a08fcfd6ca8d232b5bc7882430bfbf48b85bb2c8b`.
It imports the actual `PrimeNumberTheoremAnd.MediumPNT` proof and derives the
literal Chebyshev psi limit. It then supplies both `ThetaPNT` and `LcmPNT`
inputs of the original conditional `HarmonicAsymptotic.lean` bridge. The latter
is retained unchanged and remains conditional when considered on its own.
The actual finite-prime interval, fixed exception product, and clearing bounds
are present in `HarmonicPrimeValuation.lean` and its real shared dependencies.

The entire actual MediumPNT import closure is vendored unchanged:

- 14 PNT modules, from
  `https://github.com/AlexKontorovich/PrimeNumberTheoremAnd` at
  `55270df807213fc3584523d09e0311d7dc073ff5`;
- 9 Architect modules, from
  `https://github.com/hanwenzhu/LeanArchitect` at
  `0f5bc0209ae02a7fb0cfe7d113d4094542cee221`.

The full upstream proofs, copyright headers, blueprint comments, and attributes
are preserved byte for byte. The two original Apache-2.0 licenses are in
`licenses/`; exact commits and file hashes are recorded in `UPSTREAM.json` and
the source manifest. Architect's original toolchain was Lean 4.33.0; its exact
source has actually compiled with this package's Lean 4.33.1. No MediumPNT
stub, `sorry`, or locally introduced axiom replaces the genuine PNT proof.

The C3 native proof is retained together with the lightweight definition and
both complete platform solutions. Its original disk SHA256 is
`9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc`.
Both staged solutions were produced with actual Lean declaration/reference
spans, retaining every mathematical helper. The exact original/staged types
and two definition values match. The dated paper still contains its historical
pre-formalization status; current build records are separate.

Two files in `Theorems/` are deliberate problem statement stubs and contain
`by sorry`. They compile separately for exact statement checking. No complete
solution, native PNT proof, or endpoint audit imports them. All actual endpoint
and solution axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## Rebuild

Required versions are fixed in `lean-toolchain` and `lake-manifest.json`:
Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, with
every transitive package revision recorded. The only unbundled code dependency
is this pinned Mathlib dependency tree. No other mission, external PNT source
directory, shared Solutions directory, or source-level cache is needed.

From this project's root, with those lock-file dependencies already installed:

```
python verify_package.py
python rebuild.py
```

Run `verify_package.py` before rebuilding, since the rebuild updates its audit logs.
`rebuild.py` builds one module at a time in import order and checks sixteen actual axiom reports,
including the explicit closed MediumPNT statement, native and staged C3,
literal psi/theta/lcm limits, and the three exact final harmonic endpoints.
The recorded sequential standalone build compiled all 23 vendored upstream
modules and the native task modules in this independent project. Its earlier
run stopped after 31 successful steps without a final receipt; the resumed run
verified those sources and cached artifacts, compiled the remaining native
proofs and audits, and completed the final `lake --no-cache build Audit Theorems`.
Only the already installed pinned Mathlib dependency directory was borrowed;
no PNT/task cache from another project was borrowed. The first parallel attempt
failed with memory exhaustion and is retained as historical failure evidence.
`audit/standalone-rebuild/` contains the actual combined log and receipts.

For an offline Windows rebuild using an existing matching dependency tree,
create `.lake` and a directory junction `.lake/packages` to that tree before
building. The junction is only local setup and is not in the archive. Keep
`LEAN_PATH` unset so imports resolve through this project's own library graph.

`source-manifest.json` records every payload member and source hash. The manifest
itself is excluded from its own payload list. `SHA256SUMS.txt` accompanies the ZIP.
`package-validation.json` accompanies the ZIP and checks its exact member
set, bytes, reviewed source hashes, fixed upstream hashes, licenses, and the
unchanged earlier attachments. The archive contains no credentials, API/auth
receipts, `.git`, `.lake`, `.olean`, binaries, or dependency cache.
