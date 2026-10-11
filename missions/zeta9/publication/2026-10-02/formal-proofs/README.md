# Zeta(9): nine reviewed complete Lean proofs

Snapshot date: 2026-10-02. This attachment supplements the immutable research
release; it does not replace or modify `zeta9-research-2026-10-02.zip`.

There are exactly **four shared Definitions files and nine complete Solutions
files**. Their bytes equal the frozen independently reviewed and task-built
workspace sources, with SHA-256 recorded in `source-manifest.json`. Every
top-level `solution` has an actual Lean 4.33.1 axiom report containing only
`propext`, `Classical.choice`, and `Quot.sound`. No reference theorem stubs
are included or imported by these solution modules.

Platform state at this handoff: submitted definitions are **Pending** and the
main `ZetaNine.irrational_zeta_nine` goal remains **Open**. Local compilation
does not assert platform acceptance, published theorem proof status, a full
formalization of all research, or a proof of irrationality.

## Nine locally verified target solutions

- `ZetaNine.GramContent.primitive_row_gram_gcd_dvd_scaled_saturated`
- `ZetaNine.CenterDenominator.primitive_center_denominator_divisor`
- `ZetaNine.EightfoldZeros.first_n_derivative_sum_zero`
- `ZetaNine.HarmonicStability.harmonic_den_dvd_lcm_power`
- `ZetaNine.HarmonicStability.log_den_error_tendsto_zero`
- `ZetaNine.HarmonicStability.log_den_rate_stability`
- `ZetaNine.HarmonicStability.harmonic_finite_prime_product_dvd`
- `ZetaNine.HarmonicStability.harmonic_finite_prime_log_lower_bound`
- `ZetaNine.HarmonicStability.harmonic_large_prime_den_valuation`

The six first-batch and three prime-valuation targets retain every original
parameter and hypothesis. The arbitrary-filter stability theorem retains its
explicit unperturbed-rate input; the finite prime theorems retain their real
prefix numerator-unit and fixed exceptional-product conditions. No denominator
estimate or asymptotic claim is hidden in a definition.

## Rebuild

Install Lean using the included `lean-toolchain` (version 4.33.1). Mathlib is
fixed at `0df444a360eaa60ab8c11dca51a86af692955474`; every transitive package
revision is pinned in `lake-manifest.json`.

From this extracted directory:

```text
lake exe cache get
lake build Solutions
python verify_package.py
```

Dependency acquisition requires network access when the pinned dependencies
and their cache are not already installed. No Lean toolchain, Mathlib source,
dependency cache, `.olean`, `.git`, credentials or account receipts are bundled.
This minimal `Solutions` target contains exactly the nine proofs above and
their four actual definition dependencies; it is unrelated to any aggregate
target of the original multi-mission workspace.

The two original scoped build logs contain warning lines from deliberately
registered target stubs elsewhere in the original zeta9 task. Those stubs are
absent from this package. The relevant nine Solutions axiom lines are all
standard only. A pre-existing linter warning in the frozen center-denominator
proof is preserved rather than modifying its reviewed source bytes.

The fresh isolated rebuild of this exact minimal project is recorded under
`audit/package-rebuild`. It rebuilt all thirteen shared modules, with nine
standard-only solution axiom reports and no target theorem stubs. It used
already installed exact pinned dependencies outside the archive and disabled
network build-cache downloads. No dependency source or cache is bundled.

## Conditional harmonic appendix

`missions/zeta9/formalization/HarmonicAsymptotic.lean` is additional checked
research source, **not a tenth registered solution**. It derives the actual
full harmonic denominator rate and its perturbation transfer, including the
order-nine `N=2M` rate 18, from exactly two explicit PNT inputs:

- `Chebyshev.theta x / x → 1` as real `x → ∞`;
- `log (Nat.lcmUpto N) / N → 1` as natural `N → ∞`.

These are theorem arguments. There is no assumed harmonic baseline, custom
PNT axiom or claim to have proved PNT. The fixed Mathlib PNT theorem search
and actual compilation evidence are under `audit/conditional-harmonic-transfer`.
The original finite-prime source is included solely as its actual import
dependency, without cached binary files. After the main rebuild, compile
the appendix from this directory in PowerShell:

```powershell
lake env lean -o missions/zeta9/formalization/HarmonicPrimeValuation.olean missions/zeta9/formalization/HarmonicPrimeValuation.lean
$env:LEAN_PATH = (Get-Location).Path
lake env lean missions/zeta9/formalization/HarmonicAsymptotic.lean
```

## Evidence and integrity

The `audit` directory contains only the current independent mathematical
reviews, exact source-match audits and actual build logs. Original mathematical
notes are under `research`; their wider research links refer to the separate
dated research release rather than promising those linked files in this small
proof attachment. Documentation and audits distinguish written mathematics,
local Lean verification, outstanding PNT dependencies and platform acceptance.

`source-manifest.json` lists each package member's exact size, SHA-256 and
provenance. It excludes itself to avoid a self-referential digest. The archive's
SHA-256 and packaging verification report are provided alongside the ZIP.
