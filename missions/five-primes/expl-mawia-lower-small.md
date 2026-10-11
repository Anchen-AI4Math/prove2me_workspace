# Reduction of `TaoFivePrimes.mawia_reciprocal_sum_lower_bound_small`

Target `5cb6180b-3a9f-47fa-ae12-241767b2ba05`, the lower half of the finite-range
Mawia leaf created on 2026-09-25 by the split of `mawia_reciprocal_sum_bound`:

```
2 ≤ x → x ≤ 10^8 →
  log log x + (γ + Σ'_p (log (1 - 1/p) + 1/p)) - 4/(log x)^3 ≤ Σ_{p ≤ ⌊x⌋} 1/p
```

## What is registered

Two children, and the target's obligation becomes exactly these two:

| child | status | what it supplies |
|---|---|---|
| `TaoFivePrimes.rosser_schoenfeld_product_bound_lower` (`537dc0ba`, **new, Open**) | quoted | `e^γ log x < ∏_{p ≤ ⌊x⌋} p/(p-1)` for `2 ≤ x ≤ 10^8` |
| `TaoFivePrimes.mertens_tail_le_partial_sum` (`c10a0cd0`, **Proved**) | proved | `Σ'_p (log(1-1/p)+1/p) ≤ Σ_{p ≤ ⌊x⌋} (log(1-1/p)+1/p)` |

## The proof

With `P(x) = ∏_{p ≤ ⌊x⌋} p/(p-1)`, `T(x) = Σ_{p ≤ ⌊x⌋} (log(1-1/p) + 1/p)` and
`T(∞) = Σ'_p (log(1-1/p) + 1/p)`, the whole argument is one identity plus two
quotations.

**(1) The identity.** For a prime `p`, `p/(p-1) = (1 - 1/p)⁻¹`, so
`log(p/(p-1)) = -log(1 - 1/p)` and termwise

```
log(p/(p-1)) + (log(1 - 1/p) + 1/p) = 1/p .
```

Summing over `p ∈ Nat.primesLE ⌊x⌋₊` and applying `Real.log_prod` (legitimate:
every factor `p/(p-1)` is a nonzero real) gives **exactly**

```
Σ_{p ≤ ⌊x⌋} 1/p = log P(x) + T(x).
```

No approximation is involved; this is an equality of reals.

**(2) The new child, in logarithmic form.** `x ≥ 2` gives `log x > 0`, so the
child's strict inequality `e^γ log x < P(x)` survives `Real.log_lt_log`, and
`log(e^γ log x) = γ + log log x` by `Real.log_mul` + `Real.log_exp`. Hence

```
γ + log log x < log P(x).
```

**(3) The proved Mertens tail.** `mertens_tail_le_partial_sum` is `T(∞) ≤ T(x)`.

Adding (2) and (3) and substituting (1):

```
log log x + γ + T(∞) < log P(x) + T(x) = Σ_{p ≤ ⌊x⌋} 1/p .
```

Finally `4/(log x)^3 ≥ 0` for `x ≥ 2`, so the target's left-hand side is at most
`log log x + γ + T(∞)`, and the (strict) inequality above proves the claim.

## Why the lower half is cheap and the upper half is not

This is the one genuinely interesting point of this reduction, and it is worth
recording for whoever attacks the sibling `mawia_reciprocal_sum_upper_bound_small`.

The identity `Σ 1/p = log P + T(x)` is symmetric, but the two halves ask for
opposite information about the tail `δ(x) = T(x) - T(∞) ≥ 0`:

* lower half: needs `T(x) ≥ T(∞)`, i.e. `δ ≥ 0` — which is **precisely** what
  the already-Proved `mertens_tail_le_partial_sum` says. Free.
* upper half: needs `T(x) ≤ T(∞) + 4/(log x)^3`, i.e. an **upper** bound
  `δ(x) ≤ 1/(2⌊x⌋)` (from `|log(1-u)+u| ≤ u²/(2(1-u))` at `u = 1/p` and the
  telescoping `Σ_{n>N} 1/(n(n-1)) = 1/N`). That estimate is not on the platform
  yet and has to be proved from scratch.

So the lower half costs one quotation plus elementary algebra, while the upper
half needs the tail estimate and then a numerical comparison against the
published product bounds.

## Honest scope of the new citation child

`rosser_schoenfeld_product_bound_lower` is Rosser–Schoenfeld (1962), Illinois
J. Math. 6, 64–94, the lower half of the same calculation whose upper half is
already on the platform as `rosser_schoenfeld_product_bound_to_1e8` — that
node's own description names it explicitly as "the companion lower bound
`e^γ log x < ∏_{p≤x} p/(p-1)`". Secondary quotations: Lamzouri, *A bias in
Mertens' product formula*, arXiv:1410.3777, eq. (1.1) ("for all
`2 ≤ x ≤ 10^8`"); zbMATH review Zbl 1214.11102 of Diamond–Pintz (which renders
the pair as `e^{-γ}/(log x + 2/√x) < ∏(1-1/p) < e^{-γ}/log x` for
`2 ≤ x < 10^8`).

Two caveats, both recorded on the node itself:

1. **The range `10^8` is essential and must not be relaxed.** This is a
   computation carried out by Rosser and Schoenfeld up to `10^8`, not a theorem
   for all large `x`. Diamond–Pintz, *Oscillation of Mertens' product formula*,
   J. Théor. Nombres Bordeaux 21 (2009) 523–533, proved that
   `√x (∏_{p≤x} p/(p-1) − e^γ log x)` is unbounded above and below, so the
   inequality actually fails for arbitrarily large `x`.
2. **The margin is thin.** A sieve to `2·10^6` gives
   `min_{n ≤ 2·10^6} P(n)/(e^γ log n) = 1.000021`, attained at `n = 1772201`.
   True on the range checked, but only just.

Consequently this reduction does **not** transfer to
`mawia_reciprocal_sum_lower_bound_large` (`x ≥ 10^8`): that node needs the
large-range half of Mawia's estimate itself, and it stays Open.

## Verification

`lake env lean Solutions/Sol_TaoFivePrimes_mawia_reciprocal_sum_lower_bound_small.lean`
exits 0 with no diagnostics; the file contains no `sorry`, `axiom` or `unsafe`,
and its only non-Mathlib imports are the two platform nodes above.
