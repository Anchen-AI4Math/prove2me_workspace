# `TaoFivePrimes.mertens_tail_upper` — the Mertens correction tail is at most `1/⌊x⌋`

This submission **proves** (not reduces, not quotes) the node. The file
`Solutions/Sol_TaoFivePrimes_mertens_tail_upper.lean` (270 lines,
sha256 `fd05282f492ac06bd3a864b6edd2bc7768d69cacb6f0b9e80f6cb569bf6cb455`)
compiles under `lake env lean` with exit 0 and contains no `sorry`, `axiom` or
`unsafe`.

## Statement

With `N = ⌊x⌋`,

```
T(N)   = ∑_{p ≤ N} (log (1 - 1/p) + 1/p)
T(∞)   = ∑'_p       (log (1 - 1/p) + 1/p)
```

the node asserts `T(N) − T(∞) ≤ 1/N` for `x ≥ 2`.

It is the exact companion of the already-Proved
`TaoFivePrimes.mertens_tail_le_partial_sum`, which is the opposite inequality
`T(∞) ≤ T(N)`. Read together: the correction sum overshoots its limit by a
nonnegative amount of size at most `1/N`.

## Why this is the missing piece

The Mawia reciprocal-prime estimates go through the *exact* identity

```
∑_{p ≤ x} 1/p = log ∏_{p ≤ x} p/(p-1) + T(N),
```

which is just `p/(p−1) = (1−1/p)⁻¹` term by term plus `Real.log_prod`. So both
halves need information about `δ = T(N) − T(∞)`, in *opposite* directions:

* the **lower** half needs `δ ≥ 0`, and that is literally the Proved
  `mertens_tail_le_partial_sum` — which is why the lower half of the small range
  cost two quotations and nothing else;
* the **upper** half needs `δ` bounded **above**, and nothing on the platform
  supplied that. This node supplies it.

## The proof

Put `u = 1/p`. For `0 ≤ u < 1`, the two standard logarithm inequalities

```
1 − (1−u)⁻¹ ≤ log (1−u)        (Real.one_sub_inv_le_log_of_pos)
log (1−u)   ≤ (1−u) − 1 = −u   (Real.log_le_sub_one_of_pos)
```

give, first, `log(1−u) + u ≤ 0`: every correction term is nonpositive, so the
partial sums `T(N)` decrease towards `T(∞)` (this is the nonnegativity of the
gap, needed to apply the partial-sum characterisation of `tsum`). Second,

```
0 ≤ −(log(1−u) + u) ≤ −1 + (1−u)⁻¹ − u = u²/(1−u) = 1/(p(p−1)).
```

Because `1/(p(p−1)) = 1/(p−1) − 1/p` telescopes, the tail over *all* integers
above `N` sums to exactly `1/N`, and the prime-supported tail is dominated by it:

```
δ = ∑_{p>N} −(log(1−1/p) + 1/p) ≤ ∑_{n>N} (1/(n−1) − 1/n) = 1/N.
```

No prime number theorem, no numerical certificate and no external citation is
used. The single lossy step — replacing a sum over primes by a sum over all
integers — is precisely what produces the constant `1`.

**Infinite sums.** `Real.tsum_le_of_sum_range_le` bounds a `tsum` of a
nonnegative sequence by a uniform bound on its finite partial sums, so the tail
estimate needs no separate summability proof. The split of `∑'_n` into the head
`n < N+1` and the tail uses `Summable.sum_add_tsum_nat_add`, with summability
obtained from `summable_of_sum_range_le` applied to the *shifted* sequence.
`tsum_subtype` moves `∑' p : Nat.Primes` to a sum over `ℕ` with a prime
indicator, and `Nat.primesLE N = (N+1).primesBelow` identifies the head with the
sum over primes `p ≤ N`.

## A factor of two is deliberately left on the table

The **sharp** constant is `1/(2N)`. It comes from the second-order estimate
`|log(1−u) + u| ≤ u²/(2(1−u))`, which after the substitution `x = (1−u)⁻¹ ≥ 1`
is the classical

```
log x ≤ (x − 1/x)/2        for x ≥ 1,
```

whose proof is one line of calculus: the derivative of the difference is
`(x−1)²/(2x²) ≥ 0` and both sides vanish at `x = 1`. That yields
`δ ≤ ∑_{p>N} 1/(2p(p−1)) ≤ 1/(2N)`.

Its formalisation needs a monotonicity/derivative argument
(`monotoneOn_of_deriv_nonneg` on `Ici 1`, or an equivalent `HasDerivAt`
computation), so this node states the derivative-free `1/N` form. The weaker
constant is already sufficient for the intended applications (see below), and
the strengthening is a clean, self-contained follow-up node.

## Measured effect on `mawia_reciprocal_sum_upper_bound_small`

Reducing the upper half requires, for every `x` in range,

```
excess(x) + δ(N) ≤ 4 / log³ x,
```

where `excess` is what the quoted product bound gives for
`log P(N) − γ − loglog x`. Two product bounds are already Proved:

| form | node | range | excess |
|---|---|---|---|
| (4.10) | `rosser_schoenfeld_product_bound_to_1e8` | `0 < x ≤ 10⁸` | `log(1 + 2/(√x log x))` |
| (3.29) | `rosser_schoenfeld_product_log_bound_mid` (`700 ≤ x ≤ 10⁸`), `rosser_schoenfeld_product_bound_286_to_700` | `286 ≤ x ≤ 10⁸` | `log(1 + 1/(2 log² x))` |

Scanning `⌊x⌋` over `[2, 10⁸]` with `δ ≤ 1/N` (this node) gives:

* (3.29)-form holds for `⌊x⌋ ≤ 1978`, so it covers **`286 ≤ x ≤ 1978`**;
* (4.10)-form holds for `⌊x⌋ ≤ 7` and for `⌊x⌋ ≥ 450`, so it covers
  **`450 ≤ x ≤ 10⁸`**.

Together: **`286 ≤ x ≤ 10⁸` is now closable from Proved nodes alone.** With the
sharp `1/(2N)` the same computation gives (3.29) up to `2544` and (4.10) from
`313`, i.e. the same qualitative coverage — the factor of two is not what blocks
the small range.

**The residue `2 ≤ x < 286` is not covered, and cannot be by these two forms.**
A sieve check shows the (4.10) form already fails at `x ≈ 12` and only recovers
at `x ≈ 450`; and the (3.29) form is *false* below 286 — at `x = 20` it would
require `∏_{p≤19} p/(p−1) < 4.785` while the product is `5.848`, which is
exactly why Rosser and Schoenfeld state (3.29) only for `x ≥ 286`. Closing the
residue needs its own small-range bound (a finite certification over the 61
primes `p ≤ 283`, in the style of the already-Proved
`rosser_schoenfeld_product_bound_to_286`); that is a separate node and is not
claimed here.
