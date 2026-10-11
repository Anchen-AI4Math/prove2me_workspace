# `TaoFivePrimes.mertens_tail_upper_bound` — proof and role

New node `457799a9-007d-4dcc-ba30-dfe80f5f2787`, the missing *upper* half of the
tail estimate whose *lower* half is the already-Proved
`TaoFivePrimes.mertens_tail_le_partial_sum` (`c10a0cd0`).

```
1 ≤ x →
  Σ_{p ≤ ⌊x⌋} (log (1 - 1/p) + 1/p)
    ≤ (Σ'_p (log (1 - 1/p) + 1/p)) + 1/⌊x⌋
```

With `T(x) = Σ_{p ≤ ⌊x⌋} (log(1-1/p) + 1/p)` and `T(∞) = Σ'_p (log(1-1/p)+1/p)`
this reads `0 ≤ δ(x) := T(x) - T(∞) ≤ 1/⌊x⌋`. The lower inequality `δ ≥ 0` is
exactly `c10a0cd0`; the upper one is new.

## Why it matters

`mertens_tail_le_partial_sum` was already used, in
`expl-mawia-lower-small.md`, to close the **lower** half of the Mawia leaf: the
identity

```
Σ_{p ≤ ⌊x⌋} 1/p = log P(x) + T(x),     P(x) = ∏_{p ≤ ⌊x⌋} p/(p-1)
```

turns a bound on `log P(x)` into a bound on `Σ 1/p`, but the `T(x)` that appears
is the *finite* partial sum, whereas the constant that appears in the target is
`B = γ + T(∞)`. For the lower half `T(∞) ≤ T(x)` is exactly what is needed and
it is free. For the **upper** half one needs the reverse comparison
`T(x) ≤ T(∞) + (small)`, and that did not exist on the platform. This node
supplies it.

## The proof

Purely elementary; `import Mathlib` only, no quoted input, no prime counting,
no numerical constant.

1. **Term estimate.** `Real.abs_log_sub_add_sum_range_le` at `u = 1/p` with one
   Taylor term gives `|log(1-u) + u| ≤ u²/(1-u)`, i.e.

   ```
   |log (1 - 1/p) + 1/p| ≤ 1/(p(p-1)).
   ```

2. **Sign.** `Real.log_le_sub_one_of_pos` gives `log(1-u) ≤ -u`, so every term
   is `≤ 0`; hence `T` decreases towards `T(∞)` and
   `δ(x) = Σ_{p > ⌊x⌋} |log(1-1/p) + 1/p|`.

3. **Zero extension and splitting.** Extend the summand by `0` off the primes
   (`Set.indicator`), convert the subtype `tsum` with `tsum_subtype`, and split
   at `N+1` with `Summable.sum_add_tsum_nat_add`. Summability is by comparison
   with `2/n²`, using `Real.summable_one_div_nat_pow`.

4. **Telescoping.** Dropping the primality constraint,

   ```
   δ(x) ≤ Σ_{n>N} 1/(n(n-1)) = Σ_{n≥0} 1/((n+N)(n+N+1)),
   ```

   and `1/((n+N)(n+N+1)) = 1/(n+N) - 1/(n+N+1)` telescopes: the partial sums are
   `1/N - 1/(M+N)` by `Finset.sum_range_sub'`, and
   `hasSum_iff_tendsto_nat_of_nonneg` plus `tendsto_inv_atTop_zero` sends
   `1/(M+N) → 0`, giving `HasSum … (1/N)`.

**Honest scope.** The constant is `1`, not the sharper `1/2` that
`|log(1-u)+u| ≤ u²/(2(1-u))` would give; the missing factor 2 comes from the
Mathlib remainder lemma, which supplies `u²/(1-u)`. We did not sharpen it
because (numerically checked) the factor 2 changes no downstream conclusion on
this mission. Unlike the Rosser–Schoenfeld product bounds, this estimate is
valid for **all** `x ≥ 1` — it is not a finite-range computation.

## What it closes, and what it does not

Numerical check (real arithmetic, not a formal proof):

| range | product bound used | requirement `ε(x) + 1/⌊x⌋ ≤ 4/(log x)³` |
|---|---|---|
| `286 ≤ x < 700` | `rosser_schoenfeld_product_bound_286_to_700` (**Proved**), `e^γ log x (1 + 1/(2log²x))` | holds on every integer, min slack `1.3·10⁻³` at `x = 700` |
| `700 ≤ x ≤ 10^8` | `rosser_schoenfeld_product_log_bound_mid` (**Proved**), `γ + log log x + log(1 + 1/(2log²x))` | holds on every integer up to `10^8` |
| `2 ≤ x < 286` | `rosser_schoenfeld_product_bound_to_286` (**Proved**), only `e^γ log x + 2e^γ/√x` | **fails** on 276 of the 284 integers; max deficit `4.1·10⁻²` at `x = 18` |

So this node, together with nodes that are *already Proved*, is sufficient for
`TaoFivePrimes.mawia_reciprocal_sum_upper_bound_small` (`6b4f23b2`) on
`286 ≤ x ≤ 10^8`. It is **not** sufficient on `2 ≤ x < 286`, and no
refinement of the tail bound can fix that: at `x = 27` the Rosser–Schoenfeld
error term alone (`2/√x`/`log x` ≈ `0.117`) already exceeds the whole budget
`4/(log x)³ ≈ 0.112`. Closing that sub-range needs either

* a `(1 + 1/(2 log² x))`-form product bound valid below `286` — note it is
  **false** at `x = 3`, so it cannot simply be extended downwards; or
* a direct finite verification of the target over `⌊x⌋ ∈ {2,…,285}`.

## Verification

`lake env lean Solutions/Sol_TaoFivePrimes_mertens_tail_upper_bound.lean`
exits 0 with no diagnostics; the file contains no `sorry`, `axiom` or `unsafe`,
and its only import is `Mathlib`.
