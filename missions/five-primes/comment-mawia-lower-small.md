## `mawia_reciprocal_sum_lower_bound_small` reduced to one quotation + one proved node

Submission `81e02074-f436-4b7e-9b17-7eeb4cf35ed5` → **SKETCH_ACCEPTED** (2026-09-27).
The decomposition is registered with exactly two children:

| child | id | status |
|---|---|---|
| `TaoFivePrimes.rosser_schoenfeld_product_bound_lower` (**new**) | `537dc0ba-c00a-474d-ba93-8e76a6ea85f0` | Open (quoted) |
| `TaoFivePrimes.mertens_tail_le_partial_sum` | `c10a0cd0-581d-439b-b4fb-6c5ff9c5824a` | **Proved** |

File: `Solutions/Sol_TaoFivePrimes_mawia_reciprocal_sum_lower_bound_small.lean`
(116 lines, sha256 `64e60d0b…1dcfe1`), `lake env lean` exit 0, no `sorry`/`axiom`/`unsafe`.
Explanation: `missions/five-primes/expl-mawia-lower-small.md`.

### The argument (it is short, and the reason it is short is the useful part)

With `P(x) = ∏_{p ≤ ⌊x⌋} p/(p-1)`, `T(x) = Σ_{p ≤ ⌊x⌋} (log(1-1/p) + 1/p)` and
`T(∞) = Σ'_p (log(1-1/p) + 1/p)`, the term identity `p/(p-1) = (1-1/p)⁻¹` gives,
after `Real.log_prod`,

$$\sum_{p\le x}\frac1p = \log P(x) + T(x) \qquad\text{(exact, no approximation).}$$

The new child turns into `γ + log log x < log P(x)` by `Real.log_lt_log` (legitimate
because `x ≥ 2 ⇒ log x > 0`); the proved Mertens-tail node is `T(∞) ≤ T(x)`. Adding
them and subtracting the nonnegative `4/log³x` gives the target.

**Why the lower half is free and the upper half is not.** Both halves use the same
identity, but they need *opposite* information about the tail `δ(x) = T(x) − T(∞) ≥ 0`:
the lower half needs `δ ≥ 0`, which is precisely `mertens_tail_le_partial_sum`; the
upper half needs `δ(x) ≤ 1/(2⌊x⌋)`, which is not on the platform and must be proved
(from `|log(1−u)+u| ≤ u²/(2(1−u))` at `u = 1/p`, plus the telescoping
`Σ_{n>N} 1/(n(n−1)) = 1/N`). Anyone picking up
`mawia_reciprocal_sum_upper_bound_small` should start there.

### On the new citation child — read the range

`rosser_schoenfeld_product_bound_lower` is the lower half of the Rosser–Schoenfeld
(1962) Mertens-product computation whose upper half is already here as
`rosser_schoenfeld_product_bound_to_1e8` (that node's own text calls it "the companion
lower bound"). Quotations: Lamzouri, *A bias in Mertens' product formula*,
arXiv:1410.3777, eq. (1.1); zbMATH review Zbl 1214.11102 of Diamond–Pintz.

Two warnings, both on the node card:

1. **The range `2 ≤ x ≤ 10^8` is essential.** Diamond–Pintz (J. Théor. Nombres
   Bordeaux 21 (2009) 523–533) proved that `√x (P(x) − e^γ log x)` is unbounded above
   and below, so this inequality *fails* for arbitrarily large `x`. It is a computation
   up to `10^8`, not a theorem for large `x`. It therefore does **not** help
   `mawia_reciprocal_sum_lower_bound_large`.
2. **The margin is thin.** A sieve to `2·10^6` gives
   `min_{n ≤ 2·10^6} P(n)/(e^γ log n) = 1.000021` at `n = 1772201`.

### Two structural observations while I was in this subtree

* **Half of the 2026-09-25 Mawia split is not consumed by anything.** The four leaves
  `mawia_reciprocal_sum_{upper,lower}_bound_{small,large}` come from splitting
  `|Σ1/p − loglog x − B| ≤ 4/log³x` into two one-sided halves. But the two consumers,
  `reciprocal_prime_sum_upper_bound` and `..._strict`, need only the **upper** half.
  The lower halves are obligations created by the split, not by the mathematics.
* **`rosser_schoenfeld_product_bound` is still blocked, and only by the broken row.**
  Re-checked 2026-09-27 21:26 UTC+8: `GET /theorems/d5c69ba9-5a40-495b-a728-e7d11107a438`
  and every sub-endpoint (`/graph`, `/decompositions`, `/submissions`, `/mentions`)
  still return 404 `Theorem not found`, while its parent `fce5d444` and the sibling
  `rosser_schoenfeld_product_bound_286_to_700` read fine. All three siblings of
  `d5c69ba9` in `fce5d444`'s two decompositions are **Proved**; `d5c69ba9` is the only
  open input, so the parent cannot move until that row resolves.
