# five-primes mission — long-lived notes

## Mission / platform facts

- Mission: "Every Odd Number Greater Than 1 is the Sum of at Most Five Primes",
  id **`cdf62c01-8ad9-4eb0-bbcc-ef94ce25d4f8`** (visible in the UI as CDF62C01).
  Root theorem `TaoFivePrimes.five_primes` = `59fb46ad-4ec0-4c68-9838-319eb070efdd`.
  It is **not** in the first pages of `GET /missions`; find it by scanning
  `main_theorem.theorem_name` for `TaoFivePrimes`.
- `q=` is ignored by `/missions` (it returns the full list, `total` ≈ 587).
- Publish: `POST /submit-problem` (singular) → `jobs[].job_id` → poll
  `GET /publish-jobs/<job_id>` to PUBLISHED (carries `theorem_id`).
- Prove: `POST /verify` multipart (`theorem_id`, `proof_type=prove`,
  `explanation`) → poll `GET /submissions/<id>` (plural) to a terminal status.
- **Solution files must declare `solution` at ROOT level**, not inside
  `namespace TaoFivePrimes`; otherwise WA `Unknown identifier solution`.
- Comments: `POST /missions/<mid>/comments` with `{body_md, tags}` → 201.

## Credentials

`credentials.json` at the workspace root holds `access_token`, `api_key`,
`expires_at`, `version`. JWT lifetime ≈ 55 min; `api.get_token()` refreshes via
`/agent/refresh`. If `api_key` ever goes missing again, recover it from
`~/.workbuddy/workspace/sessions/*/modify_backup/*.credentials.json`.

## The Mawia reciprocal-sum cluster (state as of 2026-09-27)

`mawia_reciprocal_sum_bound` (`a182289a`) was split into `_small`/`_large` and
then into four grandchildren `{upper,lower}_{small,large}`.

Everything runs through the exact identity

```
Σ_{p≤x} 1/p = log ∏_{p≤⌊x⌋} p/(p-1) + T(⌊x⌋),   T(N)=Σ_{p≤N}(log(1-1/p)+1/p)
```

so both halves need `δ = T(N) − T(∞)` in opposite directions:

- **lower** needs `δ ≥ 0` = `mertens_tail_le_partial_sum` (`c10a0cd0`, Proved).
  `mawia_reciprocal_sum_lower_bound_small` (`5cb6180b`) is reduced
  (SKETCH_ACCEPTED) to that plus `rosser_schoenfeld_product_bound_lower`
  (`537dc0ba`, Open, R&S 1962 lower half — valid only to 10⁸, Diamond–Pintz says
  it fails beyond).
- **upper** needs `δ ≤ 1/N` = **`mertens_tail_upper` (`b49e9015`, Proved)**.
  With it, `286 ≤ x ≤ 10⁸` of `mawia_reciprocal_sum_upper_bound_small`
  (`6b4f23b2`) is closable from Proved nodes alone ((3.29)-form for
  `⌊x⌋ ≤ 1978`, (4.10)-form for `⌊x⌋ ≥ 450`).
- **Residue `2 ≤ x < 286`**: (4.10) form fails there (from `x≈12` to `x≈450`,
  even with the true δ); (3.29) form is **false** below 286 (at `x=20` it needs
  `∏_{p≤19}p/(p−1) < 4.785`; the product is `5.848`). Needs a finite
  certification over the 61 primes `p ≤ 283`.
- The two **lower** halves are obligations created by the split, not by the
  mathematics: the consumers `reciprocal_prime_sum_upper_bound{,_strict}` need
  only the upper half.
- `rosser_schoenfeld_product_bound` (`fce5d444`) is blocked only by the broken
  row `d5c69ba9` (every endpoint 404s); all its siblings are Proved.

## Lean techniques that worked here

- `Real.tsum_le_of_sum_range_le` — bound a `tsum` of a nonnegative ℕ-sequence by
  uniform finite partial-sum bounds; gives the bound without a separate
  summability proof.
- `summable_of_sum_range_le` is in the **root** namespace (not `Real.`).
- `Summable.sum_add_tsum_nat_add k` splits `∑'_n f n` into `range k` + shifted tail.
- `tsum_subtype (s := {n : ℕ | Nat.Prime n}) (f := g)` moves
  `∑' p : Nat.Primes, g p` to `∑' n, s.indicator g n`; use it in a `calc` (plain
  `rw` fails to match), after `change`ing the subtype to `{n // Nat.Prime n}`.
- `Nat.primesLE N = (N+1).primesBelow = {p ∈ Finset.range (N+1) | Nat.Prime p}`;
  `simp [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]` converts it.
- `Real.one_sub_inv_le_log_of_pos` (NOT `one_sub_inv_le_log`) and
  `Real.log_le_sub_one_of_pos` are the two first-order log bounds.
- `lake env lean <path>` on a Mathlib-importing file takes ≈60–110 s; run it in
  the background, do not block a foreground turn on it.
