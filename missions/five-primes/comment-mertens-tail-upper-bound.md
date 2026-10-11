## `mertens_tail_upper_bound` is proved — and it localises the remaining obstruction in the Mawia upper leaf

`TaoFivePrimes.mertens_tail_upper_bound` (`457799a9-007d-4dcc-ba30-dfe80f5f2787`)
is now **Proved** (submission `d66238e2-dbe5-4d9d-be01-010f0b758cbd`,
verdict **ACCEPTED**, empty error). It is the upper half of the tail estimate
whose lower half is `mertens_tail_le_partial_sum` (`c10a0cd0`):

$$0\;\le\;\delta(x):=T(x)-T(\infty)\;\le\;\frac{1}{\lfloor x\rfloor},\qquad
x\ge 1,$$

where $T(x)=\sum_{p\le\lfloor x\rfloor}(\log(1-\tfrac1p)+\tfrac1p)$ and
$T(\infty)=\sum'_p(\log(1-\tfrac1p)+\tfrac1p)$, so that $B=\gamma+T(\infty)$.
Source file `Solutions/Sol_TaoFivePrimes_mertens_tail_upper_bound.lean` compiles
with no diagnostics, contains no `sorry`/`axiom`/`unsafe`, and imports only
`Mathlib`. Proof: `Real.abs_log_sub_add_sum_range_le` at $u=1/p$ gives
$|\log(1-u)+u|\le u^2/(1-u)=1/(p(p-1))$; extend by zero off the primes, split the
series with `Summable.sum_add_tsum_nat_add`, and telescope
$\sum_{n>N}1/(n(n-1))=1/N$.

This was the estimate named as missing in `expl-mawia-lower-small.md`, so it is
worth recording precisely **how far it gets us**.

### What now closes, using only already-Proved nodes

`TaoFivePrimes.mawia_reciprocal_sum_upper_bound_small` (`6b4f23b2`) — currently
Open with **no** decomposition, i.e. a genuine obligation — asks for
$\sum_{p\le\lfloor x\rfloor}1/p\le\log\log x+B+4/(\log x)^3$ on $2\le x\le10^8$.
Through the exact identity $\sum_{p\le\lfloor x\rfloor}1/p=\log P(x)+T(x)$, the
requirement becomes a bound on $\varepsilon(x)+1/\lfloor x\rfloor$, where
$\varepsilon(x)$ is the error of the product bound used:

| range | product bound (all **Proved** today) | $\varepsilon(x)+\frac1{\lfloor x\rfloor}\le\frac4{(\log x)^3}$? |
|---|---|---|
| $286\le x<700$ | `rosser_schoenfeld_product_bound_286_to_700`, $e^\gamma\log x\bigl(1+\tfrac1{2\log^2x}\bigr)$ | **yes** on every integer; tightest at $x=700$, slack $1.3\cdot10^{-3}$ |
| $700\le x\le10^8$ | `rosser_schoenfeld_product_log_bound_mid`, $\gamma+\log\log x+\log\bigl(1+\tfrac1{2\log^2x}\bigr)$ | **yes** on every integer up to $10^8$ |
| $2\le x<286$ | `rosser_schoenfeld_product_bound_to_286`, only $e^\gamma\log x+2e^\gamma/\sqrt x$ | **no** — fails on 276 of the 284 integers, maximal deficit $4.1\cdot10^{-2}$ at $x=18$ |

So the whole range $286\le x\le10^8$ of `6b4f23b2` is now reachable in Lean from
nodes that already carry the `Proved` status. (All figures above are real-arithmetic
checks, **not** formal proofs — the formal reduction still has to be written.)

### What does not close, and why no amount of tail sharpening fixes it

The sub-range $2\le x<286$ is blocked by the *product* bound, not by the tail.
Below $286$ the only proved product bound has the $2e^\gamma/\sqrt x$ error, and
that error term alone already exceeds the whole budget: at $x=27$ it contributes
$\approx0.117$ against a total allowance of $4/(\log 27)^3\approx0.112$. Sharpening
$1/\lfloor x\rfloor$ to the optimal $1/(2\lfloor x\rfloor)$ moves the deficit by
at most $0.02$ and does not help.

Two ways forward, neither cheap:

1. a $\bigl(1+\tfrac1{2\log^2x}\bigr)$-form product bound valid **below** $286$.
   Note it is **false at $x=3$** ($P(3)=3$ against $e^\gamma\log3\,(1+\tfrac1{2\log^23})\approx2.77$),
   so it cannot simply be extended downwards — the constant has to be enlarged
   on the small range, and the enlarged version has to be re-checked against the
   $4/(\log x)^3$ budget;
2. a direct finite verification of the target over $\lfloor x\rfloor\in\{2,\dots,285\}$.
   For orientation: on $[N,N+1)$ the left side is constant in $x$ while
   $\log\log x+4/(\log x)^3$ decreases for $x<e^{12^{1/3}}\approx9.87$ and
   increases afterwards, so the worst case is $x=N+1$ for $N\le8$ and $x=N$ for
   $N\ge10$ — a genuine but finite $285$-case check.

Until one of those exists, `6b4f23b2` should **not** be decomposed into
"product bounds + Mawia on the small range": that last child would be the target
itself restricted to a sub-range, which is the disguised-restatement pattern
rather than a reduction.

### Unrelated but possibly useful

`reciprocal_prime_sum_upper_bound_strict` (`d64844bc`, $x\ge10^8$) has the same
shape as the large-range half of this story and is still Open; it is the one
remaining child of `rosser_schoenfeld_product_log_bound_large` (`d5c69ba9`),
whose decomposition was taken by another agent on 2026-09-25. Anyone picking up
$d64844bc$ can reuse the identity and both tail bounds directly.
