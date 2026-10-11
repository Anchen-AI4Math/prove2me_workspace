# 素数预算的精确折扣项

2026-09-29 更新：[新证明](../../research/vc-closure-2026-09-29.md)已得到
`liminf U_n/n≥0.160566059492300...`，并关闭 VC、VD、VA 和 V 的书面证明。
以下未证状态保留为原稿历史，独立形状条件和无理性仍开放。

`VC` 是充分条件，但把每个 `p≤n` 的指数一律按 `9v_p(d_n)` 计费，会丢掉一个非负的精确折扣。本稿把这个折扣保留，以便在逐点估值上界失效后研究加权总和。这里只证明代数恒等式与充分归约；折扣的正渐近下界尚未证明。

沿用 `N_n`、`g_n=gcd(N_n,d_n²)` 及[素数预算](arithmetic-prime-budget.md)的记号。令 `a_p=v_p(d_n)=⌊log_p n⌋`、`v_p=v_p(N_n)`，定义

\[
\mathcal U_n=\sum_{p\le n}
 \min\bigl\{(11a_p-v_p)_+, 9a_p\bigr\}\log p\ge0.
\tag{1}
\]

## 精确恒等式

对每个偶数 `n≥2`，

\[
\boxed{\quad
\log(N_n/g_n)=9\log d_n+\mathcal E_n+\mathcal H_n-\mathcal U_n.
\quad}\tag{2}
\]

证明只需在每个 `p≤n` 检查

\[
(v_p-2a_p)_+
=9a_p+(v_p-11a_p)_+
 -\min\{(11a_p-v_p)_+,9a_p\}.\tag{3}
\]

若 `v_p≥11a_p`，两边都是 `v_p−2a_p`；若 `2a_p≤v_p<11a_p`，右边是 `9a_p−(11a_p−v_p)=v_p−2a_p`；若 `v_p<2a_p`，右边是 `9a_p−9a_p=0`。对 `p>n`，`d_n` 没有该素因子，恰由 `𝓗_n` 计入。逐素数求和即得 (2)。先前的预算不等式是舍去 `𝓤_n≥0` 的结果。

## 比 VC 更宽的充分目标

记 `\gamma=\tfrac14\log(3\,711\,015\,000)`，`\tau=10.564`，并设 `\mathcal E_n^{\rm mid}` 为 `√(7n/2)<p≤n` 的超额和。[小素数截断](prime-valuation-attack.md)给 `𝓔_n−𝓔_n^{mid}=o(n)`，[大素数界](prime-valuation-attack.md)给 `limsup 𝓗_n/n≤1/2`。由 (2)、`log d_n/n→1` 和[逆像面积率](inverse-area-rate.md)，如果

\[
\boxed{\quad
\limsup_{\substack{n\to\infty\\2\mid n}}
\frac{\mathcal E_n^{\rm mid}-\mathcal U_n}{n}
<2\tau-\tfrac12\log(3\,711\,015\,000)-9-\tfrac12
\approx0.61071437,
\quad}\tag{4}
\]

则 `VA` 与 `V` 都成立。严格裕量由 (4) 与现有谱上界共同提供。式 (4) 比 `VC` 弱，因为 `𝓤_n≥0`；即使一个局部素数有 `v_p(N_n)>12`，也不单独否定 (4)。**式 (4) 仍开放。** 任何有限 `𝓤_n` 的正值都不能给它渐近下界。

五个冻结分解的有限诊断如下。每个 `𝓤_n` 由 `round7/verification/modulus-scan.json` 中 `N_complete_small_prime_factorization` 和 `d_n` 的整数因子直接按 (1) 计算；精确核对用 (2)，小数只显示量级。

| `n` | `𝓤_n/n` 约 | `(𝓔_n+𝓗_n)/n` 约 |
|---:|---:|---:|
| 12 | 0.399649 | 0.733280 |
| 24 | 0.203765 | 0.358043 |
| 48 | 0.336216 | 0.532361 |
| 96 | 0.196291 | 0.613854 |
| 192 | 0.285860 | 0.619460 |

这说明粗预算在这些点确有可见松弛，但不预测 `liminf 𝓤_n/n`。下一步需要证明折扣的统一下界，或直接控制 (4) 的**带符号加权和**。两个已证的逐点估值反例见[局部 Smith 核验](vc-local-smith-next.md)。
