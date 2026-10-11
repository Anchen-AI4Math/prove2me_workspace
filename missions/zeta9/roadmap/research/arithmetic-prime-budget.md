# `N_n/g_n` 的逐素数误差预算

2026-09-29 更新：[VC 闭合证明](../../research/vc-closure-2026-09-29.md)现已证明
下文预算条件，进而完成 VA 与 V 的书面证明。下文开放状态保留为原稿历史；
新结果尚未 Lean 形式化，独立形状条件和无理性仍开放。

这个引理把开放的纯算术节点 `VA` 化为两个明确的素数估值余量。预算条件尚未证明；五个有限分解仅用于诊断。

对素数 `p≤n` 令 `a_p=⌊log_p n⌋=v_p(d_n)`，定义

\[
\mathcal E_n=\sum_{p\le n}\bigl(v_p(N_n)-11a_p\bigr)_+\log p,
\qquad
\mathcal H_n=\sum_{p>n}v_p(N_n)\log p. \tag{1}
\]

两个和均有限：第七轮已证 `N_n` 的素数支持不超过 `7n/2`。`\mathcal E_n` 测量小素数的“超过 `d_n¹¹`”部分，`\mathcal H_n` 是 `d_n` 不含的大素数部分。对**每个**偶数 `n≥2` 有精确的上界

\[
\boxed{\quad
\log(N_n/g_n)\le9\log d_n+\mathcal E_n+\mathcal H_n.
\quad} \tag{2}
\]

证明：`g_n=gcd(N_n,d_n²)` 给出

\[
v_p(N_n/g_n)=\max\{0,v_p(N_n)-2a_p\}.
\]

若 `p≤n`，右边不超过 `9a_p+(v_p(N_n)-11a_p)_+`；若 `p>n`，`a_p=0`，右边就是 `v_p(N_n)`。逐素数乘以 `log p` 再相加，即得 (2)。没有使用有限样本或关于素数分布的假设。

素数定理给出 `log d_n/n→1`。结合[逆像面积率](inverse-area-rate.md)，下列单一预算条件足以完成 `VA`，从而完成 `V`：

\[
\boxed{\quad
\limsup_{\substack{n\to\infty\\2\mid n}}
\frac{\mathcal E_n+\mathcal H_n}{n}
<2\tau-\frac12\log(3\,711\,015\,000)-9
\approx1.11071437.
\quad} \tag{3}
\]

从 (2) 除以 `2n` 得 `limsup log(N_n/g_n)/(2n)≤[9+limsup(\mathcal E_n+\mathcal H_n)/n]/2`，(3) 正好给出 `VA` 的严格阈值。

## 行列式单独给出的旧大素数界

第七轮的 Smith 恒等式已给 `N_n|det(d_n⁹F_n)`。对偶数 `n≥8` 及 `p>n`，`p` 不整除 `d_n` 或 `7n`，且 `p²>7n/2`。因此已知行列式闭式逐素数给出

\[
v_p(N_n)\le v_p(\det F_n)
=\left\lfloor\frac{3n}{2p}\right\rfloor
+\left\lfloor\frac{7n}{2p}\right\rfloor.
\]

记 `θ(x)=Σ_{p≤x}log p`。将两个取整函数按层展开并对 `p>n` 求和，可严格得到

\[
\mathcal H_n\le
\theta(3n/2)+\theta(7n/2)+\theta(7n/4)
+\theta(7n/6)-4\theta(n). \tag{4}
\]

素数定理于是给出仅靠行列式的 `limsup 𝓗_n/n≤47/12≈3.91667`，显著弱于预算 (3)。[平移迹消去定理](prime-valuation-attack.md)现已证明更强的 `v_p(N_n)≤⌊3n/(2p)⌋`（偶 `n≥8, p>n`），所以 `limsup 𝓗_n/n≤1/2`。式 (4) 保留为比较：它说明只读行列式会遗漏子式 gcd 的关键消去。

冻结分解的有限诊断如下；`E/n`、`H/n` 均来自精确整数素因子，表中对数小数不充当证明。`finite-audit.json` 还逐项核对整除形式的 (2)。

| `n` | `𝓔_n/n` 约 | `𝓗_n/n` 约 | 和约 |
|---:|---:|---:|---:|
| 12 | 0.28343 | 0.44985 | 0.73328 |
| 24 | 0.07466 | 0.28339 | 0.35805 |
| 48 | 0.10265 | 0.42971 | 0.53236 |
| 96 | 0.11917 | 0.49469 | 0.61386 |
| 192 | 0.10581 | 0.51365 | 0.61946 |

当前严格障碍已缩至 `√(7n/2)<p≤n` 的超额估值。[小素数截断定理](prime-valuation-attack.md)证明更小素数的贡献为 `o(n)`，而 `p>n` 部分至多 `n/2+o(n)`；因此只要剩余中间素数的超额贡献率严格低于 `0.61071437`，就能完成 (3)。[合并极点分析](intermediate-prime-attack.md)将该区间的局部指数统一压至 `38`，但尚未把正规化迹矩的消去转移到原低 ζ 子式；五例的余量低于阈值也不推出渐近结论。
