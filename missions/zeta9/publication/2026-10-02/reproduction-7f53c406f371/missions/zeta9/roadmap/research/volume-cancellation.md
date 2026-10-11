# 算术体积基线中的 Smith 内容消去

这是对开放节点 `V` 的精确代数化简。它不提供渐近估计，也不证明 `V`。

## 定理

沿用所有偶数 `n≥2` 的原五维形式。令 `F_n` 为满秩形式矩阵，`S` 选择输出的 `B,A₉` 两坐标，`E_n=S F_n⁻¹`。令 `K_n` 为低 ζ 整核的饱和行基，`J_n=D_n K_n F_n Sᵀ` 为整值输出矩阵，Smith 因子为 `s₁,n|s₂,n`，`N_n=s₂,n/s₁,n`。以 `W_n=diag(1,n²,n⁴,n⁶,n⁸)` 定义 `E_n` 的加权面积

\[
\Xi_n=\sqrt{\det(E_nW_n^2E_n^{\mathsf T})}>0.
\]

则对任意正除数 `g|N_n`，

\[
\boxed{\quad
\frac{D_n}{s_{1,n}}\sqrt{\frac{\Delta_n}{g}}
=\sqrt{\frac{N_n}{g}\,\Xi_n},
\qquad
B_n=\frac{\log\Xi_n+\log(N_n/g_n)}{2n}.
\quad} \tag{1}
\]

这里 `Δ_n` 是 `K_n` 的加权面积。式 (1) 消去了 `D_n`、`s₁,n` 和核基的选择；唯一剩余算术因子是 `N_n/g_n`。

## 证明

第七轮的精确关系 `E_n=D_nJ_n⁻¹K_n` 给出 `K_n=D_n⁻¹J_nE_n`。二维面积在左乘 `2×2` 矩阵时按行列式绝对值缩放，故

\[
\Delta_n=\frac{|\det J_n|}{D_n^2}\Xi_n
=\frac{s_{1,n}^2N_n}{D_n^2}\Xi_n. \tag{2}
\]

代入 `B_n` 的定义，取正平方根和对数即得 (1)。所有步骤是精确等式，无渐近误差。

还可不构造 `E_n`，直接用 `F_n` 的低三列 `F_{n,\mathrm{low}}` 表示面积。Jacobi 互补子式公式把 `E_n` 的每个二阶子式变成对应低三列的互补三阶子式除以 `det F_n`；再用 Cauchy–Binet 得

\[
\boxed{\quad
\Xi_n^2=\frac{n^{40}}{(\det F_n)^2}
\det(F_{n,\mathrm{low}}^{\mathsf T}W_n^{-2}F_{n,\mathrm{low}}).
\quad} \tag{3}
\]

因此 `V` 等价于沿全部趋于无穷的偶数 `n` 证明

\[
\limsup\frac{\log\Xi_n+\log(N_n/g_n)}{n}<2\tau=21.128. \tag{4}
\]

对 `g_n=\gcd(N_n,d_n^2)`，逐素数恰有

\[
v_p(N_n/g_n)=\max\{0,\ v_p(N_n)-2\lfloor\log_p n\rfloor\}. \tag{5}
\]

所以算术工作集中在 `N_n` 超出 `d_n²` 的素数幂；(3) 把几何工作集中在一个固定 `3×3` Gram 行列式与已知 `det F_n`。

## 与子式 gcd 公式的交叉核对

令 `q_n=d_n⁹`、`A_n=q_nF_n`，低三列最高阶子式的 gcd 为 `δ₃,n`，混合四阶子式的 gcd 为 `δ₄,n*`。第七轮证明 `s₁(J_{q_n})=δ₄,n*/δ₃,n`。由于 `J_{q_n}=(q_n/D_n)J_n`，矩阵各项 gcd 随正有理标度同倍缩放，故

\[
\boxed{\frac{D_n}{s_{1,n}}=\frac{q_n\delta_{3,n}}{\delta_{4,n}^*}.} \tag{6}
\]

把 (6)、`N_n=|det A_n|δ₃,n/(δ₄,n*)²` 和[加权核面积恒等式](weighted-kernel-area.md)代入 `B_n`，可再得到

\[
nB_n=\log q_n+10\log n-\tfrac12\log|\det A_n|
+\tfrac12\log(N_n/g_n)
+\tfrac14\log\det(L_n^{\mathsf T}W_n^{-2}L_n). \tag{7}
\]

用 `A_n=q_nF_n`、`L_n=q_nF_{n,low}` 消去全部显式 `q_n`，(7) 正是 (1)、(3)。这也表明选择更大的共同分母不会改变 `B_n`。

五个冻结样本 `n=12,24,48,96,192` 已在[有限核验](../verification/finite-audit.json)中按整数核对 (6) 和 (2)，并以 Arb 区间重算 (1) 的两项。六位小数仅供定位量级：

| `n` | `log(N_n/g_n)/(2n)` | `log Ξ_n/(2n)` | 和 `B_n` |
|---:|---:|---:|---:|
| 12 | 4.003031 | 6.482220 | 10.485252 |
| 24 | 4.277356 | 6.141099 | 10.418454 |
| 48 | 4.554898 | 5.897351 | 10.452249 |
| 96 | 4.402716 | 5.739130 | 10.141846 |
| 192 | 4.627112 | 5.641908 | 10.269020 |

这些有限值不推出 (4)。下一步需要分别证明 `Ξ_n` 的统一指数上界和 (5) 中超额素数幂的统一上界，并核对两者之和是否严格低于 `21.128`；单独估计任一项不足以关闭 `V`。
