# Mellin 正矩连续指数族：精确误差夹逼与分母判据

2026-09-30。沿用 [正 Mellin Gram 构造](alternative-route-2026-09-29.md)。
本文给出全参数的实误差夹逼，不依赖 ζ(9) 是否无理。这里没有证明
primitive 分母的所需增长界，因此不宣称无理性。

## 1. 对象和一个更好的权比较

令 `E={M,M+1,...,M+D}`，M,D 为非负整数，并设

\[
w(x)=\frac{(-\log x)^8}{8!(1-x)},\qquad
\epsilon_{M,D}=\zeta(9)-q_{M,D}
=\min_{p\in x^M\mathbb R[x]_{\le D},\ p(1)=1}
  \int_0^1p(x)^2w(x)\,dx.
\]

已有 Schur 补证明 `q_(M,D)∈Q`，其最简表示记为 Q/P，P>0。
原始 Gram 行列式的 primitive 整数化恰为 `PX−Q`。

对 0<x<1，有

\[
1-x\le-\log x\le\frac{1-x}{\sqrt{x}}.
\]

第一个不等式来自 `log x≤x−1`。第二个令 x=e^(−2t)，化为 t≤sinh t，
由 sinh(0)=0、cosh(t)≥1 得到。因此有逐点夹逼

\[
\frac{(1-x)^7}{8!}\le w(x)\le
\frac{x^{-4}(1-x)^7}{8!}.                       \tag{1}
\]

上界在 x=0 发散不影响下面的论证：选取的试探多项式至少含 x²，
其平方恰好消去 x^(−4)。所有使用的积分都收敛。

## 2. 带左端权重的 Jacobi 端点核

对整数 b≥0，在次数≤D且 r(1)=1 的多项式中，有

\[
\min_r\int_0^1r(x)^2x^b(1-x)^7dx=\frac1{K_{D,b}},
\quad K_{D,b}=8\binom{D+8}{8}\binom{D+b+8}{8}.    \tag{2}
\]

这是一个有限维精确恒等式。可由 Rodrigues 多项式

\[
J_{k,b}(x)=\frac{(-1)^k}{k!x^b(1-x)^7}
 \frac{d^k}{dx^k}\bigl[x^{k+b}(1-x)^{k+7}\bigr]
\]

直接证明：k 次分部积分给正交性，端点值为 `binom(k+7,7)`，
平方范数为

\[
\frac{(k+7)!(k+b)!}{(2k+b+8)k!(k+b+7)!}.
\]

在该正交基中对 r(1) 作 Cauchy–Schwarz，所得核值为

\[
\sum_{k=0}^D\frac{(2k+b+8)(k+7)!(k+b+7)!}
 {(7!)^2 k!(k+b)!}=K_{D,b}.
\]

闭式用相邻 D 的差及 D=0 核对；归一化核多项式取得等号。
这里未将有限阶 Rodrigues 计算当作全参数证明。

## 3. 精确夹逼

写 `p=x^M r`，由 (1) 左侧及 (2)，总有

\[
\epsilon_{M,D}\ge\frac1{8!K_{D,2M}}.              \tag{3}
\]

若 M≥2，则 (1) 右侧与 `b=2M−4` 的最优核试探多项式给

\[
\frac1{8!K_{D,2M}}\le\epsilon_{M,D}
\le\frac1{8!K_{D,2M-4}}.                         \tag{4}
\]

M=0 或 1 时，令 r₀=max(0,2−M)。只要 D≥r₀，选取
`p=x^(M+r₀)` 乘次数 D−r₀ 的核多项式，得到统一上界

\[
\epsilon_{M,D}\le
\frac1{8!K_{D-r_0,\,2(M+r_0)-4}}.               \tag{5}
\]

特别地，对未平移的连续族 D≥2，有

\[
\boxed{\frac1{8!K_{D,0}}\le\epsilon_{0,D}
\le\frac1{8!K_{D-2,0}}.}                        \tag{6}
\]

两个边界只差两个多项式次数，不涉及难以计算的实际最优多项式。

## 4. 严格渐近与整数化后的等价条件

由闭式

\[
\frac1{8!K_{D,b}}
=\frac{5040}{\prod_{j=1}^8(D+j)\prod_{j=1}^8(D+b+j)}
\]

立即得到

\[
\boxed{\epsilon_{0,D}\sim 5040D^{-16}.}          \tag{7}
\]

更一般地，D→∞ 时对任意可随 D 变化的整数 M≥0，有一致估计

\[
\epsilon_{M,D}
=\frac{5040}{D^8(D+2M)^8}\bigl(1+O(D^{-1})\bigr). \tag{8}
\]

一致性可直接逐因子核对：M≥2 时 (4) 的两端比值是八个
`(D+2M+j)/(D+2M−4+j)` 的乘积，均为 `1+O(1/D)`；
M=0,1 由 (5) 分别处理。同样，闭式里的每个加法常数只引入
`1+O(1/D)` 的相对误差，常数可选为与 M 无关。

因此，这一连续区间指数族的 primitive 整数形式满足

\[
P_{M,D}\zeta(9)-Q_{M,D}\to0
\quad\Longleftrightarrow\quad
\frac{P_{M,D}}{D^8(D+2M)^8}\to0,\qquad D\to\infty. \tag{9}
\]

两侧都是对**同一个序列**的结论。固定或线性平移时，右侧就是
`P=o(D^16)`。若有人能证明满足它的一条无限族，则正整数反证能证明
ζ(9) 无理；本稿没有证明这样的分母界。已有有限分母非常大，不能据此
断言所有更大 D 都大。

## 5. 有理基变换不改变 primitive 一次式

对固定函数子空间，用任意可逆有理矩阵 T 换基会把 Gram 矩阵变为
`TGTᵀ`，其行列式乘以正有理数 `(det T)²`。清全部系数分母并除全部
gcd 后，primitive 一次式仍是同一个 `PX−Q`。

这意味着仅换到正交、多项式差分或经分母清除的基，不能改善已使用的
最小标量整数化。它可以简化计算、帮助证明 divisibility，却不能改变
最终 primitive 数值。要改变数值，必须改变子空间、权重或所取的构造。

## 6. 验证边界

伴随脚本独立计算有理 Schur 补，检查有限个 Jacobi 范数、核恒等式及
实球误差夹逼。上述全参数和一致渐近结论的依据是 §§1–4 的书面证明，
不是有限采样。本轮未进行 Lean 形式化。

[verify_mellin_sharp_error.py](../scripts/verify_mellin_sharp_error.py) 已通过
42 个精确 Jacobi 核检查及 42 个有理近似的实球夹逼，证书见
[certificate.json](../verification/mellin-sharp-error-2026-09-30/certificate.json)。
独立审阅者完成 §§1–4 的全参数数学核查并重跑脚本通过，见
[审阅记录](structure-review-2026-09-30.md)。
