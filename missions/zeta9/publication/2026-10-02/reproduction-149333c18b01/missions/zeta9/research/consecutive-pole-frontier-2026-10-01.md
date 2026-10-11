# 固定 h、m 的相邻平方极点平移：显式次数与 primitive 精确增长率

2026-10-01。本稿封闭[固定维数前沿](pole-dimension-frontier-2026-10-01.md)中尚未统一处理的
`h<m` 相邻平移族，给出所有固定 h、m 的完整次数分类。结论是算术增长定理，
不是 ζ(9) 的无理性证明。所有常数与误差允许依赖固定 h、m；不对增长维数作结论。

## 1. 全分类

固定正整数 h、m，令 `M≥0` 为整数，

\[
A_M=\{M+1,\ldots,M+m\},\quad L=M+1,\quad b=M+m,\quad
D_M(t)=\prod_{i=1}^m(t+(M+i)^2).
\]

取分子 `S=1`，定义

\[
G_M(X)_{ij}=\mu_{9,X}\!\left(\frac{t^{i+j}}{D_M(t)}\right),
\quad0\le i,j<h,\qquad \Delta_M(X)=\det G_M(X),
\]

以及最小正有理标量 primitive 多项式 `P_M=c_MΔ_M∈Z[X]`。

**主定理。** 对每个 M，

\[
\boxed{\deg\Delta_M=\operatorname{rank}B_M
=r:=\max\{0,\min(m,h,2h+4-m)\}.}
\]

若 `r=0`，则 `P_M=1` 对每个 M 成立。若 `r≥1`，则

\[
\boxed{\lim_{M\to\infty}\frac{\log P_M(\zeta(9))}{M+m}=9r.}
\]

因此所有固定维数与固定极点数的相邻整体平移，要么已经把 ζ(9) 系数完全消去，
要么 primitive 正值以严格正指数增长；这里没有趋零家族。

| 固定参数范围 | r |
|:---|---:|
| `m≤h` | m |
| `h<m≤h+4` | h |
| `h+5≤m≤2h+3` | `2h+4−m` |
| `m≥2h+4` | 0 |

第三行在 h=1 时为空。`m=h+4` 是满秩边界，`m=h+5` 才开始降秩；
`m=2h+3` 仍有一次 ζ(9) 形式，`m=2h+4` 才成为常数。

## 2. B 矩阵的完全齐次式与 Schur 正性

写 `a_i=M+i`、`z_i=−a_i²`。多项式除法和残数给

\[
(B_M)_{ij}=\sum_{a\in A_M}\frac{a^8(-a^2)^{i+j}}{D'_M(-a^2)}
=\sum_{\nu=1}^m\frac{z_\nu^{i+j+4}}{D'_M(z_\nu)}.
\]

Lagrange 最高系数恒等式，或生成函数 `∏(1−z_νu)^(−1)`，给

\[
\boxed{(B_M)_{ij}=H_{i+j+5-m}(z_1,\ldots,z_m),}
\]

其中 H_n 为完全齐次多项式，`H_0=1`、`H_n=0` 对 `n<0`。所以 B 的每个元素
都是整系数 M 多项式；这个恒等式也适用于任意互异正整数极点。

若 `m≤h`，B 的 Vandermonde 分解有 m 个非零权重，列满秩；前 m 阶主子式
的行列式为 `(-1)^(m(m−1)/2)∏a_i⁸≠0`，故 rank=m。

若 `h<m≤h+4`，令 `x_i=a_i²>0`、`λ=h+4−m≥0`。抽取逐行逐列的符号并反转行，
Jacobi–Trudi 恒等式给

\[
\boxed{\det B_M=(-1)^{h(5-m)+h(h-1)/2}
s_{(\lambda^h)}(x_1,\ldots,x_m).}
\]

Schur 多项式是该形状半标准 Young 表的正单项式之和。这里有 h 行且 `m>h`，
把第 i 行全部填 i 即给出一个合法表；因此当 `λ>0` 时至少有一个严格正单项式。
`λ=0` 时 Schur 多项式为 1。故这个完整区间 B 满秩，r=h。
使用的是标准 Jacobi–Trudi / 表展开恒等式；有限验证还直接枚举相应表来核对符号。

若 `h+5≤m≤2h+3`，置

\[
q=m-h-4,\qquad r=h-q=2h+4-m.
\]

B 的前 q 行与列全部为零。在剩余 r 阶块中，前反对角的元素为零、反对角全为 1，
所以其行列式为 `(-1)^(r(r−1)/2)`。这证明 rank=r，并非只给秩上界。

若 `m≥2h+4`，最大的 `i+j+5−m` 也为负，故 B=0。

正 Gram 矩阵 `G_M(ζ9)>0` 同时保证 `deg detG=rankB`：令
`T=G_M(ζ9)^(-1/2) B G_M(ζ9)^(-1/2)`，这是实对称矩阵，其非零特征值个数
等于 rankB，而 `detG(X)=detG(ζ9)det(I+(X−ζ9)T)`。所以次数不会因符号抵消降低。

## 3. 一个共同调和数，外加只有多项式高度的有理尾项

对每个极点

\[
H_{a_i}^{(9)}=H_L^{(9)}+\sum_{j=2}^i(M+j)^{-9}.
\]

尾项最多 m−1 个。将完整泛函中的 Bernoulli 多项式商保留，得到精确 normal form

\[
\boxed{G_M(X)=R_M+(X-H_L^{(9)})B_M,\qquad
F_M(Y):=\det(R_M+YB_M),\quad
\Delta_M(X)=F_M(X-H_L^{(9)}).}
\]

R 的每个条目都是一个固定有理 M 函数，其分母只含固定的矩分母、极点差、
`1/(2a_i)` 及这 m−1 个尾项分母。这里不含长度约 M 的调和和。

给出具体的整数多项式清分母。取固定 `C_0≥1` 清所需的有限个 Bernoulli 矩分母，
令

\[
V_M=\prod_{i<j}(a_j^2-a_i^2),\qquad
T_M=8C_0\left(\prod_{i=1}^m a_i\right)V_M
\prod_{j=2}^m a_j^9>0,
\qquad N_M=T_M^h.
\]

每个 `D'_M(z_i)` 在符号差之外整除 V_M；整数首一 D 的多项式除法保留整系数。
因此 `T_M R_M` 与 `T_M B_M` 都是整系数 M 多项式矩阵。
于是

\[
\boxed{N_M F_M(Y)=\sum_{j=0}^r A_j(M)Y^j\in\mathbf Z[M,Y],
\qquad A_r(M)\ne0.}
\]

T 的 M 次数为 `m+binom(m,2)+9(m−1)`，所以
`logN_M=O(logb)`、`log|A_r(M)|=O(logb)`。最高系数非零由上一节的 rank / 正 Gram
结论保证，甚至对所有 `M≥0` 非零。

低秩情形还可以直接看到非零性：前 q 行列上的 R 块与真实 Gram 主块相同，
故严格正定；`[Y^r]F_M=det(R_00)det(B_active)≠0`。
这避免把一个可能为零的有理系数拿去清分母。

## 4. primitive 标量保留整个调和分母的 r 次幂

写 `H_L^(9)=U_L/D_L` 为既约分数。以下 D_L 是调和分母，不是极点多项式 D_M。
令 `c_M=n_M/d_M>0` 为既约正标量。
由于最高系数是 `A_r/N_M`，且 c 乘它为整数，

\[
d_M\mid A_r(M).
\]

另一方面，`N_M D_L^r Δ_M` 已是整系数多项式。因此最小正 scalar 满足
`c_M≤N_M D_L^r`。

对任意素数 `p|D_L`，若 `p∤N_M A_r(M)`，写 `e=v_p(D_L)>0`。
F 的全部系数为 p 整、最高系数为 p 单位，而 `v_p(H_L)=−e`。
原 Δ 的常数系数为 `F_M(−H_L)`，其最高次贡献估值为 `−re`，
其余贡献至少为 `−(r−1)e`，所以最低项唯一。
所有其他 Δ 系数的估值不小于 `−re`。primitive 正常化因而给出**精确**等式

\[
\boxed{v_p(c_M)=r\,v_p(D_L)\quad(p|D_L,\ p\nmid N_M A_r).}
\]

设 E_L 是 D_L 中由 `p|N_M A_r` 支撑的全部素数幂部分。
每个素数幂 `p^e|D_L` 满足 `e logp≤9logL`，因为
`D_L|lcm(1,...,L)^9`。而异常素数的个数不超过
`log|N_M A_r|/log2=O(logb)`，所以 `logE_L=O((logb)^2)`。
结合有理标量分母的控制，

\[
\frac{(D_L/E_L)^r}{|A_r|}\le c_M\le N_M D_L^r,
\qquad
\boxed{\log c_M=r\log D_L+O((\log b)^2).}
\]

这比只保留顶部半区素数更强，也没有默认 c 是整数。
作为独立较弱检查，顶部半区 `b/2<p≤L`、`p∤N_M A_r` 时有 `v_p(H_L)=−9`，
故 `v_p(c_M)=9r`，立即给下增长率至少 `9r/2`。

## 5. 调和分母率与真实 Gram 的渐近

对每个正整数 n，设 `H_n^(9)=U_n/D_n` 为既约分数。标准素数定理足以证明

\[
\boxed{\log D_n/n\longrightarrow9.}
\]

上界来自 `D_n|lcm(1,...,n)^9` 及 `ψ(n)=n+o(n)`。
下界不需要假设一般调和分子没有消去素数：固定 K，对
`n/(K+1)<p≤n` 有 `k=floor(n/p)≤K`，n 足够大时 `p²>n`。
拆出 p 的倍数得到
`H_n=p^(−9)H_k+一个p整数`。H₁,...,H_K 的分子只含有限个素因子；
当 n 足够大时，这些例外素数全部小于 `n/(K+1)`。故整个上述区间均有
`v_p(D_n)=9`，得到
`liminf logD_n/n≥9K/(K+1)`。令 K 趋于无穷即得下界 9。

另一方面，固定 h、m 时，对每个 y>0 有 `M^(2m)/D_M(y²)→1`，
而 `M^(2m)/D_M(y²)≤1` 对 `M≥1` 成立。各多项式矩有限，故控制收敛逐条给

\[
M^{2m}G_M(\zeta(9))\longrightarrow
H_h:=(\mu_9(t^{i+j}))_{0\le i,j<h}>0.
\]

行列式连续，得到精确实渐近

\[
\boxed{\Delta_M(\zeta(9))\sim M^{-2mh}\det H_h,\qquad \det H_h>0.}
\]

因此 `logΔ=−2mhlogM+O(1)`，不是指数小值。
再用 `L/b→1`、上一节 `logc=rlogD_L+O(log²b)`，证明主定理的精确增长率 `9r`。

当 r=0，Δ 为正有理常数，多项式只有一个系数；其 primitive 正常化恰为 1。
这也与零增长率相容，但不保留任何 ζ(9) 信息。

## 6. 固定正分子和固定偏移：次数最终稳定的推论

同一个证明允许固定互异整数偏移 `c_1<...<c_m`，取 `a_i=M+c_i>0`，
以及任意固定 `S∈Q[t]`，`S(t)>0` 对 `t>0`。此处不乱给一个与 S 无关的显式次数。

取共同调和点 `L=M+c_1`。各尾项长度最多 `c_m−c_1`，是固定常数。
所以 `G_M(X)=R_M+(X−H_L)B_M` 中 R、B 仍是固定有理 M 函数，
`F_M(Y)=det(R_M+YB_M)` 的全部系数都在 `Q(M)`。

若全部非恒定 Y 系数恒等于零，则 primitive 多项式恒为常数 1。
否则令 d 为最高的非零有理函数系数的次数。非零有理函数只有有限个零点，
因此除去有限个 M 后次数恰为 d≥1，最高系数可以按前文以多项式高度清分母。
固定 S 的平方极点约分也只发生在有限个 M 上，不影响渐近。

真实 Gram 的渐近改为
`Δ_M(ζ9)∼M^(−2mh)det(μ_9(S(t)t^(i+j)))`，其常数严格正。
正常化证明完全相同，故

\[
\boxed{\deg P_M=d\text{ 最终稳定},\qquad
\log P_M(\zeta(9))/(M+c_m)\longrightarrow9d.}
\]

这里 d=0 对应常数 1，d≥1 对应指数增长。`S=1` 的显式 rank 公式本身适用于
任意正整数极点，所以固定偏移时也可直接用第一节的 r。

改变一个固定正分子，确实可能恢复此前被消去的 ζ(9) 系数，例如 `h=1,m=6,S=t`
重新有一次式，或 `h=2,m=8,S=t` 重新有 rank=degree=1；但其固定整体平移仍受本推论
的正增长约束。增长维数、增长分子次数及其他几何仍需分别研究。

## 7. 验证范围

[verify_consecutive_pole_frontier.py](../scripts/verify_consecutive_pole_frontier.py)
使用完整单项式泛函的多项式商、全部残数和有理插值，独立核对 B 的完全齐次式、
Schur 表展开符号、low-rank 首零块与反对角、rank/degree、normal form、所有 primitive
系数、scalar 分母、全部 good 调和分母素数的精确估值及 scalar 上下界。

预先列定的范围覆盖 `h=1,...,5`、`m=1,...,2h+4` 的所有整数位置，
每种取 `M=0,7,31`；低秩端点另取 `M=127`。此外有固定正分子与非相邻固定偏移的
有界对照例。它特别包含 `m=h+4,h+5,2h+3,2h+4` 四个秩变化边界。

有限证书在 [certificate.json](../verification/consecutive-pole-frontier-2026-10-01/certificate.json)，
统计在 [summary.json](../verification/consecutive-pole-frontier-2026-10-01/summary.json)。
验证器由根代理完成并运行，共 **181 例**：167 个相邻参数、14 个固定分子或固定偏移
对照，含 20 个次数零例和 **464 个** whole-harmonic good-prime 精确赋值检查。
Schur 表展开采用独立的 horizontal-strip 分支递归，与完整残数矩阵的行列式核对。
有限实验检查实现，不能取代 Schur 正性、调和分母渐近或无穷参数量词的上述书面证明。
没有 Lean 构建或外部提交，ζ(9) 无理性仍未证明。
