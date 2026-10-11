# 增长维数的 rank-one 平方极点路线：指数误差与整数化门槛

2026-10-02。前轮的聚簇定理要求固定维数，本稿改变这一条件。
取 h→∞、m=2h+3 个相邻整数平方极点，所得正矩行列式始终是一次式。
这里证明真实误差的指数夹逼；所需 primitive 分母上界尚未证明。
不宣称 ζ(9) 无理，也不以有限分母数据代替渐近论证。

## 1. 纯一次式与单项式正交范数

令 M=M_h≥0 为整数，a_j=M+j，1≤j≤2h+3，
D_h(t)=∏_j(t+a_j²)，并取

\[
G_h(X)_{ij}=\mu_{9,X}(t^{i+j}/D_h(t)),\qquad 0\le i,j<h.
\]

μ 与正密度 w₉ 来自已审阅的
[正矩泛函](positive-hankel-zeta9-2026-09-29.md)。
Lagrange 恒等式给 [X]G 的前 2h−2 条矩为零、最后一条为 1，
因此 B=e_{h−1}e_{h−1}ᵀ。
写 G=A+XB，令 C 为前 h−1 阶主块、v 为末列前 h−1 个坐标。
C 是严格正的有理矩阵，且

\[
q_h=-A_{h-1,h-1}+v^TC^{-1}v\in\mathbb Q,
\qquad \det G_h(X)=\det C\,(X-q_h).
\]

h=1 时空块行列式为 1、二次项为零。对全部 h,M，

\[
\epsilon_h:=\zeta(9)-q_h
=\min_{p\text{ 首一},\,\deg p=h-1}
\int_0^\infty \frac{p(y^2)^2w_9(y)}{D_h(y^2)}\,dy>0. \tag{1}
\]

这是 monic Gram Schur complement，不需要无理性假设。
若 q_h=U_h/T_h 为既约分数、T_h>0，则整个行列式的最小正有理标量
primitive 多项式恰为 T_hX−U_h。块行列式 det C 的公共因子已完全约去，
不能把未经约分的清分母成本当作 T_h。

## 2. 一族明确的指数常数

假设 M_h/h→c，0≤c<∞。定义

\[
I_c(t)=\int_c^{c+2}\log(t^2+x^2)\,dx,
\qquad F_c(t)=4\log t-I_c(t)-2\pi t,
\qquad f_c=\max_{t>0}F_c(t).
\]

积分可由原函数 x log(t²+x²)−2x+2t arctan(x/t) 明确计算。
F_c 在两端都趋于 −∞，且

\[
F_c'(t)=\frac2t\int_c^{c+2}\frac{x^2}{t^2+x^2}\,dx-2\pi
\]

严格递减，故最大点唯一。也可逐项微分得 F_c''<0。
由于 I_c≥I₀，f_c≤f₀<0。
c=0 的最大点满足 4/t−2 arctan(2/t)−2π=0。
伴随脚本以 Arb 和有理二分区间认证这些常数，数值只是证明的可读展示。

**指数夹逼定理。** 对每条 M_h/h→c 的序列，

\[
\boxed{f_c-\log16\le\liminf_{h\to\infty}\frac{\log\epsilon_h}{h}
\le\limsup_{h\to\infty}\frac{\log\epsilon_h}{h}\le f_c<0.} \tag{2}
\]

这是误差区间，尚未证明 ε 的精确指数。宽度 log16 来自下面的 monic Legendre
下界，不能把 f_c 当作实际最优正交范数的精确率。

## 3. 上界：单项式试探与右端 Riemann 和

记 c_h=M_h/h。由正密度的定义及 ℓ⁸≤8! binom(ℓ+7,8)，

\[
w_9(y)\le\frac1\pi(1+2\pi y)^9e^{-2\pi y}
\le C(1+y^9)e^{-2\pi y}. \tag{3}
\]

第一式还使用 1−e^(−z)≥z/(1+z)。取 p(t)=t^(h−1)，令 y=ht。
尺度 h 的幂在 y^(4h−4)、dy、w 的 y⁹项与 2h+3 个极点因子间抵消。
对递增函数 x↦log(t²+x²)，

\[
\prod_{j=1}^{2h+3}(t^2+(c_h+j/h)^2)
\ge e^{hI_{c_h}(t)}(t^2+4)^3.
\]

因此对 h≥2，

\[
\epsilon_h\le C\int_0^\infty
\frac{h^{-9}t^{-4}+t^5}{(t^2+4)^3}e^{hF_{c_h}(t)}\,dt
\le C' e^{(h-2)f_{c_h}}. \tag{4}
\]

末式抽出 h−2 次最大值，剩下 e^(2F_c_h)≤e^(2F₀)；该积分在零处与无穷处
都有限，常数与 bounded c_h 无关。F_c_h 在紧区间一致收敛，且 F_c_h≤F₀
保证最大点不逃向两端，所以 f_c_h→f_c。得到 (2) 的上界。

## 4. 下界：尺度 h 区间上的首一 Legendre 范数

固定 0<α<β，限制积分到 y∈[αh,βh]。取密度的 ℓ=1 正项，
令 x=y²/h²，p(h²x)=h^(2h−2)r(x)，r 首一次数 h−1。
使用 D_h(y²)≤D_h(β²h²)，得到完全有限的下界

\[
\epsilon_h\ge
\frac{2(2\pi)^8}{8!}\frac{\alpha^9}{2\beta}
\frac{h^{4h+6}e^{-2\pi\beta h}}{D_h(\beta^2h^2)}
\frac{(\beta^2-\alpha^2)^{2h-1}}
{(2h-1)\binom{2h-2}{h-1}^2}. \tag{5}
\]

最后一项是区间 [α²,β²] 上首一 Legendre 多项式的精确平方范数。
它是对任意首一 r 的下界，不是假定真实最优多项式等于 Legendre。

右端 Riemann 和误差有界：对 β>0、bounded c_h，

\[
\log\bigl[D_h(\beta^2h^2)/h^{4h+6}\bigr]
=hI_{c_h}(\beta)+O_{\beta,c}(1).
\]

并且 binom(2n,n)≤4ⁿ。因此

\[
\liminf\log\epsilon_h/h
\ge2\log((\beta^2-\alpha^2)/4)-I_c(\beta)-2\pi\beta.
\]

先取 h→∞、再让 α↓0，最后选 β 为 F_c 的唯一最大点，得 f_c−log16。
这里 α 的 prefactor 虽趋零，但每个固定 α 的对数除以 h 都趋零，量词顺序合法。

## 5. 真正的整数化门槛

正一次式 T_hζ(9)−U_h=T_hε_h 已全参数非零。
(2) 给出两个可操作而不循环的算术条件：

- 若 limsup log T_h/h < −f_c，则该 primitive 形式趋零，足以推出 ζ(9) 无理。
- 若 liminf log T_h/h > log16−f_c，则该族的 primitive 值趋于无穷。

等号或中间区间没有由本稿决定。尤其真实误差指数缩小不等于整数形式缩小。
T_h 的所需无穷上界尚未取得，有限巨大分母也不证明所有未来参数失败。

本路线与原最短格方向 J 不同，非零性由正 Gram 解决；它仍必须跨过自己的
primitive 分母门槛。维数增长使前轮固定复杂度排除定理不能直接套用。

### 5.1 新分母的全部大素数也由矩形子式控制

此处 m=2h+3、所有分子 t^k 的次数小于 m，没有 Bernoulli 商。
完整矩阵 A 的分母只来自 H_a、8、2a 和 ∏(a_j²−a_i²)，所以素因子均≤2b，
其中 b=M+2h+3。取矩形矩阵 K=[vᵀ;C]，令

\[
F_h=(\operatorname{num}\det C)^{(>2b)},\qquad
J_h=\left(\gcd_I|\operatorname{num}\det K_I|\right)^{(>2b)}.
\]

numerator 均约分后取；h=1 的空子式约定为 1。
由于 q_h=−A_last+vᵀC⁻¹v，A_last 在 p>2b 上为整，
[已证明的 Jacobi 约分定理](mellin-unshifted-frontier-2026-10-01.md#4-a-square-bound-on-all-possible-cancellation)
在此逐字适用，不需要 K 是 powered Hilbert 矩阵：

\[
\boxed{F_h\mid T_h^{(>2b)}J_h^2,\qquad
T_h^{(>2b)}\mid F_h,\qquad T_h\ge F_h/J_h^2.} \tag{6}
\]

因此若 J_h=1，所有新大素数分子都恰好进入 primitive 分母。
比如证明 liminf log(F_h/J_h²)/h>log16−f_c 就能排除该参数族。
目前有限脚本精确计算全部 maximal-minor gcd，不假设所有未来 J_h=1。
这是把新的增长维数路线的算术问题规约到明确整数；F_h 的渐近增长仍未证明。

## 6. 精确验证

[verify_growing_rank_one_route.py](../scripts/verify_growing_rank_one_route.py)
直接计算完整残数矩阵，核验 B 的唯一末项、Schur complement、三个以上 determinant
值、primitive 全系数及正 Arb error，并逐例核对有限下界 (5) 和简单上界
ε_h≤μ₉(t^(2h−2))/∏a_j²。
它还核对全部大素数 numerator / maximal-minor gcd 的整除关系 (6)。
常数二分采用导数两端认证符号及严格凹性，不以浮点迭代作为根证书。
有限证书与 written asymptotic theorem 分开，未运行 Lean 或外部提交。

本轮共核验 39 个参数：h=1,...,12 各取 M=0,h,2h，另取 (h,M)=(16,0),(24,0),(32,0)。
全部 primitive 值严格为正，均未小于 1。38 例的 J_h=1；唯一例外 (h,M)=(10,10)
有 J_h=24077，说明直接把 maximal-minor gcd 恒等于 1 当作定理并不成立。
最大已算样本 (32,0) 的 log ε_h/h 约为 −7.2455843021，log T_h/h 约为
304.7323748964；这是该有限样本的巨大整数化成本，不是全参数增长证明。

| c | f_c | 足够成功的 log T_h/h 上界 | 足够失败的下界 |
|---:|---:|---:|---:|
| 0 | −6.1071275076 | <6.1071275076 | >8.8797162298 |
| 1 | −8.6229608848 | <8.6229608848 | >11.3955496070 |
| 2 | −10.2182841308 | <10.2182841308 | >12.9908728530 |

表中的成功、失败条件分别指 limsup 与 liminf，严格界是 (2) 和 §5 的定理；
小数来自 [summary.json](../verification/growing-rank-one-route-2026-10-02/summary.json)
的 Arb 包含区间。指数夹逼、真实 T_h 与 fresh-minor gcd 的全部精确数据见
[certificate.json](../verification/growing-rank-one-route-2026-10-02/certificate.json)。
