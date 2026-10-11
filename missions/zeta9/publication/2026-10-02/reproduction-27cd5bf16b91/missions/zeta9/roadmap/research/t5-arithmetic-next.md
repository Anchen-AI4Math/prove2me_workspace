# T5 的端点分母、整数间隔与第一输出高度

本文只证明适用于真实矩阵的算术恒等式和充分判据；没有证明五点第一输出目标 T5，也没有改变根定理状态。五点比值窗的存在与正性沿用 [五点比值窗](five-point-ratio-window.md) 的统一大偶数范围。下文的 `L_n,H_n` **不是** Taylor 窗端点；为避免同名，记五点端点为 `ℓ_n,h_n`，宽度 `w_n=h_n−ℓ_n>0`。

## 1. 端点既约分母与混合四阶子式内容

取 `q_n=d_n^9`、`A_n=q_nF_n∈Mat₅(Z)`，并令 `S` 选择输出的 `B,A₉` 两行。记

\[
C_n=S\operatorname{adj}(A_n),\qquad
t_{n,j}=k_{n,j}(k_{n,j}+n)\in\mathbb Z,
\qquad v(t)=(1,t,t^2,t^3,t^4)^{\mathsf T}.
\tag{1}
\]

令 `δ₄,n*` 为 [第七轮子式公式](../../round7/research/arithmetic.md) 的混合四阶子式 gcd，置 `\widetilde C_n=C_n/δ₄,n*`。因为 `C_n` 的十个条目，依符号正好是 `A_n` 中包含三列低 ζ 和另一列 `B` 或 `A₉` 的全部混合四阶子式，`\widetilde C_n` 是整数矩阵，且十个条目的 gcd 为 `1`。由 `E_n=S F_n^{-1}=q_nC_n/\det A_n`，每个五点比值都有**精确整数表达式**

\[
r_{n,j}
=\frac{\widetilde C_{n,A}v(t_{n,j})}
       {\widetilde C_{n,B}v(t_{n,j})},\qquad
Q_{n,j}=
\frac{|\widetilde C_{n,B}v(t_{n,j})|}
{\gcd\bigl(|\widetilde C_{n,B}v(t_{n,j})|,
            |\widetilde C_{n,A}v(t_{n,j})|\bigr)}.
\tag{2}
\]

这里 `Q_{n,j}>0` 是该有理数的既约分母；分母非零由五点窗证明中的 `Q_n^B(y_{n,j})>0` 保证。式 (2) 把端点分母问题精确归结为**求值后的**两行 gcd，而非系数整体 gcd。后者已由 `δ₄,n*` 消去，并不能控制前者：例如两条总体系数 gcd 为 `1` 的整数多项式 `1+t`、`1−t`，在奇整数 `t` 的两个取值均为偶数。特别地，不能把 `δ₄,n*` 直接当成式 (2) 的分母约分因子。

还有一个可选的结果式上界。令 `G_n(t)` 为 `\widetilde C_{n,B}v(t)` 与 `\widetilde C_{n,A}v(t)` 在 `Z[t]` 中的 primitive 多项式 gcd，写作 `G_nP_{B,n},G_nP_{A,n}`，其中 `P_{A,n},P_{B,n}∈Z[t]` 在 `Q[t]` 中互素。两者不可能都是常数，否则 `E_n` 的两行成比例。以整数 Sylvester 结果式 `\mathcal R_n=|\operatorname{Res}(P_{A,n},P_{B,n})|>0` 记，则整数 Bézout 恒等式给

\[
\gcd(|P_{A,n}(t)|,|P_{B,n}(t)|)\mid\mathcal R_n
\quad(t\in\mathbb Z),\qquad
\frac{|P_{B,n}(t_{n,j})|}{\mathcal R_n}\le Q_{n,j}\le |P_{B,n}(t_{n,j})|.
\tag{3}
\]

若两个商多项式有额外的整数内容，该内容留在 `P_{A,n},P_{B,n}` 内，式 (3) 仍成立。此处的结果式一般也随 `n` 增长；(3) 虽给逐参数上界，却不提供 T5 所需的**统一指数上界**。

## 2. 开窗内斜率的必要高度

写五点端点为既约分数 `ℓ_n=P_-/Q_-`、`h_n=P_+/Q_+`，`Q_±>0`。设整数输出 `z=(b,a)` 满足 `a≠0`，其斜率 `p=−b/a` 严格位于 `(ℓ_n,h_n)`。两个非零整数

\[
aP_-+bQ_-,\qquad aP_++bQ_+
\]

分别来自 `aQ_-(ℓ_n−p)` 和 `aQ_+(h_n−p)`。所以

\[
\boxed{\quad
|a|w_n>\max\{Q_-^{-1},Q_+^{-1}\}
=\frac1{\min(Q_-,Q_+)}.
\quad}\tag{4}
\]

不要求 `z` primitive；若 `z` primitive，`|a|` 恰为其斜率的既约分母。反过来，`|a|w_n\min(Q_-,Q_+)\le1` 是该整数输出避开开窗的充分条件；`a=0` 的输出本来就在 T5 的同号情形中。端点相等只给弱同号，不得用闭窗替代。

用 `U_B=(1,0)E_nW_n`、`U_A=(0,1)E_nW_n`、`\Xi_n=\|U_B\wedge U_A\|`，对任意 `z=(b,a)` 的 `v=zE_nW_n`，外积直接给

\[
|a|\Xi_n=\|v\wedge U_B\|
\le\|v\|\,\|U_B\|,
\qquad
|b|\Xi_n\le\|v\|\,\|U_A\|.
\tag{5}
\]

因此若 `z` 是加权第一输出，`\|v\|=\lambda_{1,n}`，则

\[
|a|\le\frac{\lambda_{1,n}\|U_B\|}{\Xi_n}
\le\sqrt{\frac2{\sqrt3}}\frac{\|U_B\|}{\sqrt{\Xi_n}}.
\tag{6}
\]

第二个不等式使用二维 Hermite 界。结合 (4)，得到一个**全大偶数、可逐项精确核对的充分判据**：只要某个 `n` 满足

\[
\frac{\lambda_{1,n}\|U_B\|}{\Xi_n}
\,w_n\min(Q_-,Q_+)\le1,
\tag{7}
\]

该 `n` 的每个第一输出都满足 T5 的五点弱同号条件。也可把 `\lambda_{1,n}` 由 (6) 的 Hermite 上界替代，得到仅用面积的更强充分条件。若 (7) 沿无穷多个合格偶数 `n` 成立，既有解析长度界与五点正求积即推出 `ζ(9)` 无理。现在没有 (7) 的无穷次证明；已证的 `w_n\le e^{-\kappa n}` (`\kappa<10.1109`) 与 (6) 不能单独控制 `\min(Q_-,Q_+)` 或 `\|U_B\|/\sqrt{\Xi_n}`。

式 (4) 同样说明端点分母为何可能抵消窗口宽度。若反设 `ζ(9)=c/d` 为既约有理数，则 [严格夹逼](five-point-ratio-window.md) 给 `ℓ_n<c/d<h_n`，所以每个合格 `n` 都必须满足

\[
\boxed{\quad d\,w_n\min(Q_-,Q_+)>1.\quad}\tag{8}
\]

这是对端点分母的严格**条件下界**，与 `w_n` 指数收缩相容。若能独立证明 (7)，式 (8) 和解析侧第一输出稳定为 `±(−c,d)` 才会形成矛盾；仅凭缩窗或子式内容不会形成矛盾。式 (8) 也可直接由两个有理数间隔推出，不预设端点与 `c/d` 相邻。

## 3. 冻结数据能核对什么

round7 冻结的 `n=12,24,48,96,192` 均**不在上述五点统一范围内**。已证鞍点上界 `x_*<1.003` 给

\[
k_{n,-2}
\le\left\lfloor nx_*+\tfrac12\right\rfloor
\le n+1\qquad(n\le192),
\]

而五点证明要求 `k_{n,-2}>n+1`，所以不能对这些样本计算并外推合格的 `ℓ_n,h_n,Q_±`。

仍可只读 [模数扫描](../../round7/verification/modulus-scan.json) 的加权 `n2r`、`full_N` 层：若 `H_n` 是归档 Gauss 幺模矩阵、`V_n` 是 Smith 右变换，则第一输出恰为 `(H_nV_n^{-1})_1`。整数计算得其两个坐标均 primitive，且 `|a|` 的十进制位数依次为 `26,52,106,211,421`。这些只是五个真实格的输出高度诊断，既不计算五点端点，也不给 (7) 的无穷估计。

剩余的具体算术问题是：对式 (2) 的取样值 gcd 或商多项式的结果式给足够强的统一控制，并与 (6) 的真实高度上界比较，使 (7) 无穷次成立；或者直接证明第一输出斜率无穷次不在开窗内。端点分母的大下界 (3)、(8) 本身朝相反方向，不能代替所需上界。
