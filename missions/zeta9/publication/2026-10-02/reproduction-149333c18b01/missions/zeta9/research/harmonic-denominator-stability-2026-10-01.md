# 高阶调和数的分母指数与有理扰动稳定性

2026-10-01。这是供右移 Mellin 指数族使用的通用算术引理。
它使用标准素数定理，不涉及 ζ(9) 是否有理，也不是 Lean 验证。
下述初等推导不作文献优先权声明。

## 1. 精确的有限素数块

对固定正整数 s，定义

\[
H_N^{(s)}=\sum_{j=1}^N j^{-s},\qquad
d_{s,N}=\operatorname{den}(H_N^{(s)}),
\]

其中 den 表示既约有理数的正分母，den(0)=1。设 p 为素数，
p>√N，k=⌊N/p⌋。将 p 的倍数与其余项分开，得到精确恒等式

\[
p^s H_N^{(s)}=H_k^{(s)}+p^s U_{N,p},\qquad
U_{N,p}=\sum_{1\le j\le N,\ p\nmid j}j^{-s}\in\mathbb Z_p. \tag{1}
\]

由于 k<p，H_k 也是 p 整的。若 p 不整除 H_k 的既约分子，则 (1) 给

\[
v_p(H_N^{(s)})=-s,\qquad v_p(d_{s,N})=s.                 \tag{2}
\]

这里只在分子为单位时断言恰为 s；不能不加条件地把所有大素数都算进
分母。例如 s=9、k=2 时 H₂=513/512，素数 19 整除分子。
该有限异常不影响下一节的固定截断论证。

## 2. 全序列分母指数

**定理 1。** 对每个固定正整数 s，

\[
\boxed{\lim_{N\to\infty}\frac{\log d_{s,N}}{N}=s.}       \tag{3}
\]

证明。令 ℓ_N=lcm(1,...,N)。逐项清分母得到 d_{s,N}|ℓ_N^s。
标准素数定理的 Chebyshev 形式为 θ(N)∼N、ψ(N)∼N，且 log ℓ_N=ψ(N)，
因此 limsup 不超过 s。这里的外部输入是已证明的素数定理；可参照
[AFP 的正式证明与源码](https://isa-afp.org/entries/Prime_Number_Theorem.html)。
本稿没有把该外部正式证明当成本项目的 Lean 构建。

下界固定任意 0<ε<1。若 εN<p≤N，则 k=⌊N/p⌋≤⌊1/ε⌋。
所有 H₁,...,H_{⌊1/ε⌋} 都是正的非零有理数，故它们的既约分子只涉及
有限个素因子。充分大的 N 满足 εN>√N，且 εN 大于所有这些有限异常素因子。
于是区间 (εN,N] 中每个素数都满足 (2)，从而

\[
\log d_{s,N}\ge s\sum_{\varepsilon N<p\le N}\log p
=s\bigl(\theta(N)-\theta(\varepsilon N)\bigr).
\]

素数定理给 liminf≥s(1−ε)。对每个固定 ε 完成 N→∞ 后再令 ε↓0，
下界提升到 s。此过程没有让截断阶数在素数论证中随 N 移动。证毕。

特别地，s=9、N=2M 时 log den(H_{2M})/M→18。
此结论不要求调和数的分母单调，也不要求任何有限异常素数猜想成立。

## 3. 分母小的有理扰动无法消掉主指数

**引理 2。** 对任意 h,r∈Q、q=h+r，令 a=den(h)、b=den(r)、c=den(q)，有

\[
a\mid bc,\qquad c\mid ab,\qquad
|\log c-\log a|\le\log b.                              \tag{4}
\]

证明：q=h+r 的公共分母为 ab，故 c|ab；从 h=q−r 同样得到 a|bc。
两侧取对数即可。这个界允许完全约分，也允许扰动分子任意大。

**推论 3。** 固定 s≥1。对任意有理数序列 r_N，若

\[
\log\operatorname{den}(r_N)=o(N),
\]

则

\[
\boxed{\log\operatorname{den}(H_N^{(s)}+r_N)=sN+o(N).}  \tag{5}
\]

这是定理 1 与 (4) 的直接推论。结论控制的是约分后的分母，不是
人为选取的清分母乘子；因而不能用额外 primitive 内容约分逃开它。
条件需要实际证明，例如 r_N=−H_N 并不满足该条件。

## 4. 对当前 Mellin 构造的作用与边界

连续或稀疏的右移指数族都可以把 Schur 有理近似写为
q=H_{2M}^{(9)}+r。若局部矩阵计算证明 log den(r)=o(M)，则
log P/M→18；与正矩误差的多项式下界结合，primitive 整数形式必然增长。
矩阵扰动的全参数上界及其适用的移动维数区域，另见
[右移区间算术稿](mellin-shift-arithmetic-2026-10-01.md)。

本引理没有控制任意未平移指数族，也没有证明该局部扰动条件对所有
M,D 都成立。它不能解决旧方向条件 S/J，更不能直接证明 ζ(9) 无理。

## 5. 精确证书

配套脚本 [verify_harmonic_denominator_stability.py](../scripts/verify_harmonic_denominator_stability.py)
使用标准库 Fraction 逐项检查 (1)、满足单位条件时的 (2)、
d_{s,N}|ℓ_N^s，以及 (4) 的两向整除和约分抵消案例。
有限检查只验证实现；定理 1 的无穷量词由第 2 节书面证明及标准素数定理承担。
证书在 [certificate.json](../verification/harmonic-denominator-stability-2026-10-01/certificate.json)。
