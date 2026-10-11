# 真实五矩的显式统一解析界：源码准备

本记录是纯数学审查与 **UNCOMPILED SOURCE** 交接。它不声称新文件已通过
Lean、内核检查、独立形式化审核或平台接受。现有相位证明的实际编译依赖必须取
`verification/formalization-analytic-phase-upper-bound-2026-10-07/native-export/`
内的两个已验证导出文件；同名 shared 原稿是历史未编译源码。

此次准备的目的，是把本地第七轮式 (6) 的系数无关 `o(1)` 落实为真正原函数的
显式多项式前因子，不把矩界或阶乘表示当作假设。

## 原始对象与域

原函数必须使用 `formalization/CoefficientMap.lean` 的实际定义：

\[
R_n(t)=n!^7
\frac{\prod_{i=0}^{n-1}(t-i-1)\prod_{i=0}^{n-1}(t+n+i+1)}
{\bigl(\prod_{j=0}^{n}(t+j)\bigr)^9}.
\]

这里的 Lean 原对象取值于 `ℚ`。先证明在自然数 `k > n` 处的精确有理恒等式，
再通过真实 `ℚ → ℝ` 强制转换使用实对数。`n ≥ 1` 是解析界的域；不需要偶数
条件。偶数条件只出现在后续把真实和识别成含 ζ 输出的 `exactL` 等式中。

对于 `1 ≤ k ≤ n`，原始下降乘积在 `i = k - 1` 处有零因子；极点乘积每项为正。
所以这些级数项真正为零，不能以重新定义原函数的方式跳过它们。

令 `u_n(k)=k(k+n)`，真正五矩是

\[
S_{r,n}=\sum_{k>n}R_n(k)u_n(k)^r,\qquad 0\le r\le4.
\]

最终必须用实际 `CoefficientMapSummation.actualSeries`（取单项式）或与其精确
重索引等价的序列定义矩。该文件的真实绝对可和定理可复用；新解析定理不能新增
`HasSum` 或矩可和假设。

## 阶乘误差与相位的完整连接

`AnalyticFactorialBounds.lean` 给出无假设归纳证明源码：

\[
n\log n-n\le\log(n!),\quad n\ge0,
\]
\[
\log(n!)\le(n+1)\log n-n+1,\quad n\ge1.
\]

归纳下界的增量来自 `n log((n+1)/n) ≤ 1`；归纳上界的增量来自
`(n+1)(log(n+1)-log n) ≥ 1`。两者都直接用
`Real.log_le_sub_one_of_pos`，没有 Stirling 或积分渐近假设。零、一步和所有
取对数的正性条件单独保留。

`AnalyticRationalFactorial.lean` 从实际有限乘积推出

\[
R_n(k)=n!^7\frac{((k-1)!)^{10}(k+2n)!}
{(k-n-1)!((k+n)!)^{10}}>0\quad(k>n).
\]

随后先严格消去两处移位：
`log((k-1)!)=log(k!)-log k`，以及
`log((k-n-1)!)=log((k-n)!)-log(k-n)`。
只对消去后的阶乘套上下界。所有线性项精确抵消，得到

\[
\log R_n(k)\le n f(k/n)+7\log n+\log(k+2n)+\log(k-n)+18.
\]

常数 `18 = 7 + 10 + 1` 来自三个上界。若直接给移位阶乘各自加误差，会错失这里的
精确抵消；新的源码没有走那条路线。`AnalyticRationalLogBound.lean` 给出上述
真实点态界，以及用已验证相位 `f(x) ≤ -c`、`c=2641/250` 得到的指数界。

## 紧区间：有限项数及权重

当 `n < k ≤ 2n` 时，`(k+2n)(k-n) ≤ 4n²`，故

\[
R_n(k)\le4e^{18}n^9e^{-cn},\qquad u_n(k)\le6n^2.
\]

此区间有 `n` 个整数。因此，对所有五个 `r`，

\[
\frac{1}{n^{2r}}\sum_{n<k\le2n}R_n(k)u_n(k)^r
\le4\cdot6^r e^{18}n^{10}e^{-cn}
\le5184e^{18}n^{10}e^{-cn}.
\]

接合无限和时可以用半开区间 `n < k < 2n` 与 `k ≥ 2n` 精确分拆：其紧区间
只有 `n-1 ≤ n` 项，因此同一上界成立。也可以使用闭紧区间与闭尾区间的双覆盖，
因为实际各矩项非负；重复的 `k=2n` 只使上界变大。`n=1` 的半开紧区间为空，
尾区间仍覆盖所有 `k>n`。

## 远尾：实际乘积与定量 p 级数

`AnalyticRationalTail.lean` 直接从乘积逐因子证明，在 `k ≥ 2n`、`n ≥ 1` 时

\[
R_n(k)\le (n!)^7 2^n k^{-7n-9},\qquad
u_n(k)\le\tfrac32k^2.
\]

令 `s=7n+9-2r`。则 `s ≥ 7n+1 ≥ 8`，`s-1 ≥ 7n`。
`AnalyticPSeriesTail.lean` 给出没有可和假设的定量尾界源码：

\[
\sum_{k\ge M}k^{-s}\le M^{-s}
\left(1+\frac{M}{s-1}\right),\qquad M\ge1,\ s\ge2.
\]

证明使用实际 Mathlib `AntitoneOn.tsum_comp_add_le_integral`，对真实函数
`x ↦ x^(-s)` 在 `M>0` 的域调用 `integrableOn_Ioi_rpow_of_lt` 与
`integral_Ioi_rpow_of_lt`，再接回首项。必须保留实际自然数幂与实幂之间的等式。

取 `M=2n` 得 `1+2n/(s-1) ≤ 9/7`。配合真实阶乘上界，所有幂次精确化简为

\[
\frac{1}{n^{2r}}\sum_{k\ge2n}R_n(k)u_n(k)^r
\le\frac97\,3^r2^{r-9}n^{-2}e^7e^{-\gamma n},
\quad \gamma=7+6\log2.
\]

最大有理前因子在 `r=4` 为 `729/224`。已验证的
`log 2 > 693147/1000000` 给出

\[
\gamma>\frac{5579441}{500000}
=11.158882>c,\qquad
\frac{5579441}{500000}-\frac{2641}{250}
=\frac{297441}{500000}>0.
\]

这里的有限小数只是有理数的显示形式。证明与脚本均使用精确分数。

## 五矩与变化系数的最终目标

紧区间与尾区间合并，目标显式常数为

\[
C=5184e^{18}+\frac{729}{224}e^7>0,
\]
\[
0<S_{r,n}\le C(n+1)^{10}e^{-cn}n^{2r}
\quad(n\ge1,\ 0\le r\le4).
\]

严格正性可由 `k=n+1` 这一真实正项给出。任意随 `n` 变化的五个系数
`w_{n,r}` 都将满足

\[
\left|\sum_{k>n}R_n(k)\sum_{r=0}^{4}w_{n,r}u_n(k)^r\right|
\le C(n+1)^{10}e^{-cn}\sum_{r=0}^{4}|w_{n,r}|n^{2r}.
\]

这里的三角不等式与有限五项交换要由实际绝对可和定理支持。若用
`ε_n=(log C+10 log(n+1))/n`，便得到真正系数无关的 `ε_n → 0`。
不能把该结论提前假设在源文件中，也不能从一组固定系数或有限样本推广到所有变化
系数。系数全为零时最终不等式直接为零，不需要取形式绝对值的对数。

## 交付与尚待完成

已有 5 个新文件、32 个完整证明体 SOURCE：
`AnalyticFactorialBounds.lean`、`AnalyticRationalFactorial.lean`、
`AnalyticRationalLogBound.lean`、`AnalyticRationalTail.lean`、
`AnalyticPSeriesTail.lean`。前四文件的冻结纯准备记录在
`verification/formalization-analytic-factorial-preparation-2026-10-07/preparation-audit.json`。
其 501 次精确分数检查只核有限边界与数值表达，不代替任意 `n,k` 的内核证明。

尚待实际作者编译、独立检查，以及真实矩重索引、幂次/指数化简、有限紧区间和、
无限尾比较、变化系数三角界与 `ε_n → 0` 的完整源码。只有完成并验证这些步骤后，
才能称完整 Z9.A 已形式化。算术高度、第二独立短方向 J 与 ζ(9) 无理性并不由这条
解析界自动解决。
