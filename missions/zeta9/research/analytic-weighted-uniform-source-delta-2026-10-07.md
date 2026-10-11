# 完整真实加权解析上界的 SOURCE 增量

状态：**UNCOMPILED SOURCE**。本增量不改变此前冻结的五个基础文件、32 个证明体、
`preparation-audit.json`、`native-inputs-preparation-audit.json`，或其中绑定的历史研究记录。
没有调用 Lean、lake、API 或读取凭证。

新增三个文件：

- `formalization/AnalyticMomentBounds.lean`：15 个完整证明体、5 个真实定义。
- `formalization/AnalyticUniformMomentBound.lean`：11 个完整证明体、4 个真实定义。
- `formalization/AnalyticWeightedBound.lean`：12 个完整证明体、4 个真实定义。

总新准备为八个文件、70 个完整证明体。它们没有 `sorry`、新 `axiom` 或
`native_decide`；这种纯源码检查并不是类型检查或内核证明。

矩定义直接使用真实 raw 序列
`((actualR n (m+1) : ℚ) : ℝ) * ((m+1)*(m+1+n))^r`。
前 n 项由真实下降乘积的零因子证明为零。可和性直接从 tailPower 的真实 p 级数
比较推出，不导入完整 Summation 链，不新增 `Summable` 输入。

有限／无限分拆在 raw 索引 `2n-1` 进行。有限首段再分为 n 个真实零项与 n−1 个
紧区间项；`n=1` 的后半紧区间为空。尾段从 `k=2n` 开始，得到真实阶乘前因子的
无穷尾上界。

后续指数化简用对数恒等式处理自然数幂，避免将高次乘积的指数差当成假设。令

\[
b_r=\frac97(3/2)^r2^{-(9-2r)},\quad
T_{n,r}=\frac97\frac{(n!)^72^n(3/2)^r}{(2n)^{7n+9-2r}n^{2r}}.
\]

在 `n≥1, r≤4` 上，新源码证明候选为

\[
\log T_{n,r}\le\log b_r+7-(7+6\log2)n-2\log n,
\quad b_r\le729/224,
\]

进而得无穷尾的统一归一化界 `(729/224)e^7 e^(-cn)`。
所有自然数减法（`7n+9-2r`、`9-2r`）的合法截断域显式保留；`log n≥0` 只在
`n≥1` 上使用。`γ-c>297441/500000` 使用已验证实际 log2 下界。

五个真实矩的候选结论是

\[
S_{r,n}\le C(n+1)^{10}e^{-cn}n^{2r},\quad
C=5184e^{18}+(729/224)e^7,\quad c=2641/250.
\]

对任意真实 `W : ℚ[X]`、`W.natDegree≤4`，用实际
`Polynomial.eval_eq_sum_range'` 得到五项矩展开，证明实际 weightedR raw 序列
可和、绝对可和、HasSum 五矩组合，再由有限五项三角不等式给出

\[
\left|\sum_{m\ge0}\operatorname{weightedR}_n(W)(m+1)\right|
\le C(n+1)^{10}e^{-cn}\sum_{r<5}|w_r|n^{2r}.
\]

没有要求 W 的系数固定，也没有要求整数性或高度增长界。`changing_quartics_uniform_bound`
把任意 `W_n` 家族逐点接到同一个前因子。

定义明确的

\[
\varepsilon_n=\frac{\log C+10\log(n+1)}n.
\]

候选源码从实际 Mathlib
`Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1` 与常数除自然数趋零，证明
`ε_n → 0`；严格恒等式把前因子写成 `exp((-c+ε_n)n)`。最终
`actual_weighted_uniform_o_one` 同时量化所有 n≥1 和所有四次 W，ε 完全没有 W 输入。

必须实际编译并独立审核全部 70 个完整类型、证明体、所达定义值和标准公理边界，
才能把这条 SOURCE 链计作完整 Z9.A 的形式化结果。它不声称精确鞍点下界或极限
`f_*` 已形式化，也不解决整数高度、J 或 ζ(9) 无理性。

私有输入布局增量保留旧 8 份 SOURCE 副本，但补一个正确全模块路径的实际 Phase
SOURCE：`src/missions/zeta9/formalization/AnalyticPhase.lean`。
实际 native-export Upper 的 import 是该全路径；不能借 Root、aph1 或 api1 的
同名 `.olean` 来掩盖布局错误。新增三层源码使用该全路径 Phase 与短模块 Upper 的
自有对象闭包。任何实际编译依旧需要 Root 的明确 lane grant。
