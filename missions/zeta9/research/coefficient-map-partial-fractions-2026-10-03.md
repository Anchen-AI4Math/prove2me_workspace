# 实际全局部分分式恒等式

本环是 `round5/research/arithmetic.md` 中 Eq(3)/(4) 之前所用的有限部分分式前提，专门处理 p=9、单层 q=1、m=n。复用真实 R、真实 W(t(t+n)) 和已冻结的全部局部形式系数，未改 `CoefficientMap.lean`、`CoefficientMapJet.lean` 或 `CoefficientMapInjectivity.lean`。

记实际基础分子 N、加权分子 P=N·W(X(X+n))、极点多项式 Q=∏(X+j)，并定义 B_j=∏_{k≠j}(X+k)。新源直接定义

\[
\operatorname{partialNumerator}_{n,W}
=\sum_{j=0}^{n}\sum_{s=1}^{9}
c^W_{j,s}\,B_j^9(X+j)^{9-s}.
\]

这里 c^W 是冻结 `weightedLocalCoefficient` 从实际有理函数的清极点级数提取的系数，没有将它们作为任意系数参数。源码另证这同一个候选等于 Σ_j B_j^9·T_j(X+j)，其中 T_j 是真实加权清极点级数的九项截断。

在 t=−j+z，本极点项给 B_j(−j+z)^9·T_j(z)，与实际加权分子的差含 z^9；其他 i≠j 项因 B_i 包含 X+j，也都含 z^9。因此实际 P 与整个候选的差在每个 −j 处被 (X+j)^9 整除。新 `candidateClearedSeries` 使用与真实级数同一个实际单位分母，正式证明其分母恒等式和前九个系数等于实际级数。这些局部匹配不需要 proper 假设，也不引用最终全局恒等式作为前提。

复用已证的不同极点因子九次幂互素性，得到 Q^9 整除整个候选差。候选次数≤9n+8；实际加权分子次数≤2n+2deg W。故在

\[
2n+2\operatorname{natDegree}W<9(n+1)
\]

内，候选差次数严格小于 Q^9 的次数 9(n+1)，迫使差为零。`actual_global_polynomial_partial_fractions` 是这个真实多项式恒等式。

再证 Q(t)≠0 的实际求值条件和 Q(t)=(t+j)B_j(t)，在每个满足所有 t+k≠0、0≤k≤n 的有理数 t 上，得到

\[
R_n(t)W(t(t+n))
=\sum_{j=0}^{n}\sum_{s=1}^{9}\frac{c^W_{j,s}}{(t+j)^s}.
\]

`actual_global_partial_fractions` 是此真实有限点恒等式；分母非零在证明中明确处理。所有四次乘子满足 strict proper 界，独立导入审计覆盖原偶 n≥2 的整数四次乘子、n=0 边界、完整候选局部匹配和显式双重和多项式身份。

strict proper 界只保证分子次数低于分母次数，不能据此声称简单极点总和为零。原 Eq(2) 的更强次数界为 2n+2deg W≤9(n+1)−2，即 O(t^-2) 所需的界；本环没有证明 O(t^-2) 或 rho_1 消去。独立审计正式证明：n=0、W=X^4 满足 strict proper 界，却不满足更强界；其真实函数是 1/t，实际 c_{0,1}=1。这是对混淆两个界的明确反例。

本环完成有限全局部分分式恒等式。Eq(3) 的反射、偶阶总系数消去和 rho_1=0、Eq(4) 的精确无限求和/取极限、分母整性、原五维聚合 F、逆映射和 exact L 仍开放。完整局部阵列的已证单射不能替代五维聚合输出的可逆性。没有声称 Z9.F 或 ζ(9) 无理性闭合。

验证目录是 `verification/formalization-coefficient-map-partial-fractions-2026-10-03/`，保存实际全源和精确类型/定义值导入编译、observed exit、hash-bound receipt 与 manifest。新源直接用共享 Lean/Mathlib 独立编译，不将 mission 源路径当作 root Lake 注册目标，不写 root、scope、API 或凭证。
