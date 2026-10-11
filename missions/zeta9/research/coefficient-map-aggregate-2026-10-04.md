# 实际五维聚合 F 与四次坐标

`formalization/CoefficientMapAggregate.lean` 定义实际映射

`W ↦ (B(W), rho_3(W), rho_5(W), rho_7(W), rho_9(W))`，

其中 B 使用已冻结 FiniteSum 的有限调和常数，rho 使用已冻结 Jet 的真实局部幂级数系数。这是 round5/research/arithmetic.md §4–5 的形式五维输出，和所有 (j,s) 的局部系数阵列不同。

文件首先从实际 `W.comp(localU)` 和真实 `clearedSeries` 的乘法证明每个局部系数对 W 加法和有理数标量线性，再证明 B/rho 的实际线性，得到 `aggregateLinearMap`。没有以线性性质为定义替换真实系数。

四次坐标输入为 `a : Fin 5 → ℚ`，实际多项式为 `Σ_i C(a_i) X^i`。其次数不超过 4；取 i 阶系数恢复 a_i，全部次数不超过 4 的多项式也由五个系数恢复。因此四次坐标空间与实际 quartic 多项式空间的对应正式闭合。`quarticAggregateLinearMap` 是这两个已证明真实线性映射的组合。单独类型审计另检验五个标准基映射为 `1,X,X²,X³,X⁴`，以及 F 的对应真实单项式列。

五维聚合输出为零，结合已证明的 Even n 和较强次数界，可以推出所有 s=1,...,9 的实际 rho_s 均零。五维输出零也使实际 `exactL` 为零；原偶数 n≥2 的 quartic 域得到实际 HasSum=0 检查。这些是核中的必要性质，并不等于证明核只有零元。

边界反例正式保留：n=0、W=X⁴ 非零且满足严格 proper 界，但其五维聚合输出全部为零，而实际 rho_1=1，强次数界不成立。因此不能把 quartic 聚合单射写成所有 n 的结论。预期核零结论应限制在原偶数 n≥2 的域内。

本环不假设 determinant 非零、满秩、核平凡或逆映射。实际 quartic 聚合核零和五维可逆性仍 Open，另在新 Telescoper 源推进：真实 cumulative local coefficients 的差分、边界和对称零点，随后还需实际分子整除和最高系数次数矛盾。没有修改七份冻结旧源、旧 objects/receipts、root、scope、API 或凭证。
