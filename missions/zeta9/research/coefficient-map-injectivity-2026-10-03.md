# 完整实际局部系数阵列的单射桥

本环从冻结的 `CoefficientMap.lean` 与 `CoefficientMapJet.lean` 中的真实有限有理函数及形式幂级数出发。新源 `formalization/CoefficientMapInjectivity.lean` 不改变这两份源，不引入系数分解、矩阵单射或原结论作为假设。

对任意自然数 n，定义实际加权分子

\[
P_{n,W}(t)=(n!)^7\prod_{i=1}^n(t-i)\prod_{i=1}^n(t+n+i)\,W(t(t+n)).
\]

完整局部输出是所有 \(0\le j\le n\)、\(1\le s\le9\) 的冻结 `weightedLocalCoefficient n j s W`，等价于 \(\mathrm{Fin}(n+1)\to\mathrm{Fin}(9)\to\mathbb Q\)。所证域为真正严格 proper 界

\[
2n+2\operatorname{natDegree}W<9(n+1).
\]

在此域，全部实际局部系数为零推出 W=0；两个域内乘子的完整局部输出相等推出 W=V。`fullLocalCoefficientMap_injective` 直接证明该域子类型上输出函数的 `Function.Injective`，没有只比较最高系数或只取部分 j 节点。

证明链如下：九个局部系数为零使真实局部加权级数被 X^9 整除；乘以冻结的真实清极点分母恒等式，得到移位多项式分子被 X^9 整除。逆移位给每个 `(X+C j)^9` 整除 P。不同 j 的线性因子及其九次幂互素，故整个 `polePolynomial n ^ 9` 整除 P，其次数等于 9(n+1)。实际 P 的次数不超过 2n+2deg W，严格界迫使 P=0。基础有限分子含非零 `(n!)^7` 和非零线性因子，所以非零；真实内层 `X*(X+C n)` 次数恰为 2，从非恒定多项式复合消去得到 W=0。对差 W−V 使用次数的 max 界及系数线性性得到单射。

所有四次乘子都满足该严格界，证明适用于每个 n，包括 n=0，此时内层是 X^2、分母是 X^9。独立导入审计还检查原 `Even n`、`2≤n`、整数系数四次乘子语境；整数多项式转为有理数后通过注入的映射返回 W=V。审计另证新多项式商的求值恰等于原 `weightedR`，不以抽象加权分子替换真实有理函数。

这仅完成完整局部 `(n+1)×9` 系数阵列的单射桥。原 Z9.F 的五维输出由这些局部数据进一步聚合为 zeta/常数线性形式，聚合仍可能丢失信息。本环没有证明那五维映射的单射、满射、逆映射或 exact L；全局部分分式恒等式、无限求和恒等式、反射/消去、分母整性与 prescribed integer-output 逆像仍是后续义务。也不声称 Z9.F 或 ζ(9) 无理性闭合。

实际编译与完整精确类型/定义值记录位于 `verification/formalization-coefficient-map-injectivity-2026-10-03/`。源码直接用共享 Lean 4.33.1 / Mathlib 0df 工具链独立编译，不将 mission 源路径冒充 root Lake 注册目标，不写 root、scope、API 或凭证。
