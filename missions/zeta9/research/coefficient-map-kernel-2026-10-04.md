# 原 quartic 五维 F 的真实核零、逆映射和指定有理 L

`CoefficientMapKernelBridge.lean` 使用已冻结的真实 R、Jet、全局部分分式、Reflection、FiniteSum、Summation、Aggregate 和 Telescoper。最高系数次数阻碍来自父代理独立完成并冻结的 `CoefficientMapShiftDegree.lean`。本环所有数学源均在 mission 内，不改共享模块、scope、API、凭证或旧冻结文件。

首先实际证明有限乘积的移位恒等式。它给

`numerator(t+1)*(t−n)*(t+n+1)=numerator(t)*t*(t+2n+1)`，

`poleProduct(t+1)*t=poleProduct(t)*(t+n+1)`。

由已证明的正规点分母非零，这正式推出实际 `R(t+1)*A(t+1)=R(t)*B(t)`，其中 A=(t−n−1)(t+n)^10，B=t^10(t+2n+1)。没有先约分掉可能为零的分子因子；单独类型审计在真实 t>n+1 域还核对安全的商比身份。

Telescoper 中的真实 P0 乘积给 `n!⁷*P0(t)=numerator(t)*(t−n−1)*(t+n)`，最后一个极点因子也被正式切出。因此实际正规点的

`R(t)*A(t)=n!⁷*P0(t)/polePolynomial_(n−1)(t)^9`

得到证明。真实核条件下，Telescoper 已构造实际分子 P=P0*H，并已证明 degree H≤7n−3。这里的 H 是该实际多项式整除的商。

本环将实际 Q=P/M⁹ 表示与上述 R*A 身份结合，再与实际差分 `R*W=Q−Q(t+1)` 相接。在无限个真正非零 R 的有理正规点 t>n+1，可以安全取消 R；多项式恒等原理随后给

`C(n!⁷)*W.comp(X*(X+C n)) = A*H−B*H.comp(X+C 1)`。

该关系由真实构造证明，不是作为核零定理的额外假设。此前整除商 H 的存在和次数界也在主定理内部由实际聚合输出零推出。

ShiftDegree 正式证明，若 H≠0，则右边在 degree H+10 的真实系数为

`(7n−2−degree H)*leadingCoeff H`。

degree H≤7n−3 使该因子非零；而 quartic W 左边的实际次数至多 8。故 H=0，再由真实 n!⁷ 非零及二次 composition 的注入性推出 W=0。没有假设 determinant、满秩、核零或逆映射。

由此在**原偶数 n≥2** 域，真正五维 `(B,rho_3,rho_5,rho_7,rho_9)` 对 degree≤4 的有理 W 单射。Fin5 有理 quartic 坐标映射是实际五维线性 endomorphism；有限维单射推出满射，得到已证明双射的 `actualAggregateEquiv`。定义

`inverseMultiplier b = coordinatePolynomial(actualAggregateEquiv.symm b)`，

正式证明其次数≤4、真实 F(inverseMultiplier b)=b、唯一性，以及 b≠0 时真实 W≠0。它是已证明真实 F 的逆，不是把逆映射性质当作定义假设。

随后已冻结 Summation 的实际绝对可和/HasSum 证明给任意有理五维 b 的真正级数

`Σ_(t≥1) weightedR n (inverseMultiplier b) t = b0+b1*ζ(3)+b2*ζ(5)+b3*ζ(7)+b4*ζ(9)`。

每个输出和其对应实际 L 都精确成立。类型审计另检查 b=(0,0,0,0,1) 的实际**非零有理 quartic** 原像和精确 ζ(9) HasSum；这并不保证该原像有整数系数、低高度或低整化成本。

原 n=0、W=X⁴ 的真实反例仍由 Aggregate 冻结审计保留：五维向量全零、W非零、rho_1=1，且强次数界不满足。当前核零/双射/指定 L 定理均明确要求 Even n 与 n≥2。ShiftDegree 的 n=1 共振边界也在其独立类型审计保留。本环不把全部局部系数阵列的注入偷换为聚合 F 的注入。

闭合范围为当前 p=9、q=1、m=n、d=0、原 even n≥2 的 quartic 有理五维 F：真实核零、线性双射、唯一有理原像与该原像的实际精确无穷 L。指定整数输出也有唯一**有理** quartic 原像；本环没有声称它必是整数 W。原局部系数/调和数分母整性、统一原像高度和整化成本控制、低 zeta 消元且非零的无限低高度序列，以及 zeta(9) 无理性仍未完成。一般 p、多层或高次 W 全核分类/固定次数归约也不在本环结论中。
