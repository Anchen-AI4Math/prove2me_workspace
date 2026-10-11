# 实际五维核中的 telescoper 与多项式整除桥

本环的假设是实际聚合五维输出为零、Even n，以及较强真实次数界。不是假设 F 单射、逆映射、telescoper 存在或核结论。`CoefficientMapTelescoper.lean` 从真实 Jet 系数定义

`q_j,s = Σ_(i=0..j) c_i,s`，

`Q(t) = Σ_(j=0..n−1) Σ_(s=1..9) q_j,s / (t+j)^s`。

Aggregate 的已证明消去给全部实际 rho_s=0，于是最后一个累积系数 q_n,s=0。有限分部求和恒等式逐阶证明实际 `weightedR(t)=Q(t)-Q(t+1)`，真正 R 的部分分式只在全部 t+k≠0 的正规点使用。有限正整数求和给 `finiteL_T=Q(1)-Q(T+1)`；固定有限个移位倒幂证明 Q(T+1) 趋于零。结合已证明的实际 finiteL 极限和 aggregate=0 推出 Q(1)=0，不要求 zeta 值线性无关。实际分子的 1..n 零点继续给 Q(1)..Q(n+1) 全零。

累积系数反射由真实局部反射、q_n,s=0 和 q 的递推直接证明：

`q_(n−1−j),s = (-1)^s q_j,s`。

因此正式重排有限和得 `Q(1−n−t)=Q(t)`，不引入有理 1 周期函数分类假设。继而 Q 在 −n..−2n 全零。

定义实际分子

`P = Σ_(j<n,s=1..9) C(q_j,s) * clearedPolePolynomial_(n−1),j^9 * (X+Cj)^(9−s)`。

实际正规点表示为 `Q=P.eval / polePolynomial_(n−1).eval^9`，并分别证明分母非零。degree P≤9n−1。

根节点由 `Fin(n+1) ⊕ Fin(n+1)` 给出真实正根 k+1 与负根 −n−k。证明其注入、每个节点与 pole 0..1−n 分离；根多项式正式等于

`P0 = (Π_(k=0..n)(X−C(k+1))) * (Π_(k=0..n)(X+C n+C k))`。

它是实际 monic 多项式、degree=2n+2。全部正规根值为零给每个真实线性因子整除 P，再用互素乘积证明整个 P0 整除 P。于是实际存在多项式 H 满足 `P=P0*H` 且 degree H≤7n−3。H=0 情况也准确覆盖。

以上一般桥在 n≥1、Even n、StrongProperMultiplier、实际 aggregate=0 的域正式成立，类型审计另代入原 n≥2 quartic W，从旧证明推导强次数界。本文件止于真实 quotient degree bridge；五维核零还需将 Q 的真实 quotient 连接到 `R*A`，证明其差分产生真实 `A*H−B*H(X+1)`，再使用最高系数次数矛盾。后续这些步骤放在单独 KernelBridge / ShiftDegree 文件中，不改本冻结源。

旧七份数学源和 Aggregate 冻结源、旧 objects/receipts、root/scope/API/凭证均不变。类型审计覆盖全部真实声明与定义值。探索 API probe 的未知猜测名称失败只保留为诊断，不作为通过的证明证据。
