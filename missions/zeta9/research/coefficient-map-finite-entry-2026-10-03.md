# Z9.F 的真实最高极点有限入口

源码为 `formalization/CoefficientMap.lean`。它实现 `roadmap/dag.json` 的
`Z9.F` 所指向 `round5/research/arithmetic.md` 式 (1)、(5)、(6) 的主线
特例 `p=9,q=1,m=n`，并未把完整 Z9.F 或 ζ(9) 无理性标记为完成。

定义直接使用实际有限乘积：

\[
N_n(t)=n!^7\prod_{i=1}^n(t-i)\prod_{i=1}^n(t+n+i),\qquad
Q_n(t)=\prod_{k=0}^n(t+k),\qquad R_n(t)=N_n(t)/Q_n(t)^9.
\]

删去 `Q_n` 中的 `t+j` 因子得到 `Q_{n,j}`，定义真正的清极点表达式
`clearedR=N_n/Q_{n,j}^9`，以及它在 `t=-j` 的值。这个值的定义不包含
二项式闭式。Lean 首先证明在全部原分母因子非零的点上
`R_n(t)*(t+j)^9=clearedR(t)`，再证明 `Q_{n,j}(-j)≠0`；因此在极点
处求清除后的表达式合法。原始有理函数按 ℚ 的全定义除法计算，不能
把未清除的函数在极点处的值称作极点系数。

求值证明分别计算两个上升乘积和删因子分母：

\[
N_n(-j)=(-1)^n n!^9\binom{n+j}{n}\binom{2n-j}{n},\qquad
Q_{n,j}(-j)=(-1)^j j!(n-j)!.
\]

由此推出所有自然数 `n`、`j≤n` 的真实清极点系数

\[
C_j=(-1)^{n+j}\binom nj^9\binom{n+j}{n}\binom{2n-j}{n}.
\]

它是非零整数；偶数 `n` 时符号严格等于 `(-1)^j`。证明覆盖端点
`j=0,n`，也覆盖 `n=0`，没有引入最高系数公式作为假设。

对任意真正的有理多项式 `W : ℚ[X]`（因而也适用于整数多项式），实际
加权函数定义为 `R_n(t)*W(t(t+n))`。其清极点值乘上实际
`W(-j(n-j))`。文件还证明真实局部坐标

\[
t=-j+z\quad\Longrightarrow\quad
t(t+n)=-j(n-j)+(n-2j)z+z^2,
\]

以及该恒等式在实际清极点加权表达式中的代入，作为式 (5) 的有限入口。
这里未把高阶 Taylor 系数或低阶部分分式系数直接定义成预期答案。

实际全源编译和八个端点的 `#print axioms` 全部通过，仅含
`propext`、`Classical.choice`、`Quot.sound`。独立导入审计保存完整实际
端点类型、九个定义的值和所有辅助定理的公理；证据在
`verification/formalization-coefficient-map-2026-10-03/`。

完整 Z9.F 的剩余义务包括实际低阶部分分式分解、反射与一阶消去、真实
无穷和 `L(W)` 的 ζ 系数恒等式、五维完整系数映射与所有偶数 `n≥2`
的可逆性，以及给定整数 `(b,a)` 的真实逆像。该有限入口不关闭这些
义务，也不关闭 J 或无理性。没有修改 PNT 冻结批次、root 共享模块、
scope、平台状态或凭证。
