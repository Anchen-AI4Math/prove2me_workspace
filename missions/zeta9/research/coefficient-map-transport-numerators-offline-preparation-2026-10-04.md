# 清分母运输的离线 Lean 候选

当前候选 `formalization/CoefficientMapFormalTransportNumerators.lean` 已保存，
11083 bytes，SHA256 `28d831023450bd067499b3d57b20b89d38e78e6113b482ad95904962c9920b0f`。
它包含 15 个完整证明脚本，未运行 Lean；该计数只是源码清单，不是已编译声明数。
没有证明占位符。Matrix 的 73 个冻结准备文件和所有既有 Data/Bounds/PF/Kernel/
Connection 冻结记录均未修改。

最终候选端点 `actual_chosen_cleared_numerator_transport` 对所有 `n>=1`、
`r:Fin5` 使用实际 `connectionP n r` 和 `connectionQ n r`：

\[
N_{n+2,X^r}=X^9(X+n+2)^9N_{n,P_r}(X+1)
 +(X+n+2)^9\widehat A_{n,q_r}(X)-X^9\widehat A_{n,q_r}(X+1).
\]

端点没有抽象 Connection 关系、PF 存在性、系数运输、F 可逆性、Even、求和或
ζ 独立性假设。`chosen_connection_equation` 提供真实选定见证的方程。

候选先复用真实 `positiveProduct_shift` 推出
`positiveProduct n t * (t-n-1) = (t-1) * prod_(i<n)(t-i-2)`，再证明
`connectionRemainder n q t = remainderNumerator n q evalt / ((t-1) M_n(t))^9`。
只在 `t-1` 和真实极点分母非零处清分母，未除以可能为零的 `actualR`。
独立的 `connectionRemainder_eval_two` 沿用 Bounds 的真实分子零值，保留 n=1
所需的额外正根因子。

产品接口提供 `M_(n+1)(x)=x M_n(x+1)`、
`M_(n+2)(x)=x M_n(x+1)(x+n+2)`，并恢复它们的整多项式版本。
移位余项的两个分母分别是 `M_(n+1)(x)^9` 和 `M_(n+1)(x+1)^9`。
现有 `actual_original_connection_transport` 的真实 H 包含 `t+2n+1`，候选
直接使用该已证明身份，没有手工替换成不同 H。

最终路线在全部正有理数 `x>0` 上证明真实加权函数身份，统一九次分母，再用
已核对的 `Polynomial.eq_of_infinite_eval_eq` 与 `Set.Ioi_infinite` 得到多项式
相等。这里使用的是无限正有理数集合；有限 360 项证书未参与证明。

读验过的依赖字节：Data SHA256
`ae9f4eab8efecd88aaae5d4b13da7ba4bed7db89bbf257d3b0645e1b8584fb27`；Bounds
`4e26f0ba526b16e983633cf000cff9d9062209489b740817369190c62e26d646`；ParameterShift
`5e472326fd47f4ad470cf89493fa75e57e22806cd1b1ac12697c878b06f69065`。
Mathlib 本地固定版本中已只读核对 `eq_of_infinite_eval_eq`、`Ioi_infinite`、
`Finset.prod_range_succ`、`Finset.prod_range_succ'` 和 `div_left_inj'` 的实际接口。

首次实际编译可能需要处理：有限产品的 Nat 强制转换／结合次序，`rw` 对实际
分母表达式的精确匹配，以及两处 `field_simp` 后的九次幂环规范化。候选给出了
完整脚本，但这些 elaboration 边界尚未核验。它不依赖新泛化 PF 的编译状态；
后续九阶局部 transport/rho 可使用本多项式身份，B 的正则点重构再使用新 PF。
