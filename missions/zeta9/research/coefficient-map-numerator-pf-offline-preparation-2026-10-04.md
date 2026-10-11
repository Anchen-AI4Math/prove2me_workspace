# 通用真实分子 PF：离线候选交接

新文件 `formalization/CoefficientMapNumeratorPartialFractions.lean` 已写出 4 个定义、23 个完整证明脚本与 10 个未来 axiom 打印请求。它仍是 **未运行 Lean 的离线候选**，不能标为编译通过、平台证明或普遍定理已完成。静态检查没有发现 `sorry`／`admit`、新 `axiom`／`constant`／`opaque` 声明或内核绕过。静态检查不是 Lean 解析、 elaboration 或内核检查。

候选 SHA256 `929b1b89943e96c0cfe823d66698ad0465ec3081cb7cd3b603bbe8340c062787`，17786 bytes。静态准备记录在 `research/coefficient-map-numerator-pf-offline-preparation-2026-10-04.json`，SHA256 `4fee42a608a531c9a775cfd6837be89cf2f332e256ac7d6b01bac1c102e0e331`。实际 Lean 调用数为零。Data v1 和现有来源字节没有修改。

## 目标及实际数据

对任意 `m:Nat`、`A:Q[X]`，直接使用已有 Data 的真实对象：

\[
S_{m,j,A}=A(X-j)\,[\prod_{k\ne j}(X+k-j)^9]^{-1},\qquad
a_{j,s}=\operatorname{coeff}_{9-s}S_{m,j,A}.
\]

它们不是任意系数参数，也没有增加 PF 存在性假设。新 `numeratorPartialNumerator` 是这些真实系数与固定极点基的双重有限和。两个主要端点的候选声明为：

```lean
theorem actual_numerator_polynomial_partial_fractions (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) :
    A = numeratorPartialNumerator m A

theorem actual_numerator_global_partial_fractions (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) (t : ℚ)
    (hregular : ∀ k ≤ m, t + (k : ℚ) ≠ 0) :
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s
```

`m=0` 在该通用定理的正确次数条件下允许；运输应用的 `m=n+1,A=shiftedRemainderNumerator n q` 仍需其自己的 `n>=1` 与 `deg q<=9`。没有把 Q 的错误 n=0 范围加入端点。

## 已写的候选证明链

1. 真实 cleared series 的分母恒等式及唯一性：非零常数 cleared denominator 的 PowerSeries inverse 确实消去分母。
2. 真实 series 截断到九项，并把 `k=0..8` 重索引成 `s=1..9`，获得实际局部块。
3. 本块与 A 匹配九个 jets：差被 `X^9` 整除。其他块被目标极点因子的九次幂整除。
4. 各极点幂两两互素，因此完整分母 `polePolynomial m^9` 整除实际 A 与实际部分分式分子的差。此时未用严格次数，也没有用 PF 存在性。
5. 部分分式分子次数至多 `9m+8`；真实 A 次数小于 `9(m+1)`。非零差若被次数为 `9(m+1)` 的分母整除会矛盾，故重构等式成立。
6. 只在正则点使用分母因子分解与 `9-s+s=9`，把真实分子恒等式除成完整 PF。
7. 候选 additionally 证明第一九项匹配、与原 weighted jets 完全一致、系数对减法保持线性、严格次数域内零 jets 推出 A=0 及实际 jets 单射。这是实际分子之间的唯一性，没有先假设一个抽象 PF 数组。

## 实际依赖与复用范围

直接 import 只有两个：

- `CoefficientMapFormalTransportData`：仅使用 `numeratorClearedSeries`、`numeratorLocalCoefficient` 的真实定义。其 import 闭包目前经过 ParameterShift、KernelBridge 和 Connection；它自己的数据候选仍需真正编译。
- `CoefficientMapPartialFractions`：经 Injectivity、Jet、CoefficientMap 获得已证明的纯多项式／级数工具。

直接复用既有 PF 的 `truncation_remainder_X_pow_dvd`、`polynomial_X_pow_dvd_of_series`、`clearedPolePolynomial_comp_shift`、`shifted_divisibility_implies_pole_divisibility`、`clearedPolePolynomial_natDegree`、`polePolynomial_eval_ne_zero`、`polePolynomial_eval_factor` 和 `actual_series_from_shifted_numerator`。复用 Injectivity 的 `pole_factors_coprime`、`polePolynomial_pow_natDegree` 及真实 `weightedNumerator`；复用 Jet 的 `shiftedClearedDenominator_constant_ne_zero`。

其余证明从现有特定 weighted numerator 的版本泛化到真实任意 A，没有改动那些旧文件。Mathlib 的 PowerSeries trunc/inverse、Polynomial degree/composition、Finset 与 `ring`／`omega` 都由该 import 闭包提供。证明没有使用实数 zeta、zeta 独立性、整数高度、原 aggregate 的核为零或最终运输作为假设。

## 后续真正编译的难点

必须先由 Root 明确释放／授予 Lean lane；此离线准备未启动任何 Lean，也未创建编译对象。

- Data 首次编译及其实际依赖可用性需要先验证；候选无权把 Data 的未编译 witness specification 当成当前编译证据。
- 最可能的 elaboration 点是 Polynomial 到 PowerSeries 的 coercion：本块九项匹配中的 `convert h using 1`、候选第一九项中的 `rfl`，以及逆级数的分母恒等式。它们保留旧已执行证明的形状，但只有运行才知道简化器是否完全闭合。
- `numeratorLocalTruncation_comp_eq_sum` 的有限双向重索引需要核对 Nat `9-s` 的所有侧条件；目标始终只限于 s=1..9。
- `actual_numerator_global_partial_fractions` 刻意在 `conv_lhs` 中重写 A，避免把 RHS 的真实 A jets 一并改成重构分子的 jets。未来须确认该局部 rewrite 与之后的有限和展开按预期 elaboration。
- 多个已打开 namespace 里的旧辅助名称、通用次数比较与级数／多项式正规化可能需要显式全名或局部 `change`；当前没有以这些可能性声称测试通过。

真正运行后的最小有意义边界控制应含 `m=0,A=0`、`m=0,A=1`、`m=0,A=X^8`（合法 PF 的简单极点，不能额外声称可和）、一个多极点 A、与原 weighted numerator jets 的全类型一致性，以及 Q 的 `n=1` 实际分子。保持错误的 `m=0,A=X^9` 次数条件不可满足；不在极点做全定义除法的局部系数识别。之后核对所有主要端点的完整类型及实际 axiom 结果。

## 清分母短路线的判断

先前独立审阅的整多项式桥

\[
N_{\rm new}=X^9(X+n+2)^9N_{\rm old}(X+1)
+(X+n+2)^9\widehat A-X^9\widehat A(X+1)
\]

可以逐极点移位后，除去真实非零常数 cleared denominator，再利用 `X^9` 的前九项消失直接给每个 jet 的运输及 rho。这样局部系数桥不必先做有理实点的无限根唯一性往返。Root 和作者已收到这一分工建议。

但 B 的纯有理修正仍需识别 `sum c_(j,s)/(j+1)^s=Q(2)`。它需要实际 Q 的分子重构与正则点求值，或另一个同样强的专用恒等式。本模块正提供这一共享工具；因此短路线能省局部数组的有理函数唯一性环节，不能凭局部清分母桥直接略过 B 的求值义务。

当前没有 Root／API／凭证／scope 写入，且 KernelBridge 已冻结审核目录不在本工作修改范围内。新源码的归属与构建入口由 Root 登记，编译结果待真正执行后另外记录。
