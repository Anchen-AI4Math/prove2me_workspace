# 任意真实分子的九阶 PF：原生作者验证完成

`formalization/CoefficientMapNumeratorPartialFractions.lean` 的完整原生源码、类型、定义全值和边界验证已经完成。作者记录为 PASS：24 项检查、188 个稳定文件绑定。最终源码 SHA256 `2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77`；`verification/formalization-coefficient-map-numerator-pf-2026-10-04/author-audit.json` SHA256 `7285317314696ed866c4b9333e6b0b9fdc01df1813048192aad1ecfabb24f2a5`。

这一步证明的是实际任意多项式分子的重构和正则点全部分分式。参数运输、F 矩阵运输、整数高度和 ζ(9) 无理性没有在本模块完成。独立原生／平台移植审核和平台投稿尚未进行。

## 已实际验证的范围

对任意 `m:Nat`、`A:Q[X]`，若 `A.natDegree<9(m+1)`，则 A 等于由 `FormalTransportData.numeratorLocalCoefficient` 的真实 jets 构成的 `numeratorPartialNumerator`。在每个 `t+k≠0,0<=k<=m` 的正则有理点，`A(t)/M_m(t)^9` 等于所有 `j=0..m,s=1..9` 实际局部系数的完整 PF。没有抽象 PF 数组、PF 存在性或局部系数等式作为端点假设。

此外真实 cleared series 的分母恒等式／唯一性、实际截断九项、各极点整除、全分母整除、严格次数域内实际 jets 单射，以及与既有 weighted jets 完全一致的定理均已编译。

已实际记录：Data 的 12 个定义与一个 witness specification，PF 的 4 个定义与 23 个完整证明；共 16 个完整 Definition type/value Expr、24 个完整 source-proof type Expr，全部 axiom 集合包含于 `propext,Classical.choice,Quot.sound`。16 个同源定义 alias 的整 type/value 内核比较与 16 个全函数 `rfl` 证书通过；16 个 alias 没有作为新的假设传入主要端点。

三个显式通用端点（分子重构、正则点 PF、实际 jets 单射）与源码声明的全类型内核比较全部相等。15 个通用／边界控制全部关闭且仅标准三公理，包含任意 m 的零分子与零 jets、`m=0,A=1`、`m=0,A=X^8` 临界简单极点、`A=X^9` 的次数域排除、两个极点的常数分子、weighted jets 一致性及 `n=1,q=1` 的真实 Q 分子 `(X+1)^2-4`。`1/t` 的合法 PF 不附带错误的可和结论。

## 执行与父对象来源

新作者项目 `.rt/np1` 在准备时不存在。Root 明确授权复用 `.rt/ps1` 中 14 个 PS 原作者父 `.olean`；每个原对象、自己的拷贝和对应原源码均精确绑定。它们是复用，**没有在本次重新编译，也没有称作 fresh**。没有使用 Root proof cache、独审对象或另一个 Data 作者的 ft1 对象。固定 Mathlib package cache 是唯一其它允许的对象路径。

Data 冻结原字节 `ae9f4eab8efecd88aaae5d4b13da7ba4bed7db89bbf257d3b0645e1b8584fb27` 在本项目亲自编译；PF 和值比较模块也亲自编译。17 个实际 `findOLean` 定位全部指向自己 np1 的缓存，其中 14 个是以上明确复制的父对象，3 个是新编译对象。实际 Lean 为 4.33.1，Mathlib git revision `0df444a360eaa60ab8c11dca51a86af692955474`。所有执行已经结束，无 live Lean handle，lane2 已交回 Root。

共 10 次真实 Lean 调用，9 成功、1 次新增审核控制失败保留并排除。完整核心 Data/PF 从首次编译即成功。原 PF 离线初版及其实际 source/log/exit 保留；最终仅修正文件头的验证状态说明，证明脚本没有改变。初版对象在这个最终构建后被覆盖、未及时归档，所以另一次显式调用在同一项目按原源码字节重现它；重现对象 SHA256 精确等于第一次实际记录的 hash，最终缓存没有被重现覆盖。该事实记录在 `historical-object-regeneration.json`，没有把重现当成首次输出的原始留档。

## 保留的失败与诊断

`r08` 原边界控制 actual Lean exit1：两个内联分号导致战术作用域／重复关闭目标的问题，另一个 n=1 控制未把 `C 2` 规范为多项式数值。原 source/snapshot/log/exit 和全部派生 `sorryAx` 输出完整保留且全部排除。新的 `b2.lean` 去掉冗余战术、用多行写索引零证明、在 ring 前加 `map_ofNat`，相同 15 个声明真实通过；原源码及 Data/PF 均未因此修改。

失败日志打印还触发一次 GBK stdout 的 Python1；实际 Lean1 已先写入 receipt，二者分别记录。第一次纯冻结预检也以 Python1 拒绝文件头比较，因为比较器用了 C 块注释定界符；修正为 Lean 的 `/- -/` 后确认核心源码只改文档，冻结成功。此诊断没有运行 Lean或改证明，并保留在 `freeze-preflight-diagnostic.json`。

旧 `coefficient-map-numerator-pf-offline-preparation-2026-10-04` 记录是原始未编译 snapshot 的历史证据，未被覆写成成功。当前成功证据来自新的作者目录。任务 scope／构建入口由 Root 登记；本作者没有 API、Root、凭证或 scope 写入。
