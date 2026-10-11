# ζ(9) 公开研究总览

## 2026-10-07 当前平台目标

当前使用新公开提案 **Irrationality of ζ(9)**，ID
`19653cff-d481-498a-a717-10630d1ca1b7`。用户已提交；最新 v0.12.1 认证回读为
**`In review / public`**，`mission_id` 为空，等待平台审核。用户提交步骤已完成。
新提案包含 88 个引用项（18 个定义）和 69 条里程碑；67 个支持定理为 `Proved`，两个支持定理及无理性根目标仍为 `Open`。**57 份已保存完整证明回执全部 `ACCEPTED`**。

Matrix 三条定理已获完整证明验收，并被新提案引用。新增通用分子部分分式
三条定理及一个定义也已公开，三份完整证明全部 Accepted：实际多项式部分分式、
实际有理函数部分分式和完整局部系数单射性。它们尚未被审核中的提案引用。
七个对应本地模块已逐个构建，随后正式运行 `python scripts/workspace.py build zeta9` 成功。
该任务构建保留既有 PNT statement mirror 的类型集成边界；完整 PNT 证明有另行独审记录。

最新本地阶段：16 条五输出运输已通过原生作者及独审，Root 重哈希全部 1085 个独审绑定无差异；平台移植待完成。17 条参数求和运输的原生作者
冻结也已通过，Root 重哈希 755 个绑定无差异。后者包括偶数 n ≥ 2 的真实 HasSum、
绝对可和、tsum 及选定输出运输；独审已 PASS，Root 重哈希 1185 个绑定无差异，平台移植待完成。
解析相位的 34 条原生作者及独审证明已通过，给出所有 x > 1 的 phase(x) ≤ −2641/250；
Root 重哈希全部 26076 个独审绑定无差异，平台移植正在进行。
新统一解析链有 8 个 SOURCE 文件、70 段完整候选证明体和 13 个定义；作者实际编译已启动，尚无全链验证。
全体加权矩的统一解析估计 Z9.A、整数原像与分母高度、J 和 ζ(9) 无理性仍未封闭。

[Current platform readback](formalization/platform/readback-2026-10-07/user-submission-current-57/progress-audit.json), [PF acceptance](formalization/platform/coefficient-map-numerator-pf/publications-for-new-mission-2026-10-07/publication-audit.json), [Scoped task build](formalization/platform/coefficient-map-numerator-pf/publications-for-new-mission-2026-10-07/root-scoped-build/actual-build-receipt.json), [Parameter author Root rehash](verification/formalization-project-handoff-2026-10-07/root-parameter-author-complete-binding-rehash.json), [Phase author Root rehash](verification/formalization-project-handoff-2026-10-07/root-phase-author-complete-binding-rehash.json).

[Uniform analytic SOURCE handoff](research/analytic-weighted-uniform-source-delta-2026-10-07.md).

## 以下保留 2026-10-04 研究快照

版本日期：2026-10-04。目标是证明单个数 ζ(9) 无理。**当前没有完整无理性证明。**
资料分为书面证明、有限证书和平台 Lean 验证三种状态。

## 当前数学成果

原加权格路线的系数映射、运输关系、解析估计和体积部分已有本地书面证明。
在这些结果下，主 J 出口规约为排除最短 primitive 整数方向最终固定，且与目标等价。
S 是更强的充分条件，不是额外必须通过的必要障碍。
完整边界见 [direction-frontier](research/direction-frontier-2026-10-01.md)。

| 方向 | 已证明的内容 | 仍缺少的输入 |
|---|---|---|
| [主方向与新投影](research/direction-arithmetic-next-2026-10-02.md) | 全参数 Gram gcd 整除关系、中心分母除数、同侧区间及其最小分母算法 | 对真实无限序列证明方向不固定或父分母增长；这些是等价出口，不能预设无理性 |
| [增长维数正一次 Gram](research/growing-rank-one-route-2026-10-02.md) | h 阶、2h+3 个平方极点始终给一次式；正误差有严格指数夹逼 | 完整既约分母 T_h 的渐近控制；真实误差小不保证整数形式小 |
| [一阶任意分散极点](research/dispersed-pole-frontier-2026-10-02.md) | h=1、S=1 全参数分类：m≤5 primitive 值指数增长；m≥6 primitive 为 1 | 该族已排除；定理未覆盖高阶分散矩阵 |
| [七阶导数孤立级数](research/new-linear-form-route-2026-10-02.md) | 仅含 1、ζ(9) 的恒等式；正误差首项为 (16/15)n⁻⁴log⁵n；完整 primitive 大素数估值 | 完整约分成本或异常素数质量界 |
| [八重零点修复](research/new-linear-form-route-repair-2026-10-02.md) | 严格消除前 n 个端点漏项，仍只含 1、ζ(9) | 最终非零性、实际解析率、完整约分估计 |
| [固定复杂度正矩前沿](research/progress-2026-10-01-frontier.md) | 聚类极点、连续极点与若干有界分子族的 primitive 增长定理 | 不能直接套用到增长维数或全部高阶分散几何 |

这些是可替代的研究方向，证明任一有效序列的非零整数形式趋零即可完成目标。
不需要同时解决全部路线。

## 有限证据能说明什么

最新五组脚本已由根代理从冻结源码重跑，全部 PASS，书面命题也经过独立复核。
六个真实最小分母投影样本（至 n=192）严格满足 `0<abs(qζ(9)−p)<1`；
39 个增长维数 Gram 实例均给正误差，但 primitive 值未小于 1。
701 个整数分散极点配置和 213 项素数估值用于复核全参数定理；它们不是无限穷举。
孤立级数有 324 项残数核验、79 项素数同余；八重零点修复有 90 项残数和 168 项端点核验。

参数、未触发的有限分支、源码 SHA-256 和证明层级见
[统一记录](verification/continuation-2026-10-02/README.md)及
[复核说明](research/continuation-review-2026-10-02.md)。
有限衰减趋势、单个小值、构建成功均不能替代缺少的数学无穷量词。

## Lean 与平台状态

2026-10-04 UTC 最新认证回读原 mission：95 条里程碑，66 条链接正式 theorem，64 条为 completed。
平台 v0.11.8 的 [实时审计](formalization/platform/readback-2026-10-04/p51-final/progress-audit.json) 核对 51 份已提交完整证明，全部 Accepted、公开 Proved 并链接原 mission，包含 Telescoper、KernelBridge 与 Connection 九份新证明。
根 `ZetaNine.irrational_zeta_nine` 为 `Open`；两条指数小形式义务仍为 `Open`。
已经接受的证明包括通用无理性准则、有限素数预算、矩与加权平均，以及下述实际系数、局部展开和求和构造。
具体新构造仍缺少相应的整数归一化及无限序列输入，ζ(9) 无理性保持 Open。

另一个 `Zeta9Note.*` 抽象层提案与本 mission 是不同对象，旧“8/8 Proved”记录仅适用于
那八条通用陈述。本次更新的是用户指定的原 `ZetaNine.*` mission。
新研究现在有十一个核心目标的完整 solution 通过实际任务构建：Gram gcd、中心分母、
八重零点导数和、调和分母上界与稳定性、三项实际有限素数算术，以及 C3 的全参数
符号下界与所有偶数系数非零性。它们的公理输出只有 Lean 标准三项公理。
实际基础定义与十六批已验收声明均已 `PUBLISHED`；十六批共五十一份完整证明已获 `ACCEPTED`，
回读为公开 `Proved` 并链接原 mission，已计入上述数量。C3 两条和 PNT 四条均已验收。
实际调和和分母的无条件全序列渐近率及九阶双倍索引的率 18 已由真实 PNT
依赖封闭并独立重编译；它们没有预设 harmonic baseline。共享目录的 PNT 陈述镜像
只用于类型集成，完整真实 PNT 编译和提交源码的独立审核另有标准三公理记录。
九份完整证明的 [独立复核包](https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/zeta9-formal-proofs-2026-10-02.zip)
已公开，并由原 mission 首页提供入口；附有重新构建和远端 SHA-256 记录。
另有 [C3/PNT 完整源码补充包](https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/zeta9-advanced-proofs-2026-10-02.zip)，
真实独立构建和公理核验通过，远端哈希已验证。具名独立审核记录提供正确完整 import
闭包；原 manifest 列表漏记八个 Architect 子模块，但这些源码全部包含在 ZIP 内。
完整形式化的分组、日志和剩余义务见 [formalization](formalization/README.md)。

原系数路线已有进一步的真实 Lean 构造：最高极点系数、全部九阶局部卷积、完整数组单射性、全局部分分式、反射消去和有限求和已通过独立
移植审核；加上真实移位次数障碍与聚合线性结构，二十七个完整 solution 已通过正式任务构建、平台接受并链接。完整局部数组在
严格 proper 域内的单射性、真实全局部分分式、反射消去和实际有限求和均已通过独立数学审核。完整数组的
单射不能替代原五维聚合 F 的可逆性；严格 proper 的 O(1/t) 界也不保证无限 L 收敛。
原 `p=9,m=n,d=0` 的绝对可和及精确无限 L 身份已本地完整编译并通过独立审核，
覆盖原偶数 `n≥2` 的整数四次乘子；三份完整无限求和证明现已 Accepted、公开 Proved 并链接。[审核记录](verification/formalization-coefficient-map-summation-independent-2026-10-04/independent-review.json)
包含 16 项检查、31 项作者类型复验和 56 项独立类型及边界记录。
原偶数 `n≥2` 情形的五维聚合 F 核为零、双射、任意有理目标的唯一四次逆像及指定
线性形式的真实 `HasSum`/绝对可和，已完整编译并通过 22 项独立审核、296 个哈希绑定。
纯 ζ(9) 目标有非零有理四次原像；整数逆像、有效分母高度、趋零非零整数形式和 J
仍需处理。证据见 [KernelBridge 审核](verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04/independent-review.json)。
KernelBridge 的完整平台作者移植已通过 52 项检查及 57 次实际 Lean 执行，3817-job 正式任务构建通过；独立平台审核通过 38 检查及 1381 绑定，88 次 Lean 执行成功，定义及三条精确定理声明已 Published，三份完整证明已 Accepted、公开 Proved 并链接。
Telescoper 的独立平台审核已通过 36 项检查、1535 个哈希绑定，75 次 Lean 执行及一次运行时版本检查成功；定义和三条精确定理已 Published，三份完整证明已 Accepted、公开 Proved 并链接。
原 D/H 连接系统已有独立原生证明；平台作者移植的 33 检查、372 绑定及 3824-job 正式构建已通过，独立移植审核已通过 47 检查及 940 绑定，三份完整证明已 Accepted、公开 Proved 并链接。真实 R 的参数移位及正则点差分已通过 32 项独立审核和 678 绑定。显式 F/S 矩阵与逆像行式已通过作者编译及 34 项类型/值/公理记录，独立审核通过 32 检查及 517 绑定，20 次 Lean 执行及一次运行时检查成功。五形式输出和无限和的参数运输仍待完成，各环节证据见 [构造链交接](formalization/COEFFICIENT_ROUTE.md)。

原根及其链接 theorem 的公开请求已经处理；mission 容器回读仍为 `private`，
发布提案处于管理员审核流程。排队和审核均以保存的远端回读为准。

本地保留正式陈述镜像，其中 Open 目标的 `sorry` 是待证占位；完整已接受 solution 与
待证陈述分开存放。平台状态以远端回读为准，书面命题仍须忠实形式化。

## 如何接续

先读 [最新报告](research/progress-2026-10-02.md)，选择一条明确路线和它的下一项输入。
研究原格时重点是最短方向的不固定出口；研究增长维数 Gram 时先控制完整分母；
研究八重零点级数时先处理真实边界、符号和解析率。

公开源码、精确证书和解压后复跑说明放在
[research-2026-10-02 资料包](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02)，
平台首页和讨论区提供同一入口。公开申请及管理员审核状态见
[发布交接](publication/2026-10-02/README.md)。

原连接系统的独立平台审核已通过 47 检查及 940 绑定，定义及三条精确定理声明均已 Published，三份完整证明已 Accepted、公开 Proved 并链接。通用实际分子 PF 的作者审核通过 24 检查及 188 绑定，[独审](verification/formalization-coefficient-map-numerator-pf-independent-2026-10-04/independent-review.json) 已通过 32 检查及 388 绑定，26 次真实 Lean 加运行时成功；真实 chosen P/q 清分子运输已通过 [16 检查及 282 绑定的作者审核](verification/formalization-coefficient-map-formal-transport-numerators-2026-10-04/author-audit.json)，覆盖全部 n≥1。九阶局部数组、B/ρ、Gamma 的运输仍需 Lean 证明，[530 项精确检查与离线契约](research/coefficient-map-local-transport-design-2026-10-04.md) 已准备，有限检查尚不构成证明。

显式 Matrix 的平台作者移植已通过 33 检查及 1543 绑定，七个精确模块通过 3831-job 正式任务构建；独立平台审核已冻结 PASS，49 检查及 3488 绑定全部由 Root 重哈希，84 次 Lean 加运行时成功。定义作业最近保存回读为 PENDING，尚无 Matrix 证明验收。原偶数 n≥2 条件保持，整数乘子与分母高度仍未证明。
