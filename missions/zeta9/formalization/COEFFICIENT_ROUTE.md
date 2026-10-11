# 原系数构造的形式化交接

## 2026-10-07 当前平台目标与最新本地阶段

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

[Current platform readback](platform/readback-2026-10-07/user-submission-current-57/progress-audit.json), [PF acceptance](platform/coefficient-map-numerator-pf/publications-for-new-mission-2026-10-07/publication-audit.json), [Scoped task build](platform/coefficient-map-numerator-pf/publications-for-new-mission-2026-10-07/root-scoped-build/actual-build-receipt.json), [Parameter author Root rehash](../verification/formalization-project-handoff-2026-10-07/root-parameter-author-complete-binding-rehash.json), [Phase author Root rehash](../verification/formalization-project-handoff-2026-10-07/root-phase-author-complete-binding-rehash.json).

[Uniform analytic SOURCE handoff](../research/analytic-weighted-uniform-source-delta-2026-10-07.md).

## 以下保留 2026-10-04 构造链快照

本页记录 `p=9,q=1,m=n,d=0` 的实际构造链。原偶数 `n≥2` 的有理四次乘子 F 双射和精确求和已通过独立 Lean 审核；J 与 ζ(9) 无理性仍未证明。
平台数量以各批次 receipt 和最新 API 审计为准；以下是 2026-10-04 Asia/Shanghai 的工作快照。
最新 [平台 v0.11.8 审计](platform/readback-2026-10-04/p51-final/progress-audit.json) 确认 51 份完整证明全部 Accepted、公开 Proved 并链接；原 mission 为 95 条里程碑、66 条 theorem 链接、64 条完成项，包含 Telescoper、KernelBridge 与 Connection 九份新证明，主目标仍 Open。

| 环节 | 真实源码与范围 | 已完成验证 | 平台状态 |
|---|---|---|---|
| 最高极点系数 | [CoefficientMap](CoefficientMap.lean)：实际有限产品清极点、最高系数整数公式、W 的真实乘子 | 原源与正式任务构建；独立数学及 37 项移植审核 | 三条证明 Accepted/public Proved，已链接 |
| 全部九阶局部系数 | [CoefficientMapJet](CoefficientMapJet.lean)：实际单位分母逆及形式级数的全部卷积 | 原源与正式任务构建；独立数学及 45 项移植审核 | 三条证明 Accepted/public Proved，已链接 |
| 完整局部数组单射 | [CoefficientMapInjectivity](CoefficientMapInjectivity.lean)：strict proper 域内实际 `(n+1)×9` 数组单射 | 原源、16 项独立数学审核、正式任务构建及 57 项移植复核 | 三条证明 Accepted/public Proved，已链接 |
| 真实全局部分分式 | [CoefficientMapPartialFractions](CoefficientMapPartialFractions.lean)：实际系数双和的多项式身份和正则有理点身份 | 原源、39 项类型审计、16 项独立数学审核、正式任务构建及 27 项独立移植复核 | 三份完整证明 Accepted/public Proved，已链接 |
| 反射与消去 | [CoefficientMapReflection](CoefficientMapReflection.lean)：偶 n 的偶阶总和为零；加强次数界下简单极点总和为零 | 原源、40 项类型审计、17 项独立数学审核、正式任务构建及 35 项独立移植复核，383 哈希绑定 | 三完整证明 Accepted/public Proved，已链接 |
| 实际有限求和 | [CoefficientMapFiniteSum](CoefficientMapFiniteSum.lean)：真实 H 移位差、B/ρ/尾项身份 | 原源、17 项类型审计、15 项独立数学审核及正式任务构建；完整平台作者批次 29 项检查、37 项独立移植复核、446 哈希绑定通过 | 三完整证明 Accepted/public Proved，已链接；奇数阶桥显式保留实际消去输入 |
| 实际无限 L | [CoefficientMapSummation](CoefficientMapSummation.lean)：用真实反射解除消去输入，证明调和极限、移位尾消失、实际绝对可和及 HasSum/tsum | 全源、31 项类型审计、16 项独立数学审核及正式任务构建通过；平台作者 25 检查、301 定义比较、273 证明记录通过；38 独立移植检查、547 哈希绑定通过 | 定义及三定理 PUBLISHED，三完整证明 Accepted/public Proved，已链接 |
| 原五维聚合 F 的线性结构 | [CoefficientMapAggregate](CoefficientMapAggregate.lean)：真实 `(B,ρ₃,ρ₅,ρ₇,ρ₉)`、四次乘子的五个坐标与恢复 | 全源、32 项作者审计及 15 项独立数学审核通过；平台作者 35 检查、3803-job 正式任务构建、44 项独立移植复核及 771 哈希绑定通过 | 定义及三定理 PUBLISHED，三完整证明 Accepted/public Proved，已链接；核与逆见后续桥 |
| 实际累计差分与分子商 | [CoefficientMapTelescoper](CoefficientMapTelescoper.lean)：真实累计系数、正负零点、实际分子及根多项式整除与商次数界 | 原生 16 项独立审核、150 哈希绑定；平台作者 40 检查及 49 次实际执行通过，3810-job 构建成功；独立移植 36 检查、1535 哈希绑定、75 次 Lean 执行及一次运行时版本检查通过 | 定义及三条精确定理 Published；三份完整证明 Accepted、公开 Proved、已链接 |
| 实际移位算子的次数障碍 | [CoefficientMapShiftDegree](CoefficientMapShiftDegree.lean)：真实 A/B、次高系数与低次数强制 H=0 | 全源、22 项作者审计及 16 项独立审核通过，54 哈希绑定；完整平台作者 24 检查、3796-job 正式任务构建、30 项独立移植复核及 317 哈希绑定通过 | 定义及三定理 PUBLISHED，三完整证明 Accepted/public Proved，已链接 |
| 原五维 F 核与逆映射 | [CoefficientMapKernelBridge](CoefficientMapKernelBridge.lean)：真实差分桥、原偶数 n≥2 有理四次核为零、F 双射与唯一原像；指定目标的真实 HasSum 与绝对可和 | 原生 37 项作者审计及 22 项独立审核通过，296 哈希绑定；平台作者 52 检查及 57 次实际 Lean 执行通过，3817-job 正式任务构建成功；38 项独立移植检查、1381 绑定及 88 次实际 Lean 成功 | 作者、Root 与独审已冻结；定义及三条声明 Published，三份完整证明已 Accepted、公开 Proved 并链接；整数逆像、高度分母、J 与无理性仍 Open |
| n→n+2 连接系统 | [CoefficientMapConnection](CoefficientMapConnection.lean)：原 D/H/v 齐次核、15 维双射及五个原右端的唯一解 | 完整冻结版本真实原生构建退出 0；39 类型、12 作者边界及 23 作者检查通过；独立审核 28 检查、108 绑定及 6 次最终 Lean 执行成功，仅标准三公理 | 原生独审 PASS；平台作者 33 检查、372 绑定及 3824-job 正式构建通过，独立移植 47 检查及 940 绑定通过，43 次 Lean 加一次运行时成功；定义及三条精确声明 Published，三份完整证明已 Accepted、公开 Proved 并链接，实际正则点差分见 ParameterShift，五形式输出运输另待证明 |
| 原 F 显式矩阵与选择行式 | [CoefficientMapMatrix](CoefficientMapMatrix.lean)：按实际五输出定义 F；选择矩阵 S 与 (b,a)S F⁻¹ | 原生作者整源编译成功，22 条声明及 12 条端点记录通过；作者冻结 9 检查、44 绑定；独立审核 32 检查、517 绑定及 20 次 Lean 执行成功 | 原生独审 PASS，平台作者 33 检查及 1543 绑定、80 次 Lean 加运行时通过，3831-job Root 构建成功；平台独审冻结 PASS：49 检查及 3488 绑定均由 Root 重哈希，84 次 Lean 加运行时通过；定义最近保存回读 PENDING，尚无证明验收；整数输出的乘子仍定义在有理数上 |
| 真实 R 的参数移位与连接差分 | [CoefficientMapParameterShift](CoefficientMapParameterShift.lean)：实际有限产品推得 R_(n+2)(t−1)D=cZ(u)R_n(t)，原完整连接方程给出真实有理函数差分 | 完整作者编译及类型审计退出 0；作者冻结绑定 59 项文件及 20 条标准三公理报告；独立原生审核通过 32 检查及 678 绑定 | 尚未平台移植；保留实际正则点条件与 n≥1，五个形式坐标运输及 HasSum 参数运输另待衔接 |
| 通用实际分子 PF | [NumeratorPartialFractions](CoefficientMapNumeratorPartialFractions.lean)：任意严格真分子及真实局部展开的多项式/有理 PF | 原生作者 24 检查、188 绑定，9 次 Lean 成功，1 次历史边界失败保留排除 | 独审 32 检查及 388 绑定、26 次 Lean 加运行时通过，一次原别名失败保留排除，尚未平台移植 |
| 真实选定分子运输 | [FormalTransportNumerators](CoefficientMapFormalTransportNumerators.lean)：n≥1 的实际 chosen P/q 清分子运输、真实 Q(2)=0 | 15 段完整证明两次整源编译退出 0；作者 16 检查及 282 绑定、六完整类型内核核对和 17 实际解析通过，二历史控制失败保留排除 | 独审冻结 PASS：35 检查及 595 绑定，Root 全量重哈希；17 源、389 完整声明、11 边界及 19 自有解析通过；仍需完整五输出组装 |
| 全实际 jet 与九阶 rho 运输候选 | [FormalTransportJets](CoefficientMapFormalTransportJets.lean)：26 段完整候选，保留 n≥1、左右极点和最右负余项 | 原准备与共享 b081 保持；[私有修正版](../verification/formalization-coefficient-map-formal-transport-jets-author-2026-10-04/JetsVerifiedSource.lean) ccef 整文件编译成功，26 完整陈述不变，19 个真实模块及 15 个闭边界通过 | 原生作者审核冻结 PASS：21 检查及 439 绑定均由 Root 重哈希，26 完整内核类型比较、15 边界及 23 自有解析通过；独审纯准备，B 常数项及 Gamma 矩阵组装另待完成 |

关键边界不能合并：strict proper 是 `2n+2degW < 9(n+1)`，只给 O(1/t)。
加强次数界是 `2n+2degW <= 9(n+1)-2`，用于简单极点消去。真实边界 `n=0,W=X⁴`
满足前者、违反后者，实际函数为 `1/t`，`rho_1=1`，有限和为 `H_T^(1)`。
独立 Lean 审核保留了这个反例。

连接扩展用偶次 t 系数（0 至 28）表示 15 维输出，原稿用 u 系数（0 至 14）；两种表示由上三角、对角线全为 1 的转换对应，矩阵条目并不相同。独立离线对照的 39 项精确符号检查与最终 Lean 独立审核分别保留。所有新连接主结论保留 n≥1；n=0 的自然数减法截断定义不同于原稿的 t(t−1)，真正书面 n=0 系统有非零核 P=0、q=v⁹，此边界已由独立 Lean 控制复验。真实 R 的有限产品比值及正则点连接差分已通过 ParameterShift 作者编译与独立审核；五个形式坐标和无限和的参数运输仍需单独证明。

完整局部数组保留每个极点及阶数；原 F 只保留 B 与四个奇阶总系数。
前者单射不能直接推出后者可逆。无限 L 还需要真实收敛论证；仅有实数部分和极限，
不能在没有实际可和证明时直接宣称 Lean `HasSum` 或 `tsum` 身份。

现在真实 telescoper、根多项式整除及商次数界给出实际移位多项式关系。
移位算子的真实次高系数为 `(7n-2-degH)*leadingCoeff(H)`，由次数障碍迫使 H=0，
再推出原四次乘子 W=0。有限维线性代数由此给出实际 F 的双射，没有把行列式、核或逆映射当作输入。
任意有理五维目标都有唯一有理四次原像；纯 ζ(9) 目标也有非零有理原像。
原 DAG 的 Z9.F 也量化全部偶数 n≥2；round7/research/connection.md §1 的真实 R_n、u 与
(B,A₃,A₅,A₇,A₉) 输出顺序和本链一致。给定整数 (b,a) 时，目标向量 (b,0,0,0,a)
属于这些有理目标；其乘子仍是有理多项式。显式行矩阵表示已通过原生作者编译与独立审核；五形式输出的 n→n+2 运输和分母高度另待形式化。
这还没有给出整数乘子、有效分母高度或趋零的非零整数形式。
完整证据见 [KernelBridge 独立审核](../verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04/independent-review.json)。
当前 KernelBridge 正式任务构建见 [Root 冻结](../verification/formalization-coefficient-map-kernel-root-preflight-2026-10-04/root-build-freeze.json)；ParameterShift 作者范围与源码绑定见 [作者冻结](../verification/formalization-coefficient-map-parameter-shift-2026-10-04/author-audit.json)，完整 [参数移位独审](../verification/formalization-coefficient-map-parameter-shift-independent-2026-10-04/independent-review.json)、[矩阵作者冻结](../verification/formalization-coefficient-map-matrix-2026-10-04/author-audit.json) 与 [KernelBridge 移植独审](platform/coefficient-map-kernel-bridge/independent/independent-integration-review.json) 分别保留各自阶段证据。

作者冻结源码、请求和审核记录保持不变。共享模块只从已核对的 staged 字节安装，
构建入口只登记正式 `Solutions`，不把任务内 native 源路径当作根 lake 目标。
既有作业继续用原 ID 查询，避免重复发布；新的 theorem 只在 Accepted/Proved 回读后补链。

五输出运输的 [设计](../research/coefficient-map-formal-transport-design-2026-10-04.md) 与 [纯数学独立审阅](../research/coefficient-map-formal-transport-independent-review-2026-10-04.md) 已完成；作者 168 项与独立重建的 360 项有限精确检查分别保留。独审给出直接清分母整多项式身份，并核对全部九阶 rho、B 边界及 Gamma 左乘方向。这些设计和有限证书尚不替代运输定理的 Lean 编译；真实 choice、Gamma 行恢复、余项分子零值及次数基础已完成作者编译及 [24 检查、192 绑定](../verification/formalization-coefficient-map-formal-transport-bounds-2026-10-04/author-audit.json)，20 个新基础定理只依赖标准三公理；作者历史一次失败保留并排除。通用分子 PF 已通过作者编译和 32 检查/388 绑定的独审；完整运输仍待证明。
