# ζ(9) 无理性研究：任务入口

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

## 以下保留 2026-10-04 交接快照

截至 2026-10-04，**ζ(9) 无理性目标仍未完成**。
本目录包含交叉审阅的书面研究证明、可复跑的有限精确证书，以及已编译的完整 Lean 引理。
近期新研究已有十一条核心证明、四条 PNT 终点及三十九条实际系数、连接及矩阵桥引理通过正式任务构建；
PNT 的完整证明另在真实依赖环境独立核验，完整研究尚未全部形式化。
五十一份证明已获平台验收并链接原 mission，包含真实最高极点、局部系数、完整数组单射性、全局部分分式、实际反射消去、有限及无限求和、移位次数障碍、五维聚合线性结构、C3 全偶数系数非零性、
无条件调和分母渐近率及九阶双倍索引的率 18。

2026-10-04 UTC 平台 v0.11.8 查验及验收补链：95 条里程碑、66 个 theorem 链接、64 条完成项；
51 份完整证明 Accepted、公开 Proved 并链接，见 [实时审计](formalization/platform/readback-2026-10-04/p51-final/progress-audit.json)。Telescoper、KernelBridge 与 Connection 九份新证明已完成验收和补链，公开申请仍在审核。
最新审计记录的 51 份完整证明全部 Accepted；历史提交队列保留原始状态。

平台任务：[Irrationality of ζ(9): weighted lattice route](https://prove2.me/missions/Irrationality_of_%CE%B6%289%29%3A_weighted_lattice_route)。
目标定理是 `ZetaNine.irrational_zeta_nine`，远端 2026-10-04 回读为 `Open`。
公开资料包：[research-2026-10-02](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02)。
新增 [C3/PNT 完整源码包](https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/zeta9-advanced-proofs-2026-10-02.zip)
已公开并核对远端 SHA-256；其 [独立审核](https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/ADVANCED-PROOFS-INDEPENDENT-REVIEW.json)
补全了原清单遗漏的八个 import 闭包记录，实际源码与构建完整。
源码包与三份具名审核附件已在 [2026-10-04 远端核验](publication/2026-10-02/advanced-proofs/live-readback-2026-10-04.json) 中再次确认字节数与 SHA-256 一致。

正在形式化原 F 的实际构造：最高极点、全部九阶局部卷积、完整数组单射性、全局部分分式、反射消去、有限及无限求和、移位次数障碍与五维聚合线性结构的二十七条证明已获平台验收。
完整局部数组的单射性、真实全局部分分式、反射消去与有限求和桥梁均已通过独立数学审核。
原 `p=9,m=n,d=0` 的无限 L 身份已本地完整编译，并通过 16 项独立数学审核；
原偶数 `n≥2` 的五维聚合 F 双射、有理四次逆像和指定 L 的实际绝对求和，
已通过 22 项独立审核及 296 个哈希绑定，完整平台作者移植、正式任务构建及 38 项独立平台审核也已通过，定义及三条声明已 Published，三份完整证明已 Accepted、公开 Proved 并链接。
真实 R 的参数移位与正则点连接差分已通过 32 项独立原生审核；显式 F/S 矩阵及逆像行式已通过作者编译及 32 项独立审核、517 个绑定。
连接系统独立平台审核通过 47 检查及 940 绑定，定义及三条声明 Published，三份完整证明已 Accepted、公开 Proved 并链接。通用分子 PF 的作者审核通过 24 检查及 188 绑定、独审通过 32 检查及 388 绑定；真实分子运输的作者审核已通过 16 检查及 282 绑定，独审已通过 35 检查及 595 绑定并由 Root 全量重哈希。五形式输出及无限和的参数运输、整数逆像、分母高度和 J 仍未封闭，见
[形式化进度](formalization/README.md)。

## 从哪里开始

| 目的 | 入口 |
|---|---|
| 了解当前成果和真正未解问题 | [公开总览](PUBLIC_OVERVIEW.md) |
| 核对原 F 构造、求和和逆映射的最新形式化 | [构造链交接](formalization/COEFFICIENT_ROUTE.md) |
| 看最新一轮数学推进 | [2026-10-02 研究报告](research/progress-2026-10-02.md) |
| 接续研究和核对文件范围 | [status.md](status.md)、[scope.json](scope.json)、[AGENTS.md](AGENTS.md) |
| 审阅最新证明及证据边界 | [独立复核](research/continuation-review-2026-10-02.md) |
| 重跑最新五组精确验证 | [验证入口](verification/continuation-2026-10-02/README.md) |
| 查看原路线细节和历史结构 | [roadmap/DAG.md](roadmap/DAG.md)、[roadmap/dag.json](roadmap/dag.json) |
| 核对平台上传与公开流程 | [publication/2026-10-02](publication/2026-10-02/README.md) |
| 查看新证明、发布队列与剩余形式化义务 | [formalization](formalization/README.md) |

旧日期报告保留当时的判断。旧 DAG、平台交接和 `Private` 记录中的历史状态不能覆盖
当前 `status.md`、公开总览与远端回读；数学已写证也不自动使平台里程碑 `completed=true`。

## 目录与验证

`research/` 放证明和说明，`scripts/` 放验证程序，`verification/` 放参数证书，
`roadmap/` 放原研究 DAG 和历史平台归约，`publication/` 放此次公开交接与资料包，
`formalization/` 放当前 Lean 证明、审核和可恢复的发布记录。
本次通过入口和清单整理项目，保留源码路径以保证 imports、引用和证书哈希稳定。

在多任务工作区根目录导航和检查：

```powershell
python scripts/workspace.py files zeta9
python scripts/workspace.py build zeta9 --dry-run
python scripts/workspace.py check
```

实际正式构建使用 `python scripts/workspace.py build zeta9`；五十六个登记入口包含五十四份新完整 solution，最新 Matrix 移植已通过 3831-job 构建，其中五十一份已平台验收。
最新正式构建及矩阵三份新 solution 的公理输出见 [构建记录](formalization/platform/coefficient-map-matrix/task-build.log)，对应 [冻结记录](verification/formalization-coefficient-map-matrix-root-preflight-2026-10-04/root-build-freeze.json)。原连接系统的 3824-job 冻结完整保留。原五维核与逆映射的 3817-job 历史冻结完整保留。
四份 PNT solution 也已通过新的任务构建；共享平台目录中的 MediumPNT 陈述镜像
用于类型集成，因此该构建包含 `sorryAx`。相同提交源码在完整真实 PNT 环境的独立
编译只有标准三项公理，证据见 [PNT 审核](formalization/platform/pnt/independent-integration-review.json)。
根目录空目标构建不能验证本任务；也不应运行全部 `Solutions`。
最新归属检查仅剩其他任务的两个已有无归属文件，本任务新增成果已登记。

公开包内提供自己的重跑说明与环境锁定。平台正式目标、Open 子义务和 Lean 的 `sorry`
陈述镜像属于待证内容；它们与完整证明文件有明确区分。
