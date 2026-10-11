# ζ(9) 无理性研究：任务入口

截至 2026-10-02，**ζ(9) 无理性目标仍未完成**。
本目录包含交叉审阅的书面研究证明、可复跑的有限精确证书，以及部分抽象 Lean 引理。
近期的新研究尚未 Lean 形式化；有限小值不代替无限趋零证明。

平台任务：[Irrationality of ζ(9): weighted lattice route](https://prove2.me/missions/Irrationality_of_%CE%B6%289%29%3A_weighted_lattice_route)。
目标定理是 `ZetaNine.irrational_zeta_nine`，远端 2026-10-02 回读为 `Open`。
公开资料包：[research-2026-10-02](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02)。

## 从哪里开始

| 目的 | 入口 |
|---|---|
| 了解当前成果和真正未解问题 | [公开总览](PUBLIC_OVERVIEW.md) |
| 看最新一轮数学推进 | [2026-10-02 研究报告](research/progress-2026-10-02.md) |
| 接续研究和核对文件范围 | [status.md](status.md)、[scope.json](scope.json)、[AGENTS.md](AGENTS.md) |
| 审阅最新证明及证据边界 | [独立复核](research/continuation-review-2026-10-02.md) |
| 重跑最新五组精确验证 | [验证入口](verification/continuation-2026-10-02/README.md) |
| 查看原路线细节和历史结构 | [roadmap/DAG.md](roadmap/DAG.md)、[roadmap/dag.json](roadmap/dag.json) |
| 核对平台上传与公开流程 | [publication/2026-10-02](publication/2026-10-02/README.md) |

旧日期报告保留当时的判断。旧 DAG、平台交接和 `Private` 记录中的历史状态不能覆盖
当前 `status.md`、公开总览与远端回读；数学已写证也不自动使平台里程碑 `completed=true`。

## 目录与验证

`research/` 放证明和说明，`scripts/` 放验证程序，`verification/` 放参数证书，
`roadmap/` 放原研究 DAG 和历史平台归约，`publication/` 放此次公开交接与资料包。
本次通过入口和清单整理项目，保留源码路径以保证 imports、引用和证书哈希稳定。

在多任务工作区根目录导航和检查：

```powershell
python scripts/workspace.py files zeta9
python scripts/workspace.py build zeta9 --dry-run
python scripts/workspace.py check
```

实际正式构建使用 `python scripts/workspace.py build zeta9`；本轮仅核对范围，未执行 Lean。
根目录空目标构建不能验证本任务；也不应运行全部 `Solutions`。
2026-10-02 的归属检查仅剩其他任务的两个已有无归属文件，本任务新增成果已登记。

公开包内提供自己的重跑说明与环境锁定。平台正式目标、Open 子义务和 Lean 的 `sorry`
陈述镜像属于待证内容；它们与完整证明文件有明确区分。
