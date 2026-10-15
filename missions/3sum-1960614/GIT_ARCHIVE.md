# Git 归档边界（2026-10-15）

本任务的原生 Lean 源码、平台 Definitions/Theorems/Solutions、转换与发布脚本、最终清单、ACCEPTED 回执、任务完成记录和完整依赖图审计结果纳入工作区 Git。当前状态入口仍是 `status.md` 与 `verification/mission-completion.json`。

以下文件保持本地原位，不删除，也不作为普通 Git 对象重复提交：

- 重复的机器图完整响应，以及已由最终审计报告记录路径和哈希的 frontier 图快照。
- 大型原生/公开接口提取结果、类型探针输出和可再生成的索引。
- 导入、宏、证明转换的中间源码备份和已废弃的平台暂存副本。
- 嵌套的 `submission-bigospeedrun/` Git 检出；它有自己的公开仓库和固定提交，不作为未配置的 gitlink 加入本仓库。

排除项由根目录 `.gitignore` 的 3SUM 专用规则精确约束，完整文件路径、大小与 SHA-256 见 `verification/git-local-artifacts.json`。该清单是本次 Git 整理时的本地字节快照，不会改写原有平台验收记录。其余任务仍按既有忽略规则提交当前状态。

完整图审计保存在 `verification/machine-graph-check.json`；主目标与桥接目标的关键图响应、四条被有界图视图省略的边的 decomposition 响应仍在 Git 中。因为其余完整图响应留在本地，单独克隆此仓库不能读取所有历史原始图快照。

正式 Big O 源码：

- 仓库：<https://github.com/Anchen0823/three-sum-1960614>
- 固定提交：`8c25c0325de5be4286413f39ca0c9278aad33f52`
- 本地成果归档：`D:\users\self_projects\math_discovery\3 SUM\results\2026-10-15_1p960614`

math_discovery 保存了固定提交的 693 个文件、官方验证 artifact、1003 个平台提交源文件的 ZIP，以及归档校验脚本。这里的 Git 整理不重新运行 Lean，不把未完成的其他研究任务标记为已证明。
