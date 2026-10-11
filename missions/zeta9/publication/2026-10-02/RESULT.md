# ζ(9) 项目整理与公开申请结果

本次沿用用户指定的 [原 mission](https://prove2.me/missions/Irrationality_of_%CE%B6%289%29%3A_weighted_lattice_route)，
mission ID `8195d8fe-059f-4515-92b4-57b585e2bac6`。

## 已完成

- 整理任务入口、研究总览、路线状态与可复现资料，保留原源码、共享 Lean 模块路径和历史证书。
- 更新原 mission 首页、17 条未链接研究里程碑说明及资料交接讨论，逐项回读通过。
- 发布 [2026-10-02 资料包](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02)，
  共 305 个文件、7,756,223 字节；独立解压后最新五组验证均通过，源码和原证书逐字节一致。
- 提交原 mission 的公开申请，并逐个核实主目标与 15 个关联定理的 `visibility=public`。

ZIP 的 SHA-256 为
`68a821653ae08e4f0b2917c770215dfbe60af2670ea3cb6a87521f75b665f2a0`，
与 GitHub 服务端记录一致。下载入口已写入 mission 首页和交接讨论。

## 实际平台状态

公开申请时间：`2026-10-02T12:23:27.360235+00:00`（北京时间 20:23:27）。

| 项目 | 回读状态 |
| --- | --- |
| Mission 可见性 | `private`，公开申请已提交 |
| Proposal | `In review`，等待平台管理员审核 |
| 主目标及关联定理 | 16 个均为 `public` |
| ζ(9) 无理性主目标 | `Open` |
| 里程碑 | 44 条，15 个定理链接，13 条完成 |

发布前快照记录 12 条完成；发布后回读中，已有的 “Zudilin's four-value disjunction”
从 `Open` 变为 `Proved`，当前完成数为 13。公开首页按该实时状态修正。资料包内的早先
快照与历史记录保留原值，不能据此推断 ζ(9) 本身已有证明。

Mission 进入公共目录仍需要平台管理员批准；本次 API 请求已经成功。所有新研究仍按
书面证明、有限精确验证和 Lean 形式化分别标记，没有把未形式化研究标为正式完成。

## 验证与回执

- [平台同步回执](sync-receipt.json)、[首页统计修正回执](description-final-receipt.json)。
- [公开请求响应](release-response.json)、[16 个定理可见性审计](release-audit.json)。
- [最终 mission 快照](platform-after/mission.json)、[审核状态快照](platform-after/proposal.json)。
- [GitHub 服务端发布记录](github-release.json)、[源码清单](source-manifest.json)、
  [独立复跑记录](reproduction-report.json)。
- 路线图检查通过：41 个节点、13 个规约、5 个冻结有限案例；主目标仍未解决。

本次没有新增 Lean 证明，也没有执行新的 Lean 构建。全工作区归属检查发现其他任务中
两个预先存在的无归属文件，记录在 [检查日志](workspace-check.log)；本任务新增文件已登记。
