# Snaky 21 步任务：完成

核对日期：2026-10-09。平台原主目标 **Proved**，本次主证明提交 **ACCEPTED**。

- 任务：https://prove2.me/missions/Snaky_in_21_Maker_moves
- 主定理：`OAI.SnakyPrototype.snaky_winning_strategy_21_with_legal_states`
- theorem_id：`29b16242-e6c3-4ee3-b459-3e4a883b9dcc`
- submission_id：`5fb089ef-41bf-4a86-90c1-efafb0d05f92`
- 贡献账号：`Yuxuan Xu`，user_id `418b0711-62a5-416a-ba5d-876ae8758fe3`；已实时核对 ACCEPTED 记录。
- 固定论文提交：`adc7f1241b42e322a6451854ab7e4b4c146bf78a`
- Lean 4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`

## 核验

`python scripts/workspace.py build snaky-21` 通过。实际闭合证明的公理依赖仅为
`Classical.choice, Quot.sound, propext`；没有 `sorryAx` 或计算预言机公理。
原证书 SHA256 与固定源一致，两套重建逐卡一致。所有 728 张编号卡片及 898 个嵌套组合的
三字段等式经 kernel 检查；最终所需集合为空、高度 21、包络 251 格且包含于指定 17×17 方格。
目录数量与全部高度界另行验证。策略合法于所有有限输入，且不要求第 21 次 Breaker 应答合法。

平台贡献沿组合规则、放置/基础演算、编号卡片块、最终证书和策略抽取连接到原主目标。
上层较大卡片块分成小组，适应服务器编译时限。

工作区结构检查没有新增错误；原有两个 five-primes 未归属文件未改动。

## 文件

- 闭合本地主定理：`Solutions/Snaky21/Main.lean`
- 数学说明：`missions/snaky-21/proof-explanation-zh.md`
- 构建与公理日志：`verification/closed-build.log`
- 完成报告：`verification/final-report.json`
- 实时平台快照：`verification/final-platform.json`
- 提交明细：`platform/journal.json`
- 正式主目标提交源码：`platform/main-proof.lean`

`Theorems/Thm_OAI_Snaky21*.lean` 为平台接口镜像中的占位声明，不能用于独立完成性审计。
上述闭合本地证明使用实际 Solutions 证明模块。

## 用户追加：原有两个 milestone

2026-10-09 追加清理原 35 步路线的两个 milestone。35 步策略主张已于本次获得
`ACCEPTED`，submission_id `dfe524a3-32ee-4d27-98e9-b20dabb3ea8b`。
原 616 行证书的有限恒等式正在执行平台端分块内核检查。
进度见 `verification/milestones-progress.json`，当前日志路径见 `verification/milestones-runner.json`。
详细数学与交接说明见 `milestones-explanation-zh.md`。

资源约束更新：用户随后报告电脑卡死，已禁用本任务的本地 Lean/Lake 检查器。
当前入口为 `remote_queue_milestones.py`，只运行低占用 API 客户端，以平台端分块验证
剩余有限证书。已完成的 21 步结果及 35 步 ACCEPTED 记录保留。
生成后的 `platform/milestone35-manifest.json` 与已发布模块必须复用，不能重新运行生成器覆盖。
当前运行记录见 `verification/milestones-runner.json`；不要重复启动发布器。
原证书 0–43 号行已获得 ACCEPTED，0–31 号大组汇总也通过。24–31 号八行检查遇到服务器 300 秒超时，
拆为四项两行检查后全部通过；其他尚未证明的八行组拆为四行检查。已发布的声明和数据不变，
旧组通过投影汇总这些小项。空闲远端队列会预先验证后续声明，所有队列共用四个 API 工作者。
没有重启本地 Lean/Lake；本机 API 客户端实测约 36 MB。
当前客户端允许服务器超时的小组继续拆分至单行；只处理明确的服务器时限错误，其他失败保留记录供检查。
资源快照见 `verification/resource-incident-resolution.json`。剩余里程碑尚未完成，不能将已接受小项当成整个证书通过。
