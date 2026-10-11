# 补充：原任务的两个 35 步 milestone

用户在 21 步主目标完成后追加要求清掉任务原有两个 milestone。本次直接证明它们已关联的
原定理，不替换声明、不创建重复 milestone。

## 35 步获胜策略

目标 `OAI.SnakyConditional.snaky_winning_strategy_with_legal_states`
（`ba8a045d-4e6e-478a-8e05-4c1527165825`）。

由已经完成的 `CanForce 21 ∅ ∅` 增加预算至 35，再应用已证明的通用策略抽取。
增加预算的归纳保留同一个新鲜首步；已经获胜时继续在无限棋盘选择新鲜格子，目标仍保留。
所得策略只有剩余步数与当前双方集合三个输入，恰好产生 35 次实际 Maker 落子。

`SnakyConditional` 与 `SnakyPrototype` 有各自命名的定义。证明通过对回合数归纳，
识别两套 `playState`；逐一检查八个方向并以函数外延性识别放置函数，再运输目标与合法性。
原始定义均未修改。只要求前 34 次 Breaker 应答合法，第 35 次仍不受约束。

提交适配源码为 `platform/milestone35-proof.lean`，实际闭合版本为
`Solutions/SnakyMilestones/Strategy35.lean`。后者导入实际 21 步证明，已确认只依赖
`propext`、`Classical.choice`、`Quot.sound`。

## 原 35 步证书的有限恒等式

目标 `OAI.SnakyCertificate.certificate_correct`
（`c5e790f7-904e-40dd-a7f5-ba72d31e941b`）。此目标检验旧证书数据，不是 21 步结果的逻辑推论。

平台原 `Def_SnakyCertificate` 含 6 张基础卡片与 610 行非基础数据，总计 1,837 个放置项。
Python 独立重建全部行，产生候选所需集合、包络和高度。Lean 对每行核对原数组查找，
将 `rowAt` 展开一次，改写已验证子行，再分别以内核归约检查三个字段。
逐字段检查绕开派生结构判定实例的等式运输障碍；不采用计算预言机。

全部 616 行还逐项检查所需集合包含于包络、原点在包络内而不在所需集合内、高度不超过 34。
另检验表长、行索引、非空放置项及严格向后引用。四个出口的所需单格、包络大小、高度和
被排除区域逐项验证，最后合成为原目标的七项合取。

实际源码拆成 `Lookup35.lean`、逐行小组、`Certificate35Part00..22.lean` 与最终 `Certificate35.lean`。
八行小组遇到服务器时限后，未证明部分继续拆为四行子项，超时组拆为两行子项；
原小组和大组仅汇总子项投影。已发布的声明与候选数据保持原样。
候选数据在 `Definitions/Def_Snaky35Cache*.lean`，逐个字面量的哈希保存在
`platform/milestone35-manifest.json`。实际源码导入真实支撑证明；平台适配源码通过已证明目标的
合取投影取得同一行等式与性质，最后证明原声明。

用户报告电脑卡死后，停止本地 Lean/Lake，只进行低占用 Python 生成和 API 操作。
查找引理与前 12 行已通过本地内核探针；其余完整证书由平台端分块核验。
本次不宣称补充证书已完整本地构建或公理审计。最终验证以平台 `ACCEPTED` 和
`verification/milestones-report.json` 为准。原 21 步主证明的完整本地构建与标准公理审计保留。

## 记录与恢复

- `verification/milestones-before.json`、`milestone-history-*.json`：追加工作开始时的原目标与历史。
- `verification/milestone-target-*.json`、`milestone-definition-*.json`：平台原声明与原定义。
- `verification/milestones-progress.json`、`milestones-remote*-*.log`：平台端验证进度。
- `verification/milestones-after.json`、`milestones-report.json`：完成时的平台状态及账号归属。

当前唯一入口为 `remote_queue_milestones.py`，最多四个依赖已满足的小项在服务器排队。
已生成模块不可重新生成覆盖。`check_milestones.py`、`finish_milestones.py` 已加资源禁用检查。
发布仍采用任务内直接 HTTPS 设置 `SNAKY21_DIRECT_API=1`。确认现有进程退出后才能恢复，
避免并发写入 `platform/journal.json`。原 21 步完成报告与闭合证明保留。
