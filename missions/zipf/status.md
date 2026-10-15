# Zipf 分布

2026-10-11 开始执行。

- 平台任务：`9d7a43ac-2157-449b-a0b5-93d1d19ef7c2`。
- 主定理：`ZipfLaw.zipf_infinite_extension`，ID `3db55d74-324f-4340-aed9-9dbf6411b23f`。
- 主定理的服务端提交 `ea6667a1-468b-4d8c-8882-353d2a61d5ec` 已为 `ACCEPTED`。
- 归一化里程碑的提交 `b5c77b72-539f-4b29-a290-7b35bcaf37d8` 已为 `ACCEPTED`。
- 平台原始定义、陈述和接口响应保存在 `verification/`。
- 构建命令：`python scripts/workspace.py build zipf`。

本次续作已完成主定理与 12 个里程碑的本地精确类型审计：
`verification/audit.log` 中 13 个 `solution` 均仅依赖
`propext`、`Classical.choice`、`Quot.sound`，不依赖 `sorryAx`。

13 个证明已附数学解释提交服务端，全部为 `ACCEPTED`。
标准任务构建已通过原始证明及新增图证书，日志见 `verification/final-graph-build.log`。
完整 ID、源码 SHA-256 和当前判定见
`verification/submissions.json`，判定原始响应保存在 `verification/verdict-*.json`。

Benford 首位数字极限证明已写入
`Solutions/Sol_ZipfLaw_zipf_one_leadingDigit_benford.lean`，已编译并获 `ACCEPTED`。
方法为十进制区间分块、Euler–Mascheroni 误差抵消、Cesàro 平均，最后对任意
截断位置做单调夹逼。

平台版本已实时核对为 0.12.4。官方 `v0.12.4` 的证明接口与本地 0.12.1
文档一致，核对证据见 `verification/api-version-check.json`。
随后按用户要求更新共享 `SKILL.md` 与 `references/proof_graph.md`，加入图交付要求。

## 依赖图交付

主定理直接证明接受后，线上 graph 曾只有主目标和定义两个节点。
已发布并证明 5 个可复用声明，并为原目标补交 8 个实际引用子声明的归约，位于 `graph/`。
13 个新证明文件已全部通过闭合精确类型审计，没有 `sorryAx`，见
`verification/graph-audit-summary.json`。13 个新提交也全部获服务端 `ACCEPTED`，
ID、源码哈希与判定见 `verification/graph-submissions.json`。

2026-10-11 已回读 18 个相关定理的 graph 和 decompositions：所有定理为 `Proved`，
17 条预期依赖关系全部核对通过。线上采用“子定理 → 归约节点 → 父定理”路径；
每条路径的实际边、节点 ID、归约提交 ID 与判定证据见
`verification/graph-summary.json`，原始响应见 `verification/graph-graph-*.json`
及 `verification/graph-decompositions-*.json`。没有待验证的图提交。

主定理的图归约提交为 `864ba4aa-33c5-4a50-8698-4eb1a78c4b18`。
无限扩展已拆为收敛判据、ζ 极限和发散；有限分布连接 CDF、归一化、
一般矩、均值、方差、秩比、对数关系、众数和熵之间的实际依赖。
Zipf–Mandelbrot、Yule–Simon、monkey typing 和 Benford 保留为独立里程碑根。
关系说明及依赖简图见 [graph/README.md](graph/README.md)。

`Solutions/ZipfLaw/GraphCertificate.lean` 是这些声明的独立闭合镜像，
不导入原始参考文件中的占位符。证书已登记到任务 `scope.json`。
复现图审计：`python missions/zipf/scripts/graph.py audit`。
服务端图核对：`python missions/zipf/scripts/graph.py snapshot`。
标准构建已包含上述闭合证书；工作区结构检查也已通过，日志见
`verification/final-workspace-check.log`。

首次同时编译多个 legacy 模块时出现 Mathlib `.olean.private` 读取失败。
逐项构建可正常完成，并发现及修正草稿的同名辅助引理冲突、熵求和括号和方差
数值转换错误。使用 `python missions/zipf/scripts/build.py --workers 1` 预热当前
任务的目标后，再运行标准任务构建。不要重新并发加载整个 Mathlib 到大量进程。
