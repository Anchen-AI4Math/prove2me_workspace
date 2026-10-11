# Proved provider promotion audit（799-module preview）

本目录是冻结 `platform-unit-plan-preview.json` / `platform-artifact-plan-preview.json`
的独立变体，不修改原 799 计划、Accepted 文件、publisher 或 generator。生成命令：

```powershell
python scripts/plan_platform_units_providers.py --frozen-preview --variant both
```

脚本先重新调用现有 `make_plan` 与 `build_artifacts`，逐字段确认结果等于冻结计划；
再独立重算 84 个公共 inline 碰撞节点。promotion 以 AST whole-command unit 为原子，沿
`direct_unit_dependencies` 取完整传递闭包。普通 definition command 归入 `definition`，
其余 theorem proof command 归入 `definition_embedded`。变体 Definitions 依赖不得逃逸到
theorem stub，并重新检查 Definitions / Node 两个 DAG。

## 三个 statement helper 的最低修复

实际源名是：

- `OAI.PiExponent.FormalLogTruncation.logTail_constantCoeff`（并非用户速记中的
  `FormalLogJet.logTail_constantCoeff`）；
- `OAI.PiExponent.GeneralCartierDegreeLength.finite_zeroIdeal_of_mono`；
- `OAI.PiExponent.primeRectangular_maps_maximal`。

三者出现在四个公开 consumer statement 的 `typeDeps`，也都出现在 `valueDeps`。根命令
proof 最长 7 行；完整闭包含 181 个命令，其中 169 个已在 Definitions，实际新增 12 个
proved theorem commands（总 proof 86 行、最长 29 行），新增保留源码 7,423 bytes。
`finite_zeroIdeal_of_mono` 的 proof closure 会把 EulerSupportDimension 的两个既有 theorem
nodes 吸收到 Definitions，因此 nodes 从 312 变为 310。最大 Definitions bundle 总保留
命令仍是 52,660 bytes；最大单 bundle 增量 4,812 bytes。这个修复只解决 statement provider
正确性，公共 inline collision nodes 仍为 84。

逐 provider 的原命令 UTF-8、byte range、command SHA、port/original source SHA、graph
type/value/constructor interface、statement facts SHA 和 closure 都在
`minimum/providers/*.json`。`minimum/closure-command-index.jsonl` 为 181 个闭包命令逐行记录
source SHA、command SHA、范围、类别变化和直接依赖。

## 全部共享公共 inline provider

326 个共享名字来自 325 个原子命令、138 个 source modules；唯一的一对是同一
`@[reassoc]` 命令生成的 `affinePresentation_comp` 与
`affinePresentation_comp_assoc`，脚本保持整个命令。所有根 proof 都不超过 10 行。

完整闭包含 2,492 个命令；其中 581 个相对冻结计划新进入 Definitions（580 theorem proofs
以及 1 definition command），新增 384,623 source bytes、61 个 Definitions bundles，并吸收
108 个既有 nodes。闭包引入 125 个 proof 超过 10 行的依赖，其中 4 个超过 40 行，最长
66 行；这正是不能只根据 326 个短 helper 估算编译时间的原因。尽管如此，最大 bundle
总保留命令仍为 52,660 bytes，最大单 bundle 增量为 11,748 bytes；node source-component
最大值从 69 降到 57，p95 从 10 降到 6；inline-unit 最大值从 186 降到 147，p95 从 28
降到 22；84 个碰撞节点降到 0。

新闭包含 9 个 source-module-local private proof commands；4 条新跨模块边指向冻结计划中
已经 deprivate 的 providers，未产生新的 unresolved private rename。所有 326 个 provider
名字保留原公共名字，无 pending root proof-name remap。

## 边界与最终接入

这些结果只证明 Python 规划不变量。没有运行 Lean，没有生成/编译 bundle，也没有证明任一
文件满足 300 秒预算；preview 不能作为 final source certificate 或发布证据。全量方案的
384 KB 总增量和 11.7 KB 最大 bundle 增量支持优先试验它，但 580 个新增 proof commands、
4 个长 proof dependency 仍要求真实分 bundle 预检。

875 个 module facts 完成并冻结 final plans 后，接入顺序应为：

1. 用 final inventory/graph 重建 final base unit/artifact plans并再次逐字段比较；
2. 在 final base 上重跑相同 promotion closure，重新生成 provider manifests 与 command index；
3. 先生成全共享方案的 Definitions bundles，按 DAG leaves-first 逐文件运行不超过 300 秒的
   Lean preflight；任何超时只按 source-module DAG 拆 bundle，不改变命令正文或闭包；
4. 对每个公共 provider 比较 generated/source theorem type，对真正 definition 同时比较
   value，并做 Std3 / axioms 审计；
5. 再重建剩余 node plans，确认 collision=0、private inline reject=0、所有 consumer type
   仍匹配，之后才可把 reviewed variant 合入 final plan。

机器可读总表是 `provider-promotion-comparison.json`。所有 manifest 均明确
`preview_only=true`、`lean_validated=false`、`publish_ready=false`。
