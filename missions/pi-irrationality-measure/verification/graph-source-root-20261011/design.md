# 原源三父项主根归约

本 stage 保留平台主根 `e717eef2-11b1-4b14-9789-65f52c0502e1` 和 campaign 原定义。归约直接使用以下三个原源公开声明，不另造同义 wrapper：

| 原源声明 | 模块 | 实际 AST 字节区间 | 原源行 |
|---|---|---|---|
| `OAI.PiExponent.DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate` | `Approximation.DeterminantContradiction` | 8308:9062 | 167–180 |
| `OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation` | `Approximation.AdmissibleMatrixGeometry` | 1945:2155 | 41–44 |
| `OAI.PiExponent.LiteralAnalytic.analyticAggregate` | `Analysis.AnalyticAggregate` | 4686:4986 | 96–101 |

源码 commit 为 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。完整 source/port 哈希、AST、实际 scope、声明图、原始命令字节和精确 metadata 均在 `preparation.json` 和 `source/` 中保留。

`Main.pi_eventual_lower_bound`（193:347，8–9 行）调用 `piEventualLowerBound_of_globalInterpolation`；后者的原始命令在 `InterpolationConsequence`（227:520，9–13 行）。本归约仅把 Main 的几何参数代入后者证明中的唯一 `hgeometry`：

```lean
theorem solution : PiEventualLowerBound :=
  DeterminantContradiction.piEventualLowerBound_of_interpolation_and_analytic_aggregate
    AdmissibleMatrixInterpolation.globalInterpolation LiteralAnalytic.analyticAggregate
```

三项父目标是 Open：它们的 `sorry` 仅用于平台参考声明/OLean，不是完成的源证明。root sketch 本身无 `sorry`，但导入 Open 父项，因此实际公理检查明确允许并要求 `sorryAx`。这属于 graph reduction，不是闭合主根证明。

参考声明只导入 canonical `ApproximationDefinitions` 和已 Published、完整源值核对通过的 `DeterminantContradiction_CoreData`；Mathlib 和其余已 Published 源数据包由该真实依赖闭包提供。不存在 `FixedDeterminantFamily`、`FormalInterpolationPackets`、`AnalyticRemainder` 社区 adapters 的 import。

预检严格顺序共六项：三个 reference emitters；一份 original 三项+Main 的组合 type/Std3 snapshot；一份 generated 三项+同一 root solution 的组合 type/Open snapshot；精确提交 root wire 的独立 modecheck。每项 whole-file 上限为 300 秒。命令见 `compile-commands.txt`。纯消费者为 `scripts/certify_source_root_graph_existing.py`，它不能运行 Lean/API。

权威 exactName 只读查询记录 `verification/source-root-exact-name-lookup-20261011T131753_707821Z.json` 显示三项均为零匹配。既有历史 graph 中较短的 cofinal/scalar 路线依赖被排除的社区接口，不能作为此原源归约的替代。已有 campaign→Main→本根的归约可保留；本次只需在既有本根添加这三项真实源义务。最终 graph 是否接入，以根操作者上传后的实际 graph/decomposition GET 为准。
