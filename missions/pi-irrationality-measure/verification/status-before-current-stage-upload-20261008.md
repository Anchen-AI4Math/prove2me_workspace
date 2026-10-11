# π 无理性度 campaign

更新：2026-10-08（Asia/Shanghai）。历史交接完整保留于 `verification/status-history-before-20261008.md`。

## 当前结论

本轮实时复查：平台根仍 Open，frontier 已从三个适配叶子继续拆到九项，完整列表以 platform/current-open-leaves.json 为准。三份 canonical 定义的精确正文已保存于 platform/canonical-definitions，复用证书仍待内核/AST核对。性能审计确认 stock Lean 无跨独立模块 frontend 环境缓存；实测单 Lean 占约3.2GiB、机器内存余量很小，保持串行并优先打通源证明到根的路径。详见 verification/stage2-performance-audit.md。

固定 OpenAI source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`，原始 source 与 SHA-256 清单保持不变。完整兼容移植已在共享 Lean 4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` 环境构建成功，未改共享版本。原完整上界 2、源 Main 与平台 `PiIrrationality.UpperBound (2 : ℝ)` 的本地桥接已通过标准三项公理审计。最新完整构建证据：`verification/latest-build.json`，对应 `build-20261007-204658.log`，exit 0，161.08 秒。

这不是平台 campaign 完成。2026-10-08 实时 API 确认根 `406736ed-98ce-4177-b97f-24de96ba4188` / `PiIrrationality.openai_bound_two` 仍 Open。当前三个开放叶子见 `platform/current-open-leaves.json`：

- `443b7bc2-5366-4875-969c-729f392f870d`，`FormalInterpolation.eventual_packet_degree_reduction`。
- `77135f94-b700-497a-9598-1304d5238120`，`FormalInterpolation.unbounded_packet_interpolation`。
- `aa1f9e5b-ad85-494d-a859-5b0ff5a5e36b`，`DeterminantContradiction.actual_truncated_log_entry_low_index_exp_bound`。

它们是社区适配接口，不能按同名源定理直接引用。优先研究 unbounded_packet_interpolation 与 AffineJetPackets 的有限点形式插值桥接；逐 entry 的解析上界需独立审计，源 determinant summand 上界并非同一命题。

## 已上传和本轮可上传阶段

`matrix_det_norm_le_prod_row_sum` 已在平台 Proved，证明 submission `d30ccb26-f468-4672-a1a8-2d43368d468f` 的服务端 verdict ACCEPTED；本轮已实时回读。证据：`platform/det-row-sum-submission.json` 与 `platform/current-det-row-sum.json`。

本轮新增独立阶段 `OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le`。由权威 AST 机械生成，项目内依赖闭包只有自身，外部 import 闭包齐全。声明、上传证明、源类型快照与生成类型快照均严格预检 exit 0；四项最长 61.26 秒，上传证明自身 36.60 秒。内核类型逐项相等，上传证明公理只有 `propext`, `Classical.choice`, `Quot.sound`。精确源码、元数据、manifest、validation 位于 `verification/independent/OAI_PiExponent_DeterminantAnalyticBound_log_norm_sum_le/`。

首个上传请求在执行前被自动审批拒绝，要求具体 payload 与目的地授权。用户随后明确答复“授权该节点及上述完整内容上传并验证”，审批通过后才执行；授权记录为 `platform/log-norm-sum-authorization.json`。已发布 theorem `10a08e49-5f89-4055-a254-59882a447190`，proof submission `47177dbc-2588-4b46-a504-378c9b473eb9` 已 **ACCEPTED**，目标回读 **Proved**。完整幂等记录见此 stage 的 `publication.json`；无重复 POST。

下一独立阶段 `OAI.PiExponent.tendsto_nat_add_one_div_pow` 已完成四项严格预检，最长 56.22 秒；内核类型相等且只有标准公理。它尚未上传，元数据与具体发布仍待后续安排。两份已验证 Sol 已加入 scope 的正式 build roots（现在共 12 项）；预览包不加入正式构建。

## 元数据与机械生成

Stage 1 真实声明图已验证。Stage 2 全量串行提取已恢复，最新观察完成 787/875 个不可变输入模块，live session **6219**。四项 AST 索引最后刷新于 706 模块，零 unmatched，最终规划前需再次刷新。已完成提取均严格 300 秒内，源未变；本轮补齐 SimplexRationalWeights 100.18 秒、SimplexUnweighted 71.01 秒。全部事实完成前不冻结完整生成方案。

当前暂定图：514 个 definition bundle、286 个 node，两 DAG 无环；含 292 个 instance 根，886 个源声明待 Stage 2。`verification/platform-unit-plan-preview.json` 与 `platform-artifact-plan-preview.json` 明确 `ready_for_generation=false`。六个 campaign 逼近定义的复用已通过独立内核及 AST/作用域审计，记录 `platform/definition-reuse-candidates.json` 与两份 definition-reuse validation；消费者仍须类型对照。

独立生成/校验/上传脚本已补强：固定 actual snapshot/core/source/graph/facts/runtime hashes；重建 exact snapshot 文本；检查四份严格编译证书、log SHA 和类型 JSON；上传按指定环境分页查重、回读不可变目标及 Proved 状态，保存完整请求意图和 payload hashes。平台实测版本 0.12.2，公开官方文档仍 0.12.1；差异调查边界见 `platform/api-0.12.2-review.md`，共享文档与工具链未改。

`scripts/generate_platform_bundles.py` 已实现机械裁剪并生成四个纯 Python 预览样本，其中两个保留 local instance；未编译、未声称可提交。FiniteCoverCohomology 中 `simp only` 对 `:= rfl` 引理的词法依赖被最终内核 proof 消去，不能仅由 kernel graph 裁剪；生成器已增加狭窄的完整 rfl 辅助命令保留，并记录实际 AST ref 与已闭合依赖。此预览仍待 Lean 与类型审计。审计记录见 `verification/independent-generator-audit.md`。

匿名 private local instance `ReesProductSchemeChart:1847` 的常量出现在公开 theorem 的 typeDeps，必须给稳定公开名字并保留 local 行为。新增 `scripts/rename_anonymous_instance.py` 使用权威 instance binding ref 的 token.end 插入名字、删除 privateTok、按同文件 binding identity 改词法引用；没有修改 oracle 或原证明。样本双向字节重建及四种拒绝情况通过，未 Lean/type 验证；生成器已集成；整个 ReesProductSchemeChart 包仍因传递导入事实未齐备而拒绝预览。记录见 anonymous-instance-audit/rename-validation。

仍需完整提取、其余 private 同名/引用恢复、正式 Def/Sol 生成与逐项 ≤300 秒编译/内核类型对照，随后按叶到根上传并接入既有目标。所有提案保持 Draft，交由用户网站审核提交。

进一步 canonical 审计见 `verification/canonical-reuse-frontier-audit.json`：Statement 六定义之外，现有社区 FixedDeterminantFamily 已使用原 FixedData/Row/Column 等全名。若消费者同时导入 canonical 与新源 bundle，会重名；尚缺其完整定义正文与独立内核/AST证据，不能直接认定可复用。FormalInterpolationPackets 是适配接口，其名字不直接出现在原源中；AnalyticRemainder 的解析全名也需正文快照。完整源证明接入与社区适配叶子的接入应各自检查实际 imports，避免无意混入两套同名定义。


共享 lakefile 新增无关 Snaky21 库注册后，旧提取进程85538在778文件开始前由配置保护终止。核对并重建旧配置原始字节SHA完全相同，Lean/Mathlib/executable/去重有序搜索路径均未改变；详见 verification/lakefile-change-audit.json。旧runtime和777提取证据保留，新runtime重新捕获，恢复session6219。提取脚本补强了早期失败判定，避免把上一成功文件的latest-record误关联到失败输入。

上传主线已明确为 platform/upload-route.json：仅选择原pi_eventual_lower_bound作为源root，再接已有UpperBound转换；不需要求解社区九个适配leaf。仅复用已验证六定义，三个已存在但导入canonical FixedFamily的公共辅助theorem计划同namespace _source017重命名，其绑定/ref/type验证待做。源/port原件保持不变。
## 恢复入口

先读 `verification/run-state.json`，只轮询实际存在的 live session；若 handle 已失效，用只读进程检查确认是否仍在运行，不能重复启动 Lean。全量提取 live **6219** 继续运行，单 Lean；不要再轮询 68135、54888、80025。workspace check session 52537 已 exit 1，只有两个既有 TaoFivePrimes 未归属 Solutions。

构建：在根运行 `python scripts/workspace.py build pi-irrationality-measure`。新增任务文件被当前 scope 通配范围覆盖；运行 workspace check，只处理本任务归属问题。两个既有 TaoFivePrimes 未归属 Solutions 仍留给所属任务。

平台：https://prove2.me/campaigns/pi-irrationality-measure

来源：https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/017.md
