# Prove2Me 0.12.2 上传接口审查（2026-10-08）

## 结论与证据边界

2026-10-08 的 `/agent/refresh` 响应由本任务主流程实测为 `version=0.12.2`；本审查没有读取凭证或再次调用认证接口。公开的 [官方 `main/SKILL.md`](https://raw.githubusercontent.com/prove2me/prove2me_workspace/main/SKILL.md) 在本日读取时仍标 `0.12.1`，与本地根目录 `SKILL.md` 一致。尝试访问 `v0.12.2` 标签、GitHub API 和比较页未取得可核验的版本差异：本机代理 `127.0.0.1:65532` 拒绝连接，直连 DNS 不通，网页抓取无该标签/比较页可用内容。因此 **不能声称 0.12.2 与 0.12.1 的发布和验证接口完全兼容**，也不能记录不存在的 0.12.2 commit 或文件哈希。下面“接口符合”只表示符合目前可读的官方 `main` 文档（其版本为 0.12.1），不是 0.12.2 的发布前兼容性证明。

官方当前文档：[贡献 API](https://raw.githubusercontent.com/prove2me/prove2me_workspace/main/references/contribute.md)、[证明与环境](https://raw.githubusercontent.com/prove2me/prove2me_workspace/main/references/prove.md)、[完整项目上传](https://raw.githubusercontent.com/prove2me/prove2me_workspace/main/references/upload_full_project.md)。本地同步基线见根目录 `docs/platform-api-update.md`：官方 0.12.1 commit `306d05a0ea8b56a544810f270685b421f2775820`。这些官方页面是当日只读查看，未存成带 SHA 的 0.12.2 镜像。

## 与 `scripts/publish_independent_node.py` 的接口对照

| 操作 | 公开文档约定 | 当前脚本 | 判断 |
| --- | --- | --- | --- |
| `POST /submit-problem` | JSON `problems` 数组；`env` 为顶层 Mathlib revision；成功 `202`，逐项 `jobs[].job_id`，还可能有 `errors[]`。 | 发送单项数组和固定 `env=0df444a360eaa60ab8c11dca51a86af692955474`。 | 请求形状符合 0.12.1 文档；需严格检验 `202`、`errors=[]`、一个匹配 name 的 job。 |
| 发布轮询 | `GET /publish-jobs/:job_id`；只有 `PUBLISHED` 带可用 `theorem_id`，`FAILED`/`ERROR` 为终态。 | 轮询并在 `PUBLISHED` 时保存 ID。 | 基本符合；获取 ID 后需独立读取最终 theorem。 |
| `POST /verify` | `multipart/form-data`：`theorem_id`、`file`、可选 `proof_type=prove` 与 `explanation`；响应 `submission_id`，再 `GET /verify?submission_id=...`。证明使用目标 theorem 所属环境，`/verify` 无 `env` 字段。 | 发送上述字段和文件，随后轮询。 | 请求形状符合 0.12.1 文档；需严格检验响应状态、ID 和目标回读。 |
| 环境/查重 | 名称只在同一环境唯一；`GET /theorems` 可带 `env`；既有 theorem 与新建 theorem 均有 `mathlib_rev`。公共证明只能导入同环境公共声明。 | 按无 `env` 的 `q` 查询最多 100 条，仅比较 `formal_statement` 与 `preamble`。 | **不够安全**：可能漏掉同名异环境记录、误复用，或受分页/可见性影响。 |
| 不可变内容 | 已上传 theorem 的名称/声明不可变；提交的 `solution.lean`、`proof_type` 和判定状态不可修改（仅 explanation 可更新）。 | 有本地 SHA/验证门，但没有发布后对全部关键字段回读；`metadata.json` 未绑定哈希。 | **不够安全**：应在任何不可变 POST 前完成精确字节与元数据审查。 |

## 必须补的发布前门槛

1. **0.12.2 文档差异门槛**：获取官方可定位的 0.12.2 commit/tag（若尚未公开，记录官方文档与部署版本不一致），逐项比对 `SKILL.md`、`references/contribute.md`、`references/prove.md`、`references/upload_full_project.md`。在确认接口前禁止批量发布。不要更新共享 Lean/Mathlib pin。
2. **精确身份门槛**：每个节点按 `theorem_name + env` 查询，处理分页/精确匹配，并核实 `mathlib_rev`、`visibility`、`formal_statement`、`preamble`。已记录 `theorem_id` 的节点同样重新 `GET /theorems/:id` 核对。若已存在但内容或环境不同，停止该节点，不复用、不再次 POST。公开节点依赖须全部为同环境公共声明且已发布。
3. **不可变文本门槛**：发布前固定并哈希 **实际请求的** `theorem_name`、`preamble`、`formal_statement`、`env`、`private/visibility`、`source`、`theorem_title`、`natural_language_statement`、`tags` 以及 proof 文件；确认 source/citation、元数据和声明准确。脚本当前只固定 statement/source/solution 文件 SHA，未校验 `metadata.json` 和最终 JSON payload；`preflights` 也应要求非空。保留每节点 ≤300 秒完整文件预检、内核类型相等与公理审计。
4. **异步结果门槛**：仅在 `HTTP 202`、`errors=[]`、恰好一个与请求 theorem name 对应的 job 时接受新发布。`PUBLISHED` 后用 theorem ID 回读声明、preamble、环境、可见性及名称，再开始 `/verify`。`FAILED`、`ERROR`、`429` 和网络中断保留原请求证据；不盲重试。已有 `publish_intent` 但缺 job ID 时先用只读 publish-jobs 列表及精确 theorem 查询人工对账。
5. **验证结果门槛**：`POST /verify` 仅接受文档所述异步提交响应与明确 `submission_id`；校验提交关联的 theorem ID。轮询至终态，区分 `ACCEPTED`、`SKETCH_ACCEPTED` 与失败；`SKETCH_ACCEPTED` 只证明归约，不说明开放子引理已完成。若 `verify_intent` 已记录却缺 submission ID，先只读查询本人 submissions 对账，不重复 POST。
6. **版本与目标门槛**：发布当刻重新读 `/environments`、现有目标 theorem/graph/open-leaves；保持目标 `mathlib_rev=0df444a360eaa60ab8c11dca51a86af692955474`，只向当前开放且需要的节点提交。平台提案保持 Draft，按任务 `AGENTS.md` 由用户在网站逐项审核。

## 本轮操作

只读查看本地脚本和官方公开文档；没有读凭证，没有执行平台 POST、Lean 或构建，也没有修改共享根目录。因 0.12.2 官方版本树无法取得，未生成 `platform/api-0.12.2/` 的伪快照。本审查不表示上传已经就绪。
