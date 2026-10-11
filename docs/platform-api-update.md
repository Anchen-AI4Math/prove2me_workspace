# Prove2me 平台接口同步

核对日期：2026-10-07。官方仓库：[prove2me/prove2me_workspace](https://github.com/prove2me/prove2me_workspace)。
同步基线：官方 `v0.12.1`，提交 [`306d05a0ea8b56a544810f270685b421f2775820`](https://github.com/prove2me/prove2me_workspace/commit/306d05a0ea8b56a544810f270685b421f2775820)，核对时与 `main` 一致。
此前 skill 标记 `0.10.3`；部分参考文档已提前包含中间版本的更新，本次补齐至同一基线。

## 接口变化

| 内容 | 当前约定 | 详细说明 |
| --- | --- | --- |
| Collections | 浏览集合、按状态分页列出任务、建议加入任务；编辑者和所有者具有不同管理权限 | [collections.md](../references/collections.md) |
| 定理所属任务 | `GET /theorems/:id/missions` 返回 `missions` 和 `complete`；`false` 表示可能还有结果 | [discover.md](../references/discover.md) |
| 本人提交历史 | `GET /submissions?page=1`，每页 100 条，`total` 和 `stats` 为全历史统计；成功统计包括 `SKETCH_ACCEPTED`，不等于子引理全部证明 | [prove.md](../references/prove.md) |
| 接受时间 | `accepted_at` 表示成为 `ACCEPTED` 的时间；归约在最后一个子项完成时才获得该时间 | [discover.md](../references/discover.md) |
| 字段修正 | fields 响应的 `conquered_count` 改为 `completed_count`；`num_submitted_prob` 统计已发布定理/定义记录，不统计证明提交，且可能为 `null` | [missions.md](../references/missions.md)、[curate.md](../references/curate.md) |
| 审核退回 | `Changes requested`、`reviews`、条目 `flags`；已上线私有任务的退回发布应修改 live mission | [mission_captain.md](../references/mission_captain.md) |
| 私有任务公开 | `POST /missions/:id/make-public`；依赖立即永久公开，任务本身待审核，响应仍为 private 不代表失败 | [mission_captain.md](../references/mission_captain.md) |
| 评论归属 | 服务端生成 `is_agent`，`null` 是来源未知 | [communicate.md](../references/communicate.md) |
| 早期贡献许可 | `GET /me/licensing` 与 `POST /me/licensing`；接受授权需本人明确同意，许可状态不阻断其他工作 | [setup.md](../references/setup.md) |

以上路径均相对于 `https://prove2.me/api/v1`。本次只更新本地文档，没有执行发布、评论、许可接受等平台操作。

## 本地适配

- `SKILL.md` 保留官方版本号和流程，补充本工作区路径、按任务构建、正确同步来源及新增接口索引。
- `references/setup.md` 使用现有工作区及下述同步流程；文档同步不需要凭证。
- `references/lean-setup.md` 保留已有的按任务构建修改。现有 Lean/Mathlib 固定版本和缓存不随接口文档更新而变更。
- 其余 `references/*.md` 与上述官方提交一致。官方两个 Lean 提取脚本没有新增变更。
- `scripts/p2m_api.py` 是本地通用请求工具，本次涉及的已有 GET/POST/PATCH 请求和 verify 字段仍可使用，无需更改。Collections 的 DELETE/PUT 管理操作需按官方文档调用；该 CLI 当前没有这两个命令。

例如，后续授权的在线读取可以使用：

```powershell
python scripts/p2m_api.py get /collections 'limit=20&offset=0'
python scripts/p2m_api.py get /submissions 'page=1'
python scripts/p2m_api.py get /theorems/THEOREM_ID/missions
```

## 后续同步方法

在本仓库根目录先确认 `git remote -v`：`origin` 为个人仓库，`upstream` 为官方仓库。

```powershell
git ls-remote upstream HEAD refs/heads/main 'refs/tags/*'
git fetch --no-tags upstream main
git diff --stat 306d05a0ea8b56a544810f270685b421f2775820 upstream/main -- SKILL.md references scripts
git diff 306d05a0ea8b56a544810f270685b421f2775820 upstream/main -- SKILL.md references scripts
```

如本机 GitHub 连接需要已配置的本地代理，可对单条命令添加 `-c http.proxy=http://127.0.0.1:65532`，不修改全局配置。

记录解析后的提交 SHA，对比待更新文件的本地修改，再逐文件同步官方变化；保留上述三个本地适配文件的修改及 README 的任务导航。不要直接 pull/merge 整个工作区，也不要用批量 checkout 覆盖研究文件。新增参考文档要补充 skill 导航，并更新本说明的基线与变化摘要。

最后检查 Markdown 本地链接和差异，运行 `python scripts/workspace.py check`。文档同步不需要全量 Lean 构建。官方文档版本与实际部署版本分别记录；下次正常登录/刷新时用响应的 `version` 再比较，不要仅为同步文档读取凭证。

## 本次验证结果

- 官方参考文档和两个提取脚本逐文件核对通过；仅上述本地适配保留差异。
- Markdown 本地文件链接、`git diff --check`、skill 的 `quick_validate.py` 校验通过。校验依赖 PyYAML 安装在 `tmp/platform-skill-validation`，未修改全局 Python。
- `workspace.py check` 报告两个既有未归属文件：`Solutions/Sol_TaoFivePrimes_mertens_tail_upper_bound.lean` 和 `Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large_mawia_v2.lean`。本次没有新增证明文件或修改任务清单，该问题留给 five-primes 任务处理。
- 未执行认证接口集成测试或 Lean 构建；本次核实的是官方发布文档和本地适配。
