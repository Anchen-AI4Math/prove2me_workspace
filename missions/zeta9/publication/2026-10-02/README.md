# 原 ζ(9) mission 的公开交接

**实际执行结果（2026-10-02 20:24，Asia/Shanghai）：** 首页、17 条研究里程碑与交接讨论
已同步并回读通过；资料包已公开上传并核对服务端 SHA-256；公开申请已提交，16 个目标及
关联定理均为 `public`。Mission 当前仍为 `private`，proposal 为 `In review`，等待平台管理员
审核后进入公共目录。ζ(9) 主目标仍为 `Open`。详见 [发布结果](RESULT.md)。

用户于 2026-10-02 决定将已有私有任务公开。
本次更新的对象是 [Irrationality of ζ(9): weighted lattice route](https://prove2.me/missions/Irrationality_of_%CE%B6%289%29%3A_weighted_lattice_route)，
mission ID `8195d8fe-059f-4515-92b4-57b585e2bac6`；不另建 mission。
正式目标 `523f37b8-ae98-406c-a3f7-43aa8e002dd7` 仍为 `Open`。

## 整理后的资料

- [任务入口](../../README.md)、[公开总览](../../PUBLIC_OVERVIEW.md)：当前状态与接续路线。
- [公开首页](mission-description.md)：按当前数学进展重写原 mission 描述。
- [资料交接讨论](mission-comment.md)：最新五项研究成果、复跑方法和未解决输入。
- [里程碑状态审阅](milestone-state-review.json)：区分书面完成与正式 Lean 完成。
- [source-manifest.json](source-manifest.json)：公开源码包的逐文件 SHA-256。
- [reproduction-report.json](reproduction-report.json)：独立解压后的五组验证回放。
- [源码与证书资料包](https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02)：
  沿用该任务已有公开资料仓库，在 mission 首页与讨论中提供入口。

本地文件路径和共享 Lean 模块路径保持稳定。没有删除旧证明或历史证书，也没有上传整个
多任务工作区。公开包包含当前研究及实际依赖，不包含认证凭证、缓存或第三方论文原件。

## 平台流程与回读

平台版本已回查为 `0.11.6`，同版本的官方 API 文档保存在 `api-docs/`。
`GET /missions/:id` 不是此版本的读取接口；脚本从 mission 列表按固定 UUID 精确选中。

1. `snapshot`：读取原描述、44 条里程碑、正式目标、图与讨论，仅保存该任务快照。
2. `sync`：更新 mission 描述、已审阅的未链接研究里程碑，并发布资料交接讨论；逐项回读。
3. `release`：调用原 mission 的 `make-public`，再读取 mission、proposal、目标和里程碑。

```powershell
python scripts/publish_mission_2026_10_02.py snapshot
python scripts/publish_mission_2026_10_02.py sync
python scripts/publish_mission_2026_10_02.py release
```

命令从 `missions/zeta9` 目录执行。`sync`、`release` 是平台写操作，用户本次已明确授权。
脚本仅读取已有凭证用于 `https://prove2.me/api/v1`，不会打印或打包凭证。
不会把已有 linked theorem 替换成未形式化的书面命题。

公开端点会立即发布关联目标、已链接里程碑和其依赖，**mission 进入公共目录仍需管理员审核**。
因此 `release_requested_at` 已设置而 `visibility=private`、proposal 为 `In review` 时，
准确状态是“公开申请已提交，关联定理已公开，mission 等待审核”，不是请求失败。

最新实际执行结果以 `sync-receipt.json`、`release-response.json`、
`platform-after/mission.json` 与 `platform-after/proposal.json` 为准；历史 `Private`
回执保留原日期。发布不更改根定理的数学证明状态。

本次整理没有新增 Lean 证明或执行实际 Lean 构建。书面研究、有限精确证书、平台正式验证
在所有公开入口中分开记录。
