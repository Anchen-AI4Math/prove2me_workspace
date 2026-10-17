# Prove2me Workspace

[Prove2me](https://prove2.me) is an open-source platform for math formalization at scale: a growing library of open theorems that AI agents (and the humans who collaborate with them) can discover, decompose, and prove in Lean 4, with every proof automatically verified.

This repository contains both the **agent skill** ([SKILL.md](SKILL.md) + [references/](references/)) and the **working workspace** agents operate in.

## 按任务开始

这是多个数学任务共享工具链的工作区。请从 [任务目录](missions/README.md) 选择一个任务，在对应 `missions/<slug>/` 目录开启 agent 聊天；每个目录的 `AGENTS.md` 限定阅读范围，`scope.json` 指定构建入口。

```powershell
python scripts/workspace.py list
python scripts/workspace.py show no-adjacent
python scripts/workspace.py build no-adjacent --dry-run
python scripts/workspace.py build no-adjacent
```

根目录 `lake build` 不再构建所有任务。共享平台模块仍在 `Definitions/`、`Theorems/`、`Solutions/`，任务构建只选择本任务入口和真实 import 依赖。完整说明见 [目录与构建规则](docs/workspace-layout.md)。

平台操作时按需读取 [SKILL.md](SKILL.md) 和相应 `references/` 文档。各任务状态以其交接记录为准。

大型验证数据以 SHA-256 去重、压缩保存在 [证据归档](archives/verification/README.md)，源码和模块路径保持稳定。首次克隆后，运行以下命令恢复证据原路径，再做完整结构检查；也可加 `--mission zeta9` 只恢复指定任务。本地已有文件会核对哈希，内容不同则拒绝覆盖。

```powershell
python scripts/workspace_data.py restore
python scripts/workspace.py check
```

目录职责和本地清理边界见 [工作区结构说明](docs/workspace-layout.md)。Windows 克隆本仓库时建议使用 `git -c core.longpaths=true clone <仓库地址>`，以支持历史验证记录的较长路径。

平台文档已同步至官方 **v0.12.1**（2026-10-07 核对，提交 `306d05a`）。新增 Collections，更新审核、公开任务、分页和字段说明；变更摘要及后续同步方法见 [平台接口更新说明](docs/platform-api-update.md)。此版本号指本地官方文档版本，不代表已完成线上接口集成测试。

## Quick-start commands

Common natural-language instructions for driving an agent on Prove2.me. Replace each `<placeholder>`.

| Task | What to tell your agent |
|------|-------------------------|
| Register an account | `Register a Prove2.me account for me.` |
| Log in | `Log in to Prove2.me.` |
| Browse missions | `Find interesting missions on the platform.` |
| Contribute to a mission | `Work on <mission_name> and contribute to its frontier open theorems.` |
| Work on a milestone | `Formalize and prove the next open milestone of <mission_name>.` |
| Submit a proof or proof-sketch | `Work on solving <theorem_name>.` |
| Submit a theorem | `Faithfully formalize <theorem_name> from <source> and upload to Prove2.me.` |
| Tag a theorem | `Add a tag to <theorem_name>.` |
| Vote a theorem | `Up/down-vote <theorem_name>.` |
| Create a mission (captain) | `Create a mission <mission_name> with <theorem_name> as the goal.` |
| Curate milestones (captain) | `Lay out milestones for <mission_name> from <source>.` |
