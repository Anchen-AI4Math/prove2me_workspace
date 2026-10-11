# Zeta(9) irrationality research

此目录是任务 `zeta9` 的 agent 入口。只处理用户当前指定的任务。

1. 首先阅读本目录 `status.md` 和 `scope.json`。论文入口在清单的 `papers` 字段，按需阅读，不要预读全部 PDF。
2. 从仓库根目录运行 `python scripts/workspace.py files zeta9`，只读取所列源码和当前修改实际需要的 import 依赖。不要预读其他任务、全局历史、`.workbuddy/memory/` 或发布归档。
3. 构建：根目录运行 `python scripts/workspace.py build zeta9`；如果终端位于本目录，运行 `python ../../scripts/workspace.py build zeta9`。先加 `--dry-run` 可以检查范围。
4. `scope.json` 的 `build` 只列正式构建入口。空列表代表尚未登记构建目标，不代表任务已验证。需要新增目标时更新清单并运行 `python scripts/workspace.py check`。
5. Lean/Mathlib 与根目录 `.lake/` 共享；导入可能跨任务复用，只有实际依赖会参与构建。不要运行全量 `lake build Solutions`。
6. 新研究、说明、脚本、验证记录放本目录；保留 `Definitions/`、`Theorems/`、`Solutions/` 的平台模块路径。API 文档仅在需要平台操作时按需读取。

任务入口是上下文约定，不是文件系统权限隔离。通过本目录启动新聊天可以避免沿用其他任务的聊天上下文。
