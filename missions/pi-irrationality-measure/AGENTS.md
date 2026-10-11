# π 无理性度 campaign

- 先读 `status.md` 与 `scope.json`。只处理本任务和实际 import 依赖。
- 目标：根据 OpenAI math family 017 的公开结果，推进 Prove2Me 的 `pi-irrationality-measure` campaign。
- 使用 campaign 原有定义与模板；不得用自定义的无理性度代替平台定义。
- 先复现源证明并检查 `#print axioms`；比较器中的 `sorry` 是声明占位，不是可提交证明。
- 保留源仓库 commit、文件哈希、原始文件及版本差异。不要更改共享 Lean/Mathlib 版本。
- 构建：`python scripts/workspace.py build pi-irrationality-measure`。
- 用户明确单个 theorem 的编译预算为 300 秒（2026-10-07）；生成后的每个提交节点都须在该上限内验证，超限则拆分辅助证明。单文件预检默认对整个文件采用更严格的 300 秒限时。
- 平台提案保持 Draft，交由用户在网站逐项审核并提交；遵循根目录 `SKILL.md` 与 `references/campaigns.md`。
