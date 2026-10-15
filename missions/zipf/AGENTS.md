# Zipf 分布任务

先读 `status.md` 和 `scope.json`。平台任务 ID 为
`9d7a43ac-2157-449b-a0b5-93d1d19ef7c2`。

- 保留平台原始定义和定理陈述，验证证据放在 `verification/`。
- 主目标是 `ZipfLaw.zipf_infinite_extension`；里程碑按平台原始陈述推进。
- 证明使用本工作区固定的 Lean 4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。
- 编译运行 `python scripts/workspace.py build zipf`，新增文件后更新 `scope.json` 并运行工作区结构检查。
- 提交文件具有顶层 `theorem solution`，不得导入目标本身，不得包含未证明的占位符。
- 仅更新本任务及必要的根目录任务导航，不改其他任务的工作。
