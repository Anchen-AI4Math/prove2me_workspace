# Snaky in 21 Maker moves

先读 `status.md` 与 `scope.json`。只处理本任务及其真实 import 依赖。
从根目录运行 `python scripts/workspace.py build snaky-21`，不要全量构建 Solutions。
保持平台 SnakyTwentyOne 定义和主目标声明原样；论文固定于 adc7f1241b42e322a6451854ab7e4b4c146bf78a。
Python 证书检查不是 Lean 证明。最终审计必须排除 sorryAx 与新增公理。
新增证明文件更新 scope.json。平台凭证只用于必要的认证请求，不打印。
验证成功的支撑结果逐项提交并接回主目标；SKETCH_ACCEPTED 不表示完成。

2026-10-09 用户报告本地检查导致电脑卡死。机器约 16 GB RAM，单个本任务 Lean 进程曾占约
5.9 GB。当前续接使用平台端分块验证；不得自动启动本地 Lean/Lake 或旧的续编检查器。
低占用的源码生成、API 请求和结构检查可以继续。参见 verification/resource-policy.json。
