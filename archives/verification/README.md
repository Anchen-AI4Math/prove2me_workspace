# 大型验证数据归档

此目录保存工作区内大型验证数据的精确字节。`index.json` 将原始仓库相对路径映射到大小和 SHA-256；`objects/<sha256>.gz` 保存去重后的 gzip 数据。归档不代表对应数学目标已经得到证明。

## 使用

在仓库根目录运行，无需第三方 Python 包或网络：

```powershell
python scripts/workspace_data.py verify
python scripts/workspace_data.py restore
# 或者仅恢复当前任务
python scripts/workspace_data.py restore --mission zeta9
python scripts/workspace.py check
```

恢复前检查目标路径和所有归档哈希，已有原文件字节相同则跳过，不同则报错并保留原文件。新文件在校验通过后以独占方式写入，避免覆盖并发创建的文件。Windows 长路径由工具处理。

新增归档：`python scripts/workspace_data.py pack --mission <slug>`。只打包该任务未跟踪、至少 1 MiB 的 `.json`、`.jsonl`、`.bin` 或无扩展名数据，保留所有本地原文件。不会打包 Lean/Python 源文件。任务的 `.gitignore` 自动维护精确路径清单；不要手动删除索引仍引用的对象。

共享 Mathlib/Lake 缓存与密钥不属于本归档。论文、发布 PDF/ZIP、任务状态、源码以及较小的验证记录继续按原路径直接版本管理。
