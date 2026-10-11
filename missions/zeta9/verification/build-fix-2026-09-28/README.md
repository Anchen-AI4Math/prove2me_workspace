# zeta9 构建读取错误修复

2026-09-28。用户要求修复此前 `.olean.private` 读取失败。

## 诊断边界

原八个入口全部 `import Mathlib`，一次构建图为 8713 项。
此前并发构建报多个代数几何 `.olean.private` 无法读取，但随后文件存在，
串行导入成功。因此“缓存缺失”不是已证实原因；并发加载/资源压力是合理推断，
没有取得当时的底层 Windows 错误码，不能断言具体系统故障。

## 持久修复

只修改 zeta9 所属八个 `Theorems/Thm_ZetaNine_*.lean` /
`Theorems/Thm_Zeta9Note_*.lean` 的导入：

- ζ(9) 指数形式：`Mathlib.NumberTheory.LSeries.RiemannZeta`。
- 无理性准则：`Mathlib.NumberTheory.Real.Irrational`。
- 五点求积：多项式求值与次数、实数、Fin 的有限类型模块。
- 加权平均：实数、Fin 的有限类型及有限和模块。

定理名称、陈述、注释及证明体逐字节保持不变。清单及前后 SHA-256 见
[imports.json](imports.json)。未重装或删除 Mathlib 缓存，未修改共享构建器。

## 验证

从根目录执行 `python scripts/workspace.py build zeta9`，八个目标全部显示 **Built**，
不是 Replayed；同一次普通构建完成，退出码 0，没有串行预热。
构建图为 **3150 jobs**，八个入口各用时 12–18 秒。见 [build.log](build.log)。

此修复解决本次可验证的构建问题；它不保证在任意资源耗尽情况下都能编译。
八个镜像中原有的 `sorry` 警告仍在，构建成功不是无理性证明完成。
