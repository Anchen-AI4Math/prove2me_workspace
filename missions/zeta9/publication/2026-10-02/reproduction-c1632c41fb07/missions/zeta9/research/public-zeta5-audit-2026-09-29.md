# 公开 ζ(5) 进展与 ζ(9) 换路线：独立源码审查

审查日期：2026-09-29。范围为 Fauzan 原预印本、指定的 Dan Romik 仓库及直接相关原始文献；未安装依赖、未运行外部代码、未执行 Lean build 或 kernel replay。没有依据 Reddit 评论认定数学结论。

## 1. 结论与证据层级

指定仓库确有完整终点 `Zeta5.zeta5_irrational`，不是仅列出目标或留下论文核心条件的 scaffold。但它显式使用一条项目公理——通常的素数定理。因此准确表述是：**仓库提交了基于 PNT 的 ζ(5) 无理性形式化，并报告完成 Lean 内核复检；本轮已独立核对终点、源码静态特征和固定版本，尚未独立重编译。**

这比“网上有人声称 ζ(5) 已证明”强得多，也不同于“完全没有外部公理的 Mathlib 定理”。PNT 是既有经典定理，并非把待证明的 ζ(5) 命题换名作为假设。形式系统中的这一依赖仍必须明示。

## 2. 版本与实际 theorem

本轮固定 [commit fc2fefa77076e22e7e80b4c101ded5a98d53e14d](https://github.com/danromik/zeta5-irrationality/tree/fc2fefa77076e22e7e80b4c101ded5a98d53e14d)，提交时间 2026-09-25 09:08:54 UTC。工具链为 Lean 4.34.0，Mathlib v4.34.0 的锁定修订为 `5ed2965256430c3649e86755f9576b54eca72435`。

[cert/Check.lean](https://github.com/danromik/zeta5-irrationality/blob/fc2fefa77076e22e7e80b4c101ded5a98d53e14d/cert/Check.lean) 使用 Mathlib 名称复述：

```lean
Irrational (∑' v : ℕ, (1 : ℝ) / ((v : ℝ) + 1) ^ 5)
```

这正是实数级数 ζ(5)。它没有在终点额外假设正性、整数化或衰减。[Interface.lean](https://github.com/danromik/zeta5-irrationality/blob/fc2fefa77076e22e7e80b4c101ded5a98d53e14d/Zeta5/Interface.lean) 用已构造的分配 `stdAlloc` 和已证明的中间定理装配终点。

[Axioms.lean](https://github.com/danromik/zeta5-irrationality/blob/fc2fefa77076e22e7e80b4c101ded5a98d53e14d/Zeta5/Axioms.lean) 的唯一项目 axiom 是 Mathlib `Chebyshev.theta x / x → 1`。仓库报告的终点公理依赖为 `propext`、`Classical.choice`、`Quot.sound` 和该 PNT 公理。

本地对固定快照全部 **74 个 `.lean` 文件**去除嵌套注释与字符串后做词法扫描：`sorry`、`admit`、`unsafe`、`native_decide`、`implemented_by`、`extern` 均为 0；`axiom` 恰为上述一处。这是源码筛查，不冒充内核依赖检查，也不审查全部 Mathlib 源码。

## 3. 构建与审查状态

[CERTIFICATION.md](https://github.com/danromik/zeta5-irrationality/blob/fc2fefa77076e22e7e80b4c101ded5a98d53e14d/docs/CERTIFICATION.md) 报告 2026-09-25 在 `a87234f` 上完成 clean build、终点公理打印和独立进程 `leanchecker` 全模块重检，退出码为 0。本轮通过 GitHub compare API 独立确认：当前提交仅比该认证版本多一次 `docs/CERTIFICATION.md` 修改，证明源码没有变化。

这里区分“维护者记录的成功重检”和“本轮亲自重检”。本轮只完成前述源审；没有作出后一声明。当前取得的原始来源仍称论文为预印本，没有据此认定已获期刊同行评审或数学界一致验收。

另一个 [long-mathematics 同名仓库](https://github.com/long-mathematics/zeta5-irrationality) 在本次查询时明确尚未完成无理性终点。不能将不同仓库的状态混用。

## 4. 原预印本与新路线的实质

[Fauzan v1](https://zenodo.org/records/22826419) 日期为 2026-09-17，DOI `10.5281/zenodo.22826419`。PDF SHA256 为 `a42c05ccc46b9a7c36428913453c4617202c59109713ba20f464ab9ec640d0da`。论文构造次数随 n 线性增长的整数多项式，目标值严格正且按 n² 指数衰减。非零性来自正矩 Hankel 行列式；分母成本则对整个有理泛函估计，包含多项式商与极点项。其第 31 页明确没有宣称已完成更高奇数值扩展。

[Basic.lean](https://github.com/danromik/zeta5-irrationality/blob/fc2fefa77076e22e7e80b4c101ded5a98d53e14d/Zeta5/Basic.lean) 固定 `K=40n,N=3n,h=37n`，以 `D_N(t)^6/D_K(t)` 修饰测度。这个 numerator power 与参数比例属于定量构造，不是可以不经检查地沿用到 ζ(9) 的常数。

独立数学判断：这条路线值得在 zeta9 中单独推进，因为它可以通过正性直接提供非零量，不需要先解决当前最短线性形式的形状猜想。新的关键门槛是找到 **同一族** 多项式，其所有系数同时整数化后仍保持严格二次指数衰减。

## 5. ζ(9) 哪些部分可移植，哪些尚缺

[2026-09-24 的公开数学说明](https://galoisrepresentations.org/2026/09/24/zeta5-is-irrational/) 已给任意整数 k≥2 的泛函与正密度，正 Gram 结构及 degree 结论可推广；它同时明确当前定量论证没有直接覆盖 k>5。这里把该说明当作可检查的数学推导来源，不把其中未形式化的参数改进视为本仓库 Lean 结论。

代入 k=9 后，极点函数中的 `j^4,H_j^(5),−1/4` 改为 `j^8,H_j^(9),−1/8`；多项式矩中的三次因子改为七次因子，常数分母为 `8!`；正密度中的 `y^5` 和四阶导数改为 `y^9` 与八阶导数。由此必须重新核对全泛函的素数估值、平方节点合并后的混合配对、分母正规化及实能量余量。不能只验证有利极点项，也不能从正性单独推出无理性。某些改变可能只产生低阶误差，另一些会改变主成本；必须计算，不能预设。

有关方法的原始文献入口是 [Prévost 的 Hurwitz ζ Padé 论文](https://arxiv.org/abs/1709.05389)、[Zudilin 的行列式无理性判据](https://arxiv.org/abs/1507.05697) 与 [Brown 的多参数 Mellin 判据](https://arxiv.org/abs/2604.20741)。本轮只核查其文献身份和摘要范围，没有把它们说成 ζ(9) 现成证明。

## 6. 本地可复核材料

- [来源获取与静态审计脚本](../scripts/audit_public_zeta5.py)：只读取公网源，不运行下载的代码。
- [证据清单](../verification/public-zeta5-audit-2026-09-29/manifest.json)：commit、源文件 SHA256、词法扫描、PDF 指纹、工具链及认证版本差异。
- [原 PDF](../verification/public-zeta5-audit-2026-09-29/Fauzan-zeta5-v1.pdf) 与 [提取文本](../verification/public-zeta5-audit-2026-09-29/Fauzan-zeta5-v1.txt)。
- `verification/public-zeta5-audit-2026-09-29/sources/` 保存所审核心文件；其余源文件只保存指纹。

不修改 status/scope；不把这些第三方源码加入任务 Lean 构建入口。
