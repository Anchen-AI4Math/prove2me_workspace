# ζ(9) Prove2me 私有提案

**当前交接（2026-10-02）：** 用户决定公开这个已有 mission。最新公开首页、源码包、
里程碑状态核对及实际 API 回读统一放在
[publication/2026-10-02](../../publication/2026-10-02/README.md)。
下面的 `Private`、提案数量与数学开放状态是原日期的历史记录；当前数学状态以
[公开总览](../../PUBLIC_OVERVIEW.md)为准，公开审核状态以此次平台回读为准。
根目标仍开放，书面已证节点不自动成为平台 Lean 已证节点。

本目录把[本地数学 DAG](../DAG.md)的目标和可独立形式化的归约整理成 Prove2me private mission。平台回读记录在 [proposal-receipt.json](proposal-receipt.json)：提案 ID `06faf23f-00c2-4edf-92ab-1212cdb7d7d6`，mission ID `8195d8fe-059f-4515-92b4-57b585e2bac6`，当前状态 `Private`。数学根节点仍开放。

提案包含一个根定理 `ZetaNine.irrational_zeta_nine`、两条通用归约陈述，以及既有的 Zudilin 四数择一无理定理引用；三项里程碑分别对应该文献结果、两形式无理性准则和抽象指数裕量桥。三份提案 Lean 文件以 `by sorry` 收尾，只是陈述；根定理仍开放。每项新陈述已附独立盲读回。

[两形式准则的完整证明](solutions/Sol_ZetaNine_irrational_of_two_small_integer_forms.lean)和[抽象裕量桥的完整证明](solutions/Sol_ZetaNine_exponential_margin_of_volume_and_shape.lean)已在本地 Lean 4.33.1 编译，并以数学说明提交到此 private mission。平台回执 [proof-submissions.json](solutions/proof-submissions.json) 记录两项均为 `ACCEPTED`。这不形式化本地 J、V、S、VA，也不证明 `ζ(9)` 无理。

本轮新数学结果的三个**抽象核心**已在本地编译并由平台接受：[体积对数消去](solutions/Sol_ZetaNine_volume_baseline_cancellation.lean)以具体面积等式为前提，[有限素数预算](solutions/Sol_ZetaNine_finite_prime_budget.lean)证明逐项估值不等式，[精确有限素数折扣](solutions/Sol_ZetaNine_finite_prime_discount.lean)证明新的加权恒等式。三者的私有定理 ID、发布作业和验证回执见 [new-results-receipt.json](new-results-receipt.json)。[对应范围表](new-dag-mapping.md)明确区分抽象证明与尚未 Lean 形式化的具体 Q、X、Y、YD。

Private mission 的说明现包含双形式主线、正号单形式备选路线及精确折扣预算，共十七项新增研究里程碑。Q2、Y1、YD 链接已接受的抽象定理；TP、T、TG、VD 和其他具体算术里程碑尚未链接忠实 Lean 定理。H、Z、I、LC、TP 为新数学笔记证明，具体形式化仍待进行；T、TG、VD、VC、S 仍是数学开放节点。平台根定理已回读为 `Open`，mission 可见性已回读为 `private`。

本地 J、T、TG、V、S、VD 的具体算术量与 Taylor 锥尚未编码成 Lean 定义，所以它们只出现在 mission 说明和本地 DAG 中，保持数学上的开放状态；笔记已证的 F、A、G、P、M、C、L、X、H、Z、I、LC、TP 也未被冒充为平台已证。

用户已按 Prove2me 的 [mission captain 流程](https://github.com/prove2me/prove2me_workspace/blob/main/references/mission_captain.md)完成逐项确认和提交；平台已回读 `Private`。同步脚本中的 `--refresh-status` 只读取平台状态并更新本地回执，不会公开 mission。

本地复核：

```powershell
python missions/zeta9/roadmap/verify_dag.py
python missions/zeta9/roadmap/verification/check_inverse_area_roots.py
python missions/zeta9/roadmap/verification/check_prime_valuation_attack.py
python missions/zeta9/roadmap/verify_artifacts.py
python missions/zeta9/roadmap/platform/sync_private_proposal.py
```

## 2026-09-25：目标定理接上平台依赖图

此前根节点 `ZetaNine.irrational_zeta_nine` 在平台的 dependency graph 里**一个孩子都没有**——
mission 说明写了箭头，图里没有边。现在根节点有两条已接受的 proof-sketch 分解，另有**七**个
已证的一般引理节点，里程碑数 35 → 44（其中 15 条挂到定理）。细节与复现命令见
[wiring/README.md](wiring/README.md)，平台回执 [wiring/wiring-receipt.json](wiring/wiring-receipt.json)
与 [wiring/notes-layer-receipt.json](wiring/notes-layer-receipt.json)，
盲审报告 [wiring/readback-2026-09-25.md](wiring/readback-2026-09-25.md) 与
[wiring/readback-notes-layer-2026-09-25.md](wiring/readback-notes-layer-2026-09-25.md)。

| 新节点 | 状态 | 链接里程碑 |
|---|---|---|
| `ZetaNine.irrational_of_small_nonzero_integer_forms` | Proved | TP2 |
| `ZetaNine.taylor_sign_implies_kernel_sum_pos` | Proved | TP1 |
| `ZetaNine.quadrature_exact_of_moments` | Proved | FQ1 |
| `ZetaNine.five_sample_sign_forces_nonzero` | Proved | TP3 |
| `ZetaNine.min_lt_weighted_average_lt_max` | Proved | FI1 |
| `ZetaNine.mediant_strictly_between_min_and_max` | Proved | FI2 |
| `ZetaNine.positive_matrix_maps_nonneg_to_pos` | Proved | TA1 |
| `ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine` | Open | R1 |
| `ZetaNine.exponentially_small_independent_forms_of_zeta_nine` | Open | R2 |

**已登记的两条内部边**（平台的 decomposition）：`five_sample_sign_forces_nonzero ←
quadrature_exact_of_moments`、`mediant_strictly_between_min_and_max ←
min_lt_weighted_average_lt_max`。

两条根约简：单形式路线 `{一对多式准则(Proved), 指数小非零形式义务(Open)}`、双形式路线
`{双形式准则(Proved), 指数小独立形式义务(Open)}`，均 `SKETCH_ACCEPTED`。两个开放义务都
**严格强于**目标且**不等价**（要求固定速率的指数级逼近），因此根仍 `Open`。

## 2026-09-25：公开 mission（ζ(9) 笔记的抽象层）

与上面的 private mission 平行，另有一个**公开** mission 提案
*Formalize the abstract layer of "Research Notes on ζ(9)" (v0.1)*，提案 ID
`00d787d8-91c8-45bf-87f0-6a5e9e8bc472`，命名空间 `Zeta9Note.*`（与私有侧 `ZetaNine.*` 隔离），
可见性 `public`，8 个 item + 7 条里程碑，目标是单形式无理性准则。它只承载**抽象层**——
八条陈述都不出现 ζ(9)。

本地 8 份 `Sol_Zeta9Note_*.lean` 全部 `lake env lean` 编译通过（含两条归约，先
`lake build` 了 `Theorems.Thm_Zeta9Note_quadrature_exact_of_moments` 与
`…_min_lt_weighted_average_lt_max`），公开仓库的合并文件
`zeta9-research-notes/formalization/Zeta9Note.lean` 也编译通过。8 份证明已提交平台，
**8/8 `ACCEPTED`，8 条定理全部转为 `Proved`**；回执
[public-proposal/submissions-receipt.json](public-proposal/submissions-receipt.json)，
流程与复现命令见 [public-proposal/README.md](public-proposal/README.md)。

提案此刻仍是 `In review`（`mission_id` 为空，等 moderator 批准）。这纠正了此前的一个错误假设：
脚本原以为 `In review` 期间平台不接受提交，实测 `POST /verify` 照常接受，定理状态也会立刻翻转。

这不改变私有侧的状态：私有根 `ZetaNine.irrational_zeta_nine` 仍 `Open`，两个指数小形式义务
既未证也不等价于根。

**没有接的**：具体构造（$F_n$、饱和核、Smith 数据、加权面积、同余格极小值）仍无 Lean 定义，
所以 `V←VA,Q,X`、`VA←VB,Y`、`VB←VC,H,Z` 等算术箭头没有作为平台分解发布；X、VB、VC、VD、S、
J、T、TG、TS、T5、FD、FM、CP 里程碑仍未链接定理。两条原因记在 wiring/README 里：① 只写
「存在小整数形式」的孩子一旦有准则就与目标**等价**，是伪装的重述而非分解；② 带自由参数的
父节点无法 import 封闭的孩子定理，多级图必须先有定义层。下一步就是补定义层 + 逐节点挂
statement。
