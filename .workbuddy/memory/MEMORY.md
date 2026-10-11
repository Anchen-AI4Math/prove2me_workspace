# Project memory — prove2me_workspace

Lean 4 / Mathlib 打 prove2.me 众包形式化平台。**本文件只做索引**，细节在下列文件里，别再往这里堆：

| 想找什么 | 去哪 |
|---|---|
| Lean / Mathlib 踩坑、tactic 怪癖 | `memory/LEAN-PITFALLS.md` |
| 平台 API、成员资格、draft 校验、盲审、提交模式 | `memory/PLATFORM-NOTES.md` |
| 幻方领域数据、BCCG 文献、可选路线 | `memory/MAGIC-SQUARES-REF.md` |
| 单个 mission 的设计与进度 | `missions/<slug>/status.md` |
| ζ(7)/ζ(9) 无理性尝试（ζ(9) 有 private mission，见下表） | `missions/{zeta7,zeta9}/research/*.md`, `report.md` |
| **ζ(9) 九轮 + roadmap + 平台层的完整证明态审计** | `missions/zeta9/research/zeta9-proof-state-audit.tex`（+ `-zh.md` 中文摘要） |
| 幻方 V Spencer 路线 | `missions/magic-squares-v/SPENCER-ROUTE.md`, `S5-NOTES.md` |
| 五素数 A/A\* 路线审计 | `missions/five-primes/status.md`, `A-star-route-audit.md` |
| **ε₀ 以上 FGH / 序数表示 可行性侦察（2026-09-26）** | `missions/fgh-scout/FEASIBILITY-REPORT.md`（结论 GO WITH REDUCED SCOPE；探测代码 `tmp/eps_probe.lean` 编译通过） |

## 环境（Windows）

- Bash PATH 是坏的：**每条命令先** `export PATH="/usr/bin:/bin:/c/Windows/System32:/c/Windows:$PATH";`
  PowerShell 工具取不到输出，别用。**同一消息里别并行发两个 Bash 调用**（其中一个被 SIGTERM 且无输出）；
  长命令用 `run_in_background`，后台跑时别再加第二条。⚠️ 输出**重定向到文件时必须加 `-u`**，
  否则进程被杀时缓冲区丢光、文件为 0 字节（2026-09-25 复现）。
- 🔴 **别用 Bash 删 `Solutions/` 里的文件**（2026-09-17：整个目录消失）→ 改用资源管理器；
  恢复：`rm -f .git/index.lock && git checkout HEAD -- .`。
- Lean `v4.33.1`（elan），Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，已构建在 `.lake/`
  （8.4 GB，**绝不删**）。Python：`C:/Users/anche/.workbuddy/binaries/python/versions/3.13.12/python.exe`。
  纯 Python 包（mpmath 等）在 `tmp/zeta7/exact_packages`，脚本靠 `sys.path.insert` 加载；
  那里的 numpy/scipy 是 cp312，配 3.13 会 import 失败。
- 单文件 `lake env lean <file>`；模块 `lake build <Module.Name>`。⚠️ **全量 `lake build` 会随机失败
  20–35 个模块**（`failed to read file '...olean'`，并发 IO 竞争未定位）→ 只 build 目标模块。
- `lakefile.lean` 给 `Definitions`/`Theorems`/`Solutions` 开了 `autoImplicit false`，`examples/`
  不是 lean_lib（那里是 ON）⇒ **提交前必须挪进 `Solutions/` 再编一遍**。例外：`examples/magic-squares/spencer/`
  八文件互 import，已是 lean_lib `SpencerRoute`（非 default target）→ `lake build SpencerRoute`；
  import 名带书名号：`import examples.«magic-squares».spencer.SupportSplit`。
- `lakefile.lean`/`lean-toolchain`/`lake-manifest.json` 都是被跟踪的 ⇒ 常规 `git add` 即可，**不需要 `-f`**。

## 各 mission 状态（一行）

| mission | slug | 状态 |
|---|---|---|
| Magic Squares I/II/III | `magic-squares` / `semi-magic` / `normal3` | 三个 goal 全 Proved，proposal Reviewed |
| Magic Squares IV | `magic-squares-iv` | goal + 6 定理 + 1 定义全 Proved；proposal `7af96e14` In review |
| Magic Squares V | `magic-squares-v` | mission `e06131f8`（≠ IV 的 `df1cb8cc`）。goal `semi_magic_polynomial_exists` 仍 **Open**；S1–S4 + Brick 12 全完，节点 `4394b225`（`…_degree_eq`，Proved）已上平台。**只剩 S5** = (A) 倒易律 `q_B(−1)` + (B) 面格 Euler `Σ(−1)^rank B = 1`，n=2/3/4 数值通过但无初等推论 |
| 孤儿挂回（一次性） | `magic-squares-reattach` | 18 条经 milestone 挂回，22→4 孤儿（余 4 是定义） |
| Every Odd Number … Five Primes | `five-primes` | **Open**。θ 链 = `theta_lower_finite`(Proved) + `…_analytic_finite`(Open) + `schoenfeld_psi_error_large`(Open，单点最高杠杆)。Mertens 侧 `mertens_tail_le_partial_sum` 已 Proved，A/A\* 已 SKETCH_ACCEPTED（`512a35d6`/`ebbdeec3`） |
| Weak Goldbach | `weak-goldbach` | 目标 Open，已归约到一个筛覆盖孩子 |
| Bunkbed is False | `bunkbed` | 全部封版归档 |
| Irrationality of Euler's γ | `euler-gamma` | 部分 Proved，见 `sondow/INTEGRAL-IDENTITY-COMPLETE.md` |
| ζ(7) 泛奇 ζ 支撑研究 | `zeta7` | **本地研究，无平台 mission**。为 zeta9 提供 odd-zeta 泛函件，见 `missions/zeta7/status.md` |
| **Irrationality of ζ(9): weighted lattice route** | `zeta9` | mission `8195d8fe-059f-4515-92b4-57b585e2bac6`（**Private**，不是「无平台节点」）。本地数学 DAG = `missions/zeta9/roadmap/DAG.md`；平台接线 = `roadmap/platform/wiring/README.md`。**2026-09-25：根节点从「零分解」→ 两条 `SKETCH_ACCEPTED` 分解**（单形式 / 双形式各一条），+3 条 Proved 一般引理（TP/FQ 的可形式化核）+2 条 Open 义务节点，里程碑 35→40。根仍 **Open** |
| ζ(9) 公开侧 | `zeta9`（公开） | 公共仓库 `github.com/Anchen0823/zeta9-research-notes`（本地 `D:\users\self_projects\zeta9-research-notes`，Zenodo concept DOI `10.5281/zenodo.22951154`，已开 Zenodo–GitHub 联动）。**公开 ResearchPaper mission** proposal `00d787d8-…`（Draft→**In review**，`mission_id` 仍空），8 个 `Zeta9Note.*` items + 7 milestones。**2026-09-25：8 条证明已提交并全 `ACCEPTED`，8 条定理全 `Proved`**（回执 `public-proposal/submissions-receipt.json`，流程见同目录 `README.md`）。流程已存为 skill `prove2me-public-mission`；🔴 该 skill 曾误记「In review 期间平台不收提交」——实测照收，已更正 |
| **Equal Sums of Two Squares（参数化 + 无限族）** | `two-squares` | **2026-09-26 新开**。本地 Obj 1–3 全 Proved（`lake build TwoSquares` 绿 + 公理干净），15 条定理。Obj 4「四值为正且两两不同」用一条严格链表达（`1 < 2n-1 < n²-n-1 < n²-n+1`，边界 4 紧）。公开 proposal `1c96fbbb` **已 Submit → `In review`**（`mission_id` 仍 null，等 moderator）。**2026-09-26 20:2x：13/13 条全部提交并 `ACCEPTED`，含 goal `complete_parametrization`** ⇒ Obj 1–6 全闭。平台命名空间 `EqualTwoSquares` ≠ 本地 `TwoSquares`。见 `missions/two-squares/status.md`（含两个坑：`rw` 会污染 `Int.gcd`；本 pin 无 `Int.gcd_comm`，用 Bézout 替代） |

## 跨 mission 硬约束

**五素数**（细节 `missions/five-primes/status.md`）：① frontier 叶多为硬外部结果（R&S、Schoenfeld、
Liu–Wang、Siebert、Helfgott–Platt、4·10^14 Goldbach）；② `theorem51_vaughan_split` **是假的**（评论
`1c0c941b`，反例 `vaughan-step-counterexample.lean`）——andreaskapfer 已发布 repaired 版 `3a0afac6`；
③ `theorem51_typeII_dyadic_block_bound` 不是短约简（三个「已证成分」都以 Open 的 `large_sieve_inequality`
为假设）；完整数值证伪不可行（~1400 条 7–8 位 log 界、~10⁵ 行）；④ frontier 数会被**循环约简**污染，
真义务数法用 `tmp/frontier_report.py`；⑤ 🔴 **平台证书机制只给上界**（`Chebyshev.psi_eq_log_lcmUpto` +
`by decide`）⇒ 只能证 ψ 的上界，θ 是 primorial 的对数、给不出下界，别以为 `rosser_psi_certificate_*` 能平移。
动手前先读 `GET /missions/<mid>/comments`；提交文件必须**根级** `theorem solution`（包 namespace 判 WA）。

**ζ(9) 接线的两条硬教训**（2026-09-25，细节 `roadmap/platform/wiring/README.md`）：
① **「存在小整数形式」型的孩子一旦平台上有准则就与目标等价**（Dirichlet 给每个无理数这种形式，准则
反过来给无理性）⇒ 拿它当根的孩子是**伪装的重述**，不是分解；要严格更强必须钉死**固定指数速率**
（一般无理数不保证指数级逼近）。② **带自由参数的父节点无法 import 封闭的孩子定理** ⇒ 想建多级图
必须先给具体构造（$F_n$、饱和核、Smith 数据、加权面积、同余格极小值）写 Lean 定义，每个节点一条
封闭 statement。所以算术箭头 `V←VA,Q,X` 等**暂不发布**是有意为之，不是遗漏。

**幻方**（细节 `memory/MAGIC-SQUARES-REF.md`）：① **`IsPanMagic` ≠ BCCG 的 $P_n$**（我方两个方向、
BCCG 单向且不要求副对角），引用时不可互相对照；② Mathlib 无 Ehrhart / 拟多项式 / 有理生成函数，格点计数要自建；
③ 走 Spencer 纯初等路线（生成函数 + Hall + 支撑集偏序，不用 Ehrhart），S5 是最硬的剩项。

## 仓库卫生

两轮瘦身（2026-09-17）只做 `git rm --cached`，磁盘文件全保留；新生成的证书产物一律写 `tmp/`。
`.git` 仍 146 MB，彻底瘦身要 `git filter-repo` + force push —— **不可逆，必须宇轩点头**。

## 用户偏好

- 数学/Lean/文档写**英文**，给他的汇报写**中文**。Lean 教学别拆太碎，给完整证明任务。
- **严格区分「我确认了」和「我推测」**——数值验证 ≠ 形式化证明；报告要写明证据边界。
- 不可逆操作（rewrite history / force push / 删历史产物）**必须先问**。要可运行的交付物。
- **他是这几个幻方 mission 的 captain**（2026-09-18 确认）⇒ 挂节点、批 proposal 这类动作他自己能做。
