# 任务目录

在对应 `missions/<slug>/` 目录开启 agent 聊天；先读该任务的 `AGENTS.md` 与交接文档。

共享 Lean/Mathlib，按任务选择构建入口。仓库根目录运行：

```powershell
python scripts/workspace.py show <slug>
python scripts/workspace.py files <slug>
python scripts/workspace.py build <slug> --dry-run
python scripts/workspace.py build <slug>
```

| 领域 | 任务与交接 | agent 入口 |
| --- | --- | --- |
| number-theory | [Pi irrationality measure: OpenAI exponent-two campaign entry](pi-irrationality-measure/status.md) | [pi-irrationality-measure](pi-irrationality-measure/AGENTS.md) |
| magic-squares | [Magic Squares I: order-three enumeration](magic-squares/status.md) | [magic-squares](magic-squares/AGENTS.md) |
| magic-squares | [Magic Squares II: semi-magic count](semi-magic/status.md) | [semi-magic](semi-magic/AGENTS.md) |
| magic-squares | [Magic Squares III: normal order-three squares](normal3/status.md) | [normal3](normal3/AGENTS.md) |
| magic-squares | [Magic Squares IV: special order-three classes](magic-squares-iv/status.md) | [magic-squares-iv](magic-squares-iv/AGENTS.md) |
| magic-squares | [Magic Squares V: general counting theory](magic-squares-v/status.md) | [magic-squares-v](magic-squares-v/AGENTS.md) |
| magic-squares | [Magic-square node reattachment (maintenance)](magic-squares-reattach/status.md) | [magic-squares-reattach](magic-squares-reattach/AGENTS.md) |
| number-theory | [Every odd number: at most five primes](five-primes/status.md) | [five-primes](five-primes/AGENTS.md) |
| number-theory | [Weak Goldbach](weak-goldbach/status.md) | [weak-goldbach](weak-goldbach/AGENTS.md) |
| number-theory | [Elementary number theory textbook (proposal)](nt-textbook-proposal/DRAFT.md) | [nt-textbook-proposal](nt-textbook-proposal/AGENTS.md) |
| analysis | [Irrationality of Euler gamma](euler-gamma/SESSION-CHECKPOINT.md) | [euler-gamma](euler-gamma/AGENTS.md) |
| probability | [The Bunkbed conjecture is false](bunkbed/status.md) | [bunkbed](bunkbed/AGENTS.md) |
| number-theory | [Distinct prime polynomial record search](prime-polynomials/status.md) | [prime-polynomials](prime-polynomials/AGENTS.md) |
| number-theory | [Equal sums of two squares: parametrization and infinite families](two-squares/status.md) | [two-squares](two-squares/AGENTS.md) |
| number-theory | [Zeta(7) irrationality research attempt](zeta7/status.md) | [zeta7](zeta7/AGENTS.md) |
| number-theory | [Zeta(9) irrationality research](zeta9/status.md) | [zeta9](zeta9/AGENTS.md) |
| number-theory | [Zudilin: one of zeta(5,7,9,11) is irrational](zudilin/explanation_reduction.md) | [zudilin](zudilin/AGENTS.md) |
| logic | [Fast-growing hierarchies above epsilon-zero: feasibility](fgh-scout/FEASIBILITY-REPORT.md) | [fgh-scout](fgh-scout/AGENTS.md) |
| combinatorics | [Binary strings with no adjacent ones](no-adjacent/status.md) | [no-adjacent](no-adjacent/AGENTS.md) |
| approximation-algorithms | [Karmarkar-Karp II: geometric grouping](kk-bin-packing/status.md) | [kk-bin-packing](kk-bin-packing/AGENTS.md) |
| combinatorics | [Snaky in 21 Maker moves](snaky-21/status.md) | [snaky-21](snaky-21/AGENTS.md) |

平台状态以各任务的带日期证据为准。新增任务需登记 `index.json`、`scope.json`、`AGENTS.md` 与本目录导航，再运行 `python scripts/workspace.py check`。
