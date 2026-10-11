# ζ(9) 首轮攻击报告

2026-09-24。**预定网格与验证已执行完成，尚未得到 ζ(9) 的无理性证明。**
21 个线性形式样本和 21 个 ζ(9) Gram 样本的 primitive 整数形式都经 Arb 认证绝对值大于 1。
两例 ζ(5)、ζ(7) 回归对照另计。44 例全部完成，没有超时或计算错误。
本轮获得了覆盖全部素数的更强整化引理、公因子的精确渐近公式以及经过区间认证的解析上界；这些局部成果未能合成负指数。

## 1. 主攻线性形式：完整网格与晋级决定

取偶数 $n$、$0\le m\le3n/14$，定义

$$
R_{n,m}(t)=\frac{n!^3}{m!^{14}}\frac{[(t-m)_m(t+n+1)_m]^7}{(t)_{n+1}^3},\qquad
L_{n,m}=\sum_{k\ge1}\frac{R^{(6)}_{n,m}(k)}{6!}=A_{n,m}\zeta(9)+B_{n,m}.
$$

部分分式和反射恒等式精确消去 ζ(7)、ζ(8)。程序对 $A,B$ 全系数清分母并除尽 gcd，
记录正有理倍数 $m_{\rm prim}$，得到 $P_{n,m}(X)=m_{\rm prim}(A_{n,m}X+B_{n,m})\in\mathbb Z[X]$。
线性形式可能为负；筛选值统一为 $\ell_n=\log|P_{n,m}(\zeta(9))|/n$。

| $m/n$ | $n=56$ | $n=112$ | $n=224$ |
|---|---:|---:|---:|
| 0（控制） | 7.301097 | 7.839264 | 7.527787 |
| 1/28 | 7.919132 | 8.527755 | 8.273517 |
| 1/14 | 8.438666 | 9.110458 | 8.657046 |
| 3/28 | 8.999860 | 9.108041 | 9.101122 |
| 1/7 | 9.117860 | 9.324543 | 9.337972 |
| 5/28 | 9.046996 | 9.909189 | 9.507511 |
| 3/14 | 9.290300 | 9.959672 | 9.790245 |

表中小数用于展示；[结果索引](verification/linear-results.jsonl)保留严格 Arb 区间，
[完整记录](verification/linear-coeff/)保留两个完整整数系数、原始有理系数、公因子、每步比例与 SHA-256。
21 例中正值 10 例、负值 11 例，全部认证 $|P|>1$。

六个正比例剖面均不满足“后两尺度都小于 1”或“三尺度的 $\ell_n$ 严格下降”的预定晋级门槛，
因此 $n=448$ 晋级数为零。$m=0$ 是控制组。主网格 $n=224$ 中最好的是 $m/n=1/28$，
$\ell_{224}\approx8.273517>0$。端点 $m/n=3/14$ 已纳入计算及解析尾部审查。

## 2. 本轮证明的算术改进

记

$$
C_j=(-1)^{m+j}\binom nj^3\binom{j+m}{m}^7\binom{n-j+m}{m}^7,\qquad
G=\gcd_{0\le j\le n}|C_j|,\quad d_n=\operatorname{lcm}(1,\ldots,n).
$$

完整证明给出比初始 $2d_{n+m}^9/G$ 更强的有限整化乘子：

$$
\boxed{\frac{d_n^9}{G}A_{n,m}\in\mathbb Z,\qquad
       \frac{d_n^9}{G}B_{n,m}\in\mathbb Z.}
$$

证明先用整数二项式 Taylor 系数去掉表面的因子 2，再利用最高素数幂层的进位所提供的七阶余量，
把调和分母上限从 $n+m$ 降至 $n$。它包括小素数、零剩余类、常数项和端点。
主代理与分析代理分别审查了证明；21 例还通过了各个极点的一阶、二阶系数整性核验。

对 $p^2>n+m$，另有精确公式

$$
\boxed{v_p(G)=7\,\mathbf1_{(n\bmod p)+2(m\bmod p)\ge2p-1}.}
$$

小素数总贡献为 $o(n)$，取整边界差别的总贡献至多 $7\log(n+2m+1)$。固定有理比例 $\alpha=m/n>0$ 时，

$$
\frac{\log G}{n}\longrightarrow
\Gamma(\alpha)=7\int_1^\infty\frac{\mathbf1_{\{x\}+2\{\alpha x\}\ge2}}{x^2}\,dx,\qquad
\frac1n\log\frac{d_n^9}{G}\longrightarrow9-\Gamma(\alpha).
$$

详见[算术证明](research/arithmetic.md)和[改进证书](verification/arithmetic-improved-certificates.json)。
Γ 的数值区间由有理周期积分、向外舍入和完整尾界获得；这里没有把渐近常数冒充有限分母上界。

这项改进减少了可证明整化乘子与 primitive 最优乘子之间的差距。
**它不会改变已经除尽 gcd 的实验多项式。** 对同一个有理线性形式，任何有效的正有理整化乘子
都是 primitive 乘子的正整数倍，因此更换清分母方式无法继续缩小本轮已记录的 primitive 值。

## 3. 解析估计闭合到哪里

已证明以 $c=m+1/2$ 为竖直线的精确轮廓表达及全域绝对值上界。相应相位为

$$
\Phi_\alpha(w)=-14\alpha\log\alpha+10w\log w+7(w+1+\alpha)\log(w+1+\alpha)
-7(w-\alpha)\log(w-\alpha)-10(w+1)\log(w+1),
$$

$$
\limsup_{n\to\infty,\ m=\alpha n}\frac{\log|L_{n,m}|}{n}\le
\sup_{y\ge0}H_\alpha(y),\qquad H_\alpha(y)=\Re\Phi_\alpha(\alpha+iy)-2\pi y.
$$

移位 Riemann 和给出包含 $y=0$ 的统一 $O(\log n)$ 误差；无限尾部单独由指数函数控制。
六个比例的全局最大值通过导数符号及 Arb 夹根认证。合并更强整化乘子后，目前得到的**上界常数**为：

| $\alpha$ | 算术成本 $9-\Gamma(\alpha)$，约 | $\sup H_\alpha$ 的严格上界 | 合并上界，向上舍入 |
|---|---:|---:|---:|
| 1/28 | 8.858284 | 0.671769718688 | 9.530055 |
| 1/14 | 8.717459 | 1.167676972547 | 9.885137 |
| 3/28 | 8.573372 | 1.609438937754 | 10.182811 |
| 1/7 | 8.421794 | 2.021873399673 | 10.443667 |
| 5/28 | 8.290944 | 2.416195251742 | 10.707140 |
| 3/14 | 8.147892 | 2.798637880122 | 10.946530 |

这些正数只是现有估计给出的上界，不能被读成 $|L|$ 或 $|P|$ 的下界。
它们没有推出整数形式趋零，也没有排除更尖锐的估计或其他构造。
六个振荡模式的主项、相位抵消以及无穷多个非零值仍未建立。
详见[解析证明](research/analytic.md)及[区间证书](verification/analytic-vertical-bound.json)。

## 4. Gram 对照

使用正权重的 ζ(9) 矩泛函，取 $D_N(t)^{2q}/D_K(t)$、连续单项式基底、
$q\in\{4,5\}$、$N/K\in\{1,3,6\}/40$、$h/K\in\{1/2,7/10,1-N/K\}$。
18 个 $K=40$ 样本全部完成；前三组进入 $K=80$。筛选指标为 $r_K=\log P_K(\zeta(9))/K^2$。

| $q$ | $N/K$ | $h/K$ | $r_{40}$ | $r_{80}$ |
|---:|---:|---:|---:|---:|
| 4 | 3/20 | 1/2 | 1.343774 | 1.429423 |
| 5 | 3/20 | 1/2 | 1.387844 | 1.432339 |
| 5 | 3/40 | 1/2 | 1.514384 | 1.623551 |

三组指标都上升。所有 21 个 ζ(9) Gram 值严格大于 1。旧构造对照复现
$r_{40}(\zeta(5))=-0.165705667$、$r_{40}(\zeta(7))=0.766949846$，完整系数哈希与既有记录一致。

另对最佳剖面在两个尺度构造了覆盖所有分母素数的精确 assignment 对偶证书。
用整数 Newton 换基后，证书相对 primitive 乘子的额外成本仍分别为
$\log(\mathrm{gap})/K^2\approx1.690479,1.817305$。换基改善这类估计，primitive 多项式保持不变。
这是有限证书，未被用作渐近界。见[Gram 索引](verification/gram-results.jsonl)、
[晋级清单](verification/gram-manifest.json)及[全素数有限证书](verification/gram-arithmetic-certificates.json)。

## 5. 独立核验与证据边界

- 44 份完整系数产物均重读核对哈希、primitive gcd 和正比例整化因子；使用不同求值分组重新做 Arb 计算。
- 默认基底与显式连续指数一致；小规模行列式按多个有理点直接交叉检查。
- 三个线性形式小例直接构造 $R(k+x)$ 的截断 Taylor 级数，以精确有理数求和；完整多项式恒等式核对部分分式，再以积分判别法控制整个尾部。三例的独立和式区间均排除零并与 ζ 表达重合。
- 大素数估值公式另对偶数 $n\le120$ 的全部允许 $m$ 检查：818 组参数、15,687 个素数项通过。这些检查辅助审查，统一结论依赖上面的证明。
- 证明审查修正了 $\log\operatorname{lcm}=\psi$ 被误写成 $\vartheta$ 的问题，并补严移位积分的端点误差与无穷尾部。

审计见[主代理独立核验](verification/independent-audit.json)和[线性形式归档核验](verification/linear-audit.json)。
有限样本不证明无穷序列衰减或最终非零；本轮没有开始 Lean 形式化。

## 6. 下一轮的决策依据

预定首轮没有筛出可晋级的主攻候选。下一轮应优先改变有理函数的结构或零点布局。
若沿用本轮已证的整化方法，需要实侧衰减抵消约 8.15–8.86 的算术指数成本；改变构造后必须重新计算两侧成本。
对当前 primitive 形式单纯重复清分母或扩大尺度，没有本轮结果支持的收益。
若继续研究当前族，决定性待证项是含相位的鞍点主项与非零性，而非更多浮点拟合。
这不构成对整个族不可行的证明，也不构成对 ζ(9) 无理性的结论。

## 7. 复现

从工作区根目录运行。脚本自动加载现有 `tmp/zeta7/exact_packages`；Gram 复用现有精确计算器，
并记录实际源码哈希。单例 120 秒，成功项支持断点续跑；全部完整系数均已保存。

```powershell
$py = 'C:/Users/anche/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
& $py missions/zeta9/scripts/attack_linear.py
& $py missions/zeta9/scripts/attack_gram.py
& $py missions/zeta9/scripts/audit_linear.py
& $py missions/zeta9/scripts/independent_audit.py
& $py missions/zeta9/scripts/audit_gram_arithmetic.py
& $py missions/zeta9/scripts/linear_arithmetic_certificate.py --improved --compare-exact missions/zeta9/verification/linear-results.jsonl --output missions/zeta9/verification/arithmetic-improved-certificates.json
& $py missions/zeta9/scripts/linear_saddle.py --certify
& $py missions/zeta9/scripts/build_report.py
```

[机器摘要](verification/summary.json)记录计数与组合界；[文件清单](verification/artifact-manifest.json)记录脚本、笔记和证据的 SHA-256。
