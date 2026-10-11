# 实际有理函数的有限与无穷求和：p=9、q=1、m=n

本环使用已冻结的真实 `weightedR`、全部实际局部系数、全局部分分式、反射消去和有限求和证明。没有重新定义局部系数，也没有把 rho 消去、zeta 身份或收敛性作为输入假设。

`formalization/CoefficientMapSummation.lean` 采用较强次数域

`2*n + 2*W.natDegree ≤ 9*(n+1)-2`。

在此域内，原反射文件已证明实际 `rho_1=0`。再加 `Even n`，实际 `rho_2,rho_4,rho_6,rho_8` 均为零，因此有限求和文件的条件化恒等式变为无额外消去假设的恒等式：实际从 1 到 T 的 `weightedR` 求和等于 `B + rho_3 H_T^(3) + rho_5 H_T^(5) + rho_7 H_T^(7) + rho_9 H_T^(9) + shiftedTail`。

对于 s>1，文件从 Mathlib 的 `zeta_nat_eq_tsum_of_gt_one`、`Complex.ofReal_tsum` 和实际实数 p 级数证明 `H_T^(s)` 趋于 `(riemannZeta (s:ℂ)).re`。全部固定 j 的调和尾差均从实际有限区间身份展开，每一项 `1/(T+k)^s` 在 s≥1 时趋于零。因此实际尾项趋于零，包含 s=1 的局部项；这一步不要求次数界或偶数 n。

无穷求和的索引是 `t:ℕ ↦ weightedR n W (t+1)`，对应正整数 1,2,3,...，每一求值点均正式证明没有极点。文件首先证明实际绝对可和性，再证明 HasSum 和 tsum 身份：

* s≥2 的移位项由实际 p 级数和注入移位映射证明 Summable。
* s=1 的实际部分分式项使用已证明的 `rho_1=0` 重写为 `c_j,1*(1/(t+1+j)-1/(t+1))`。差等于 `-j/((t+1)*(t+1+j))`，其范数被 `j/(t+1)^2` 控制。
* 有限个上述实际项相加给出 `Summable actualSeries`；实数空间中的 `Summable.norm` 给出 `Summable (‖actualSeries‖)`。
* 在实际 Summable 已证明后，才将其真正 HasSum 的自然数部分和极限与实际有限 L 的极限比较，得到精确 HasSum/tsum。

实际结果为

`Σ_(t≥1) weightedR n W t = B + rho_3 ζ(3) + rho_5 ζ(5) + rho_7 ζ(7) + rho_9 ζ(9)`，

右边的 B 和 rho 都是已定义实际局部系数的有理有限和；ζ 的实数值取上述 Mathlib 函数的实部。不是仅凭自然数部分和极限宣称任意实数级数 HasSum。

原偶数 n≥2、整数系数 quartic W 的包装定理正式由旧文件的较强次数界推导新 HasSum，完全没有 rho 或收敛输入假设。n=0、W=1 也在较强域内，并有实际 HasSum 检查。n=0、W=X⁴ 的边界另行检查：它满足严格 proper 界，却不满足较强界；实际 rho_1=1，且正整数项为 `1/(t+1)`。本证明从未用严格 proper 界代替较强界。

本环闭合了原 d=0、p=9、单层 q=1、m=n、偶数 n≥2 的整数 quartic 情形的实际 Eq(4) 无穷 L 身份及绝对可和性。一般 p、多层或 d>0 的求和、原分母整性、聚合后的五维 F 的可逆性、指定整数输出的逆像与由此得到的指定目标 L 仍未完成。本环不推出 zeta(9) 无理性。

完整源码和单独导入的类型审计使用根共享 Mathlib 缓存编译，只有新的 mission 源/object/审计/说明文件写入。六份旧数学源、旧 objects/receipts、共享根模块、scope、API 和凭证均不改。

本轮保留了一次导入路径错误的实际 exit 1 记录：在 `lake env pwsh` 内部把根源目录强行放在 `LEAN_PATH` 最前会遮蔽正式 Definitions 缓存。最终调用在外层 PowerShell 先设置根目录为继承前缀，再运行 `lake env lean`；Lake 先加入正式 `.lake/build/lib/lean`，纯 `Def_ZetaNine_HarmonicStability` 从那里读取，而 mission 模块从根源目录读取。这是导入路径修正，没有修改或重新构建旧证明或数学依赖。
