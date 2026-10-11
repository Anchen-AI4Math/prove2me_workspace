# VB 的逐素数推进：平移迹消去与小素数截断

本稿给出两个对参数统一成立的结论：大素数部分满足
`limsup H_n/n <= 1/2`；`p <= sqrt(7n/2)` 对小素数超额的贡献为
`o(n)`。证明使用第五轮整性与第七轮子式恒等式，不依赖有限审计的外推。
这尚未证明 VB：余下的小素数超额仍须控制。

## 1. 定义

沿用 `arithmetic-prime-budget.md`：`n >= 2` 为偶数，
`d_n=lcm(1,...,n)`，`q=d_n^9`，`A=qF_n` 为整数矩阵；
`F_n` 的行对应 `1,u,...,u^4`，列次序为 `(B,A_3,A_5,A_7,A_9)`。
令 `delta_3` 为低 ζ 三列的三阶子式 gcd，`delta_4^*` 为含这三列的
混合四阶子式 gcd。第七轮已证

\[
 N_n=\frac{|\det A|\delta_3}{(\delta_4^*)^2},\qquad
 \delta_3\mid\delta_4^*,\qquad
 \det F_n=\frac{(3n/2)!(7n/2)!}{7n((n/2)!)^{10}}.                 \tag{1}
\]

以下把形式系数 `A_s(W)` 与矩阵 `A` 区分使用。

## 2. 平移迹引理：整列的模素数消去

**命题。** 设 `n >= 8` 为偶数，`p > n` 为素数，`W in Z[u]`、
`deg W <= 4`。对 `s in {3,5,7}`，有

\[
 (s-1)p<7n\quad\Longrightarrow\quad A_s(W)\in p\mathbb Z_{(p)}. \tag{2}
\]

这里 `Z_(p)` 是分母与 `p` 互素的有理数环。尤其 (2) 同时适用于五个单项式，
故是完整低 ζ 列的整除结论。

**证明。** 令

\[
 Q_n(t)=\prod_{j=0}^n(t+j),\quad u=t(t+n),\quad
 f(t)=R_n(t)W(u),\quad
 R_n(t)=n!^7\frac{(t-n)_n(t+n+1)_n}{Q_n(t)^9}.
\]

因 `p>n`，极点互异模 `p`，其部分分式系数均属 `Z_(p)`；这也直接由
第五轮的 `d_n^{9-s}c^W_{j,s} in Z` 得到。可把恒等式整体约化到 `F_p(t)`。
下文所有系数与多项式都在 `F_p` 中。

置 `H(t)=t^p-t`。`Q_n` 的互异根都属于 `F_p`，故 `Q_n|H`，于是

\[
 P(t)=H(t)^9f(t)
 =n!^7(t-n)_n(t+n+1)_nW(u)(H/Q_n)^9\in\mathbb F_p[t],
\]

\[
 \deg P\le 2n+8+9(p-n-1)=9p-7n-1.                         \tag{3}
\]

对任意多项式 `P`，定义平移迹
`Tr(P)(t)=sum_{a in F_p}P(t+a)`。因
`sum_a a^k=0` 对 `0<=k<p-1` 成立（`k=0` 时和是 `p=0`），逐单项式展开给出

\[
 \deg\operatorname{Tr}(P)\le\deg P-(p-1)\le8p-7n,           \tag{4}
\]

其中右端若为负则迹为零；零多项式也按满足该度数上界理解。

对 `1<=s<=9<p`，从

\[
 \sum_{a\in\mathbb F_p}\frac1{t+a}=\frac{H'(t)}{H(t)}=-\frac1{H(t)}
\]

求 `s-1` 次导数，利用 `H'=-1` 和 `(s-1)!` 可逆，得到

\[
 \sum_{a\in\mathbb F_p}\frac1{(t+a)^s}=\frac{(-1)^s}{H(t)^s}. \tag{5}
\]

部分分式 `f=sum_{j,s}c^W_{j,s}/(t+j)^s` 中，反射使偶数阶的总系数为零，
且无穷远衰减给出一阶总系数为零。因此 (5) 与平移置换 `F_p` 给出

\[
 \operatorname{Tr}(f)
 =-\frac{A_3(W)}{H^3}-\frac{A_5(W)}{H^5}
   -\frac{A_7(W)}{H^7}-\frac{A_9(W)}{H^9}.                 \tag{6}
\]

又 `H(t+a)=H(t)`，所以 `Tr(P)=H^9 Tr(f)`，即

\[
 \operatorname{Tr}(P)
 =-A_3(W)H^6-A_5(W)H^4-A_7(W)H^2-A_9(W).                 \tag{7}
\]

右边四种非零项的最高次数分别为 `6p,4p,2p,0`，互不相同。
依次从最高项比较 (4)：当 `2p<7n` 时 `A_3=0`；当 `4p<7n` 时
前者已零且 `A_5=0`；当 `6p<7n` 时前两者已零且 `A_7=0`。
这正是 (2)。证明全程对全部整数四次 `W` 同时成立。证毕。

## 3. 大素数指数至多一，且支持不超过 3n/2

**定理。** 对每个偶数 `n>=8` 及每个素数 `p>n`，

\[
 \boxed{\quad v_p(N_n)\le\left\lfloor\frac{3n}{2p}\right\rfloor.\quad} \tag{8}
\]

**证明。** 若 `p>7n/2`，第七轮的素数支持定理已给 `v_p(N_n)=0`。
其余情形令

\[
 k=\left\lfloor\frac{7n}{2p}\right\rfloor\in\{1,2,3\}.
\]

对 `j=1,...,k`，有 `2jp<=7n`，而等号不可能：
若相等，则 `p|7n`；`p>n>=8` 排除 `p|n` 与 `p=7`。
于是 (2) 表明列 `A_3,...,A_{2k+1}` 全部被 `p` 整除。
`p` 不整除 `q`，故这也是整数矩阵 `A=qF_n` 的列整除。
任何低 ζ 三阶子式都含这 `k` 列，因而

\[
 v_p(\delta_3)\ge k.                                      \tag{9}
\]

另一方面，`p^2>7n/2`、`p` 不整除 `7n` 或 `q`。阶乘闭式 (1) 精确给出

\[
 v_p(\det A)=\left\lfloor\frac{3n}{2p}\right\rfloor+k.      \tag{10}
\]

由 `delta_3|delta_4^*` 与 (1)，

\[
 v_p(N_n)
 =v_p(\det A)+v_p(\delta_3)-2v_p(\delta_4^*)
 \le v_p(\det A)-v_p(\delta_3)
 \le\left\lfloor\frac{3n}{2p}\right\rfloor.
\]

证毕。特别地，`p>n` 的指数只可能为 `0` 或 `1`，并且

\[
 \prod_{p>n}p^{v_p(N_n)}\ \mid\ \prod_{n<p\le3n/2}p,
 \qquad
 \boxed{\ \mathcal H_n\le\theta(3n/2)-\theta(n).\ }        \tag{11}
\]

这把第七轮有限观察的 `3n/2` 支持界提升为所有偶 `n>=8` 的定理。
有限的 `n=2,4,6` 不影响以下极限；此处没有未经检查声称它们也满足 (8)。
素数定理给出

\[
 \boxed{\ \limsup_{2\mid n,\ n\to\infty}\mathcal H_n/n\le\tfrac12.\ } \tag{12}
\]

## 4. 小素数幂的显式余量界

置 `x_n=7n/2`、`Y_n=sqrt(x_n)`。对偶 `n>=4` 有 `Y_n<=n`。
令

\[
 \mathcal E_n^{\rm small}
 =\sum_{p\le Y_n}(v_p(N_n)-11\lfloor\log_p n\rfloor)_+\log p.
\]

第七轮的统一界为
`v_p(N_n)<=45a_p+8b_p`，其中
`a_p=floor(log_p n)`、`b_p=floor(log_p x_n)`。由 `a_p<=b_p`，

\[
 (v_p(N_n)-11a_p)_+\log p
 \le(34a_p+8b_p)\log p\le42\log x_n.
\]

素数个数至多 `floor(Y_n)`，所以有完全显式且无需素数定理的界

\[
 \boxed{\quad
 0\le\mathcal E_n^{\rm small}
 \le42\lfloor\sqrt{7n/2}\rfloor\log(7n/2),\qquad
 \mathcal E_n^{\rm small}/n\longrightarrow0.
 \quad}                                                    \tag{13}
\]

该结论允许随 `n` 增长的整个小素数集合；比只剥离固定有限素数集更强。

## 5. VB 现在剩下什么

设

\[
 \mathcal E_n^{\rm large}
 =\sum_{\sqrt{7n/2}<p\le n}(v_p(N_n)-11)_+\log p.
\]

这些素数满足 `p^2>7n/2`，故 `a_p=1`，没有更高素数幂的 Legendre 项。
式 (13) 说明
`limsup E_n/n = limsup E_n^large/n`。结合 (12)，以下单一剩余条件足以完成 VB：

\[
 \boxed{\quad
 \limsup_{2\mid n,\ n\to\infty}\frac{\mathcal E_n^{\rm large}}n
 <\left(2\tau-\tfrac12\log(3\,711\,015\,000)-9\right)-\tfrac12
 \approx0.61071437.
 \quad}                                                    \tag{14}
\]

**(14) 尚未证明。**

冻结的五个完整素因子分解给出 `E_large/n` 约为 `0, 0, 0.065323, 0.111946, 0.061317`（依次对应 `n=12,24,48,96,192`）。这些仅是有限诊断，不给出 (14) 的上极限界。

为把待证的局部估值写得精确，令

\[
 D_{n,p}=\lfloor3n/(2p)\rfloor+\lfloor7n/(2p)\rfloor
          -10\lfloor n/(2p)\rfloor-v_p(7n),\qquad
 C_{n,p}=2v_p(\delta_4^*)-v_p(\delta_3).
\]

对 `sqrt(7n/2)<p<=n`，(1) 精确给出

\[
 (v_p(N_n)-11)_+=(34+D_{n,p}-C_{n,p})_+.                   \tag{15}
\]

因此剩余任务是对这些局部子式消去量 `C_{n,p}` 给出足够强的统一下界，
或直接证明 (15) 的加权总和满足 (14)。平移迹证明不能直接照搬到 `p<=n`：
`Q_n` 的根在模 `p` 下重合，`Q_n` 不再整除 `t^p-t`，且原始部分分式
系数可能含 `p` 分母。必须先控制这些合并极点及其归一化，不能沿用第 2 节
的约化步骤。这是本稿尚未跨过的最窄算术障碍。

任何有限参数中 (14) 的小值都不作为渐近证明。新增理论结论是 (2)、(8)、
(11)–(13)；VB 本身保持开放。

## 6. 独立有限交叉检查

[标准库脚本](../verification/check_prime_valuation_attack.py) 与
[精确证书](../verification/prime-valuation-attack-audit.json) 记录以下检查：

- 从原始有理乘积独立重建 `n=8,10,12` 的五个完整形式向量，计算全部所需子式
  与 `N`，不用旧的部分分式生成器。
- 读取且不修改冻结的 `n=12,24,48,96,192` 数据，检查整列模 `p` 消去、
  `delta_3,delta_4^*` 估值及 (8)；与新生成的 `n=12` 逐坐标精确相等。
  新旧案例合计检查 187 个 `(n,p)`。
- 对 `n=8`、`p=11,13,17,23,29`、`r=0,...,4`，直接构造
  `P=H^9 R_n u^r`，逐系数核对 (7) 的 25 个有限域多项式恒等式和 (4) 的度数界。
  `p=11` 是定理范围内最小可能的素数；此时至多八次求导的阶乘仍可逆。
- 脚本只写本目录的新证书，输入与脚本 SHA-256 随证书保存，无网络调用。

执行命令为 `python missions/zeta9/roadmap/verification/check_prime_valuation_attack.py`，
结果为 `passed`。这些检查核对实现、符号和边界；参数统一结论由第 2–4 节证明承担。
