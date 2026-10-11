# 主路线的二次内容分离与最小分母投影

2026-10-02，书面证明及有限精确验证，未运行 Lean。

本稿接续[方向前沿](direction-frontier-2026-10-01.md)。新的无条件算术结论是：
把两行各自的整数内容除去后，中心投影的 Gram gcd 整除“外积内容 × 饱和 Gram
判别式”。它给出能直接用整数 gcd 计算、无需大整数素因数分解的中心分母下界。
另外给出实际同侧坐标区间内分母最小的投影算法。后一个算法改善已验证实例的
分母，但其无限衰减条件仍与无理性等价，不能作为已经解决 J 的新输入。

## 1. 任意整数行对的局部恒等式

先设 u,v∈Z^d，u primitive，且两行线性无关。记

\[
T=\langle u,u\rangle,\ C=\langle u,v\rangle,\ R=\langle v,v\rangle,
\quad G=\gcd(T,C),\quad\Delta=\gcd_{i<j}(u_iv_j-u_jv_i)>0.
\]

令

\[
D_{\rm sat}={TR-C^2\over\Delta^2}
=\sum_{i<j}\left({u_iv_j-u_jv_i\over\Delta}\right)^2\in Z_{>0}.\tag{1}
\]

这是 primitive 外积向量的平方范数，不假设平方自由或模 p 二次型非退化。
本文使用 d=5，但论证适用于任意 d≥2。

固定任意素数 p（包括 2），置 s=v_pΔ。选 j 使 u_j 为 p-adic unit，取

\[
\lambda=v_j/u_j,\qquad w=(v-\lambda u)/p^s\in Z_{(p)}^d.\tag{2}
\]

全部二阶 minor 被 p^s 整除，故 w 的分母与 p 互素且 w_j=0；至少一个 w_i
为 unit，否则全部 minor 被 p^(s+1) 整除。定义 t=v_pT、e=v_p〈u,w〉、
q=v_pD_sat，允许 e=∞。由 C=λT+p^s〈u,w〉 得到

\[
\boxed{v_pG=\min(t,s+e),\quad
v_p\operatorname{den}(C/T)=\max(0,t-s-e).}\tag{3}
\]

gcd 同时包含 T，因此 C 两项之间的额外抵消不能改变该最小值。外积还给

\[
q=v_p\{T\langle w,w\rangle-\langle u,w\rangle^2\}.\tag{4}
\]

p^s/Δ 是 unit，所以 (4) 没有遗漏 Δ 的其他因子。若 t>q，第一项至少有
阶 t>q，故 q=2e；若 t≤q，则 v_pG≤t≤q。于是对全部素数

\[
v_pG\le s+q,\qquad\boxed{G\mid\Delta D_{\rm sat}.}\tag{5}
\]

特别地，p∤ΔD_sat 而 p^t∥T 时 e=0，整个 p^t 留在 C/T 既约分母中。
模块外积内容与饱和平面的二次退化是不同的约分来源；Smith 内容不决定后者。

## 2. 两行内容与一个可计算分母除数

对任意非零独立整数行写 u=g_u u_0、v=g_v v_0，g_v/g_u=b/a 既约且 a,b>0。
两行 u_0,v_0 primitive；T_0,C_0,Δ_0,D_sat 对应它们。原中心为
ξ=(b/a)C_0/T_0，Q=den ξ。置 Q_0=T_0/gcd(T_0,C_0)，则
Q_0/gcd(Q_0,b) 整除 Q：乘 b/a 只能消掉分子 b 支持的旧分母幂次。使用 (5)，

\[
\boxed{\mathcal F={T_0\over\gcd(T_0,b\Delta_0D_{\rm sat})}\mid Q.}\tag{6}
\]

逐素数，v_pQ≥max(0,v_pT_0−v_pgcd(T_0,C_0)−v_pb)，而 (5) 给中间 gcd
阶数≤v_p(Δ_0D_sat)，即得 (6)。a 不进入损失项，因为分母方向的内容不帮助
取消旧分母。这不要求两行内容相同。共同尺度乘正整数时，primitive 两行、
b/a 和 F 均不变，所以该下界是实际行对的不变量。

由[实际第二模态](second-mode-direction-2026-09-29.md)，η_n∼Cηexp[−(α−β)n]，
且原中心 primitive 值 |Q_nθ−P_n| 与 Q_nη_n 最终双向可比。因此

\[
\liminf\log\mathcal F_n/n>\alpha-\beta
\quad\Longrightarrow\quad |Q_n\theta-P_n|\to\infty.\tag{7}
\]

**未证明真实 F_n 满足 (7)。** 它只排除这个指定中心族。若该中心族沿子序列
衰减，F_nη_n→0 是必要条件；并非所有整数形式衰减的必要条件。
即使 D_sat 总高度很大，也不决定 gcd(T_0,bΔ_0D_sat) 在 T_0 上的共同质量。

## 3. 不使用 θ 数值的同侧真实区间

真实加权有理行记 U_n,V_n，取 r_{j,n}=V_{n,j}/U_{n,j}，j=0,1。
[第二模态坐标定理](second-mode-direction-2026-09-29.md)给

\[
r_{j,n}-\theta={c\over a}{p_{B,j}\over p_{A,j}}
(-B/A)^{n/2}(1+O(n^{-1})).\tag{8}
\]

此处 a,c 为实模态振幅，与 §2 内容 a,b 无关。写
Q(y)=∏_{i=2}^4(y−y_i)=q_0+q_1y+q_2y²+y³，q_i>0。已隔离的根满足
y_0>0、y_1<0，p_A=(y−y_1)Q，p_B=(y−y_0)Q。因此

\[
{p_{B,0}\over p_{A,0}}={y_0\over y_1}<0,\qquad
{p_{B,1}\over p_{A,1}}-{p_{B,0}\over p_{A,0}}
={q_0(y_1-y_0)\over y_1(q_0-y_1q_1)}>0.\tag{9}
\]

p_{B,1}<0 已由根区间严格认证。故这两个系数比为不同的负数。
I_n=[min(r_0,r_1),max(r_0,r_1)] 对全部充分大偶数 n 满足

\[
\theta\notin I_n,\quad c_1\eta_n\le|I_n|\le c_2\eta_n,
\quad c_3\eta_n\le|x-\theta|\le c_4\eta_n\quad(x\in I_n),\tag{10}
\]

全部 c_i 为固定正数。区间每次 n→n+2 翻到 θ 的另一侧。端点由有理矩阵
直接给出，不使用 θ 小数；全参数 (10) 来自模态证明。横跨 θ 的区间不能
替代它：有理分支中跨越区间可能选中零形式，破坏最终非零性。

## 4. 精确最小分母 witness 与 rank-one 投影

对正有理闭区间 [l,r]，从 Stern–Brocot 父端点 L=0/1、R=1/0 开始，不断
试 mediant，多次同向移动用整数除法加速，保持 L<l≤r<R。第一次进入区间的
x=(p_L+p_R)/(q_L+q_R)=p/q 已既约，且 q 为区间内全部有理数的最小分母。
其证书是

\[
p_Rq_L-p_Lq_R=1,\qquad L<l\le x\le r<R.\tag{11}
\]

任意既约有理数 z 在父端点之间，都可写为
`(k p_L+j p_R)/(k q_L+j q_R)`，其中 k,j 是正整数：它们是该 unimodular
基的整数坐标，位置的严格夹逼使两个坐标为正。故分母至少 q_L+q_R。
算法有限终止，因为预选的区间内有理数之分母限制所有继续包围它的父端点
分母。一开始右端点为 ∞ 时最多先做一次整数左移；右端点有限之后，父端点
分母和每一步严格增长。

该 witness 可实现移动有理 metric 投影。取共同正尺度把 U,V 写成整数 u,v；
令 j,k 为按 r_j≤r_k 排序的 0,1 坐标。充分大时 u_j,u_k>0，置

\[
\ell_j=qv_k-pu_k\ge0,\quad\ell_k=pu_j-qv_j\ge0,
\quad\ell_i=0\ (i\ne j,k).
\]

δ=u_jv_k−u_kv_j>0，u·ℓ=qδ、v·ℓ=pδ。正半定 H=ℓℓᵗ 给

\[
{\langle U,HV\rangle\over\langle U,HU\rangle}=p/q.\tag{12}
\]

输出 qθ−p primitive，且由 (10) 最终严格非零。H 允许 rank one，未声称
保持原 Euclidean 格的极小值。q 是该区间内所有非负两坐标 rank-one 投影
的最低可能分母；它主动绕过原中心的完整二次分母 Q。

## 5. 新算法的无限条件仍等价核心障碍

右父端点有限时，(11) 给 |I|≤R−L=1/(q_Lq_R)，因此

\[
|I|q\le1/q_L+1/q_R.\tag{13}
\]

算法及最优性已证明；真实无限序列的父分母行为仍需要新输入。
事实上若 θ 无理，由 (10) 有 p_n/q_n→θ，故 q_n→∞。两个父分母的最小值
也趋∞：否则沿子序列一个分母有界，另一个趋∞，父端点间隙趋零；在 θ
的有界邻域内，分母有界的父端点只能取有限多个有理数，因此某固定有理数
必须等于 θ，矛盾。充分大时右父端点必有限。由 (10),(13)，q_nη_n→0。
反之若 θ=c/d 有理，则 θ∉I_n、|p_n/q_n−θ|≤c_4η_n 强制
q_nη_n≥1/(dc_4)>0。所以严格有

\[
\boxed{\theta\notin Q\iff q_n\eta_n\to0
\iff|q_n\theta-p_n|\to0.}\tag{14}

\]

`min(q_L,q_R)→∞` 同样与无理性等价：若其成立，(13) 给形式衰减；若 θ
无理，前段已经证明。观察有限指数或直接援引 θ 的无理连分数理论保证
父分母增长，都不能当作非循环关闭 J。

原中心 Qη 衰减仅是充分条件，未证明无理性必使其衰减；本区间族在无理
分支确实全序列衰减，但该分支正是未解决输入。§§1–2 则是独立的新算术结论。

## 6. 有限证书与下一项输入

[verify_direction_arithmetic_next.py](../scripts/verify_direction_arithmetic_next.py)
从独立 F₂ 和真实连接验证 n=2,12,20,48,96,192。六个真实行对满足 (1)–(6)，
各有 15 个小素数检查，共 90 项；另有 358 个标准库随机整数行对、2864 项
局部检查，以及 160 个区间的全体较小分母穷尽检查。

| n | log F_n/n | log Q_n/n | log q_n/n | log abs(q_nθ−p_n)/n |
|---:|---:|---:|---:|---:|
| 48 | 20.8963972673 | 30.2805837642 | 5.0669085804 | −5.0037462380 |
| 96 | 21.3509778293 | 30.2465986750 | 5.0610840229 | −5.0304043899 |
| 192 | 21.4749505879 | 30.8839951361 | 5.0587610966 | −5.0427771048 |

六个新 witness 均由 Arb 严格认证 `0<abs(qθ−p)<1`，并验证两端点同侧。
完整 primitive Gram、行内容、局部阶数、区间端点、Farey 父端点及整数 ℓ
保存于[证书](../verification/direction-arithmetic-next-2026-10-02/certificate.json)
及[摘要](../verification/direction-arithmetic-next-2026-10-02/summary.json)。
有限证据不承担无穷量词。原中心的下一项额外输入是 (7) 的真实 gcd 质量界；
更小分母族的下一项是排除父分母最终有界，它与固定零方向出口等价，不应
重复计作新的独立问题。本稿未证明全部移动投影失败，未关闭 J、S、CP 或
ζ(9) 无理性；未修改 status/scope，未提交外部结果。

## 7. 本轮独立交叉审阅

本审阅者另分别阅读全文并重构以下三份同轮稿的主要证明；全部通过，无数学
修补要求。这里不把其他作者的脚本运行写成本审阅者自己的运行。

- [增长维数 rank-one 路线](growing-rank-one-route-2026-10-02.md)：最后一条
  X-moment 为 1，monic Schur norm 与 primitive T_hX−U_h 正确；密度上界、
  h 缩放、右端 Riemann 和和 Legendre 首一范数给 f_c−log16 到 f_c 的真实
  error 夹逼。α↓0 的量词顺序及两个严格 denominator thresholds 合法。
  没有把 raw error 指数当作 primitive 衰减，未偷用 J。
- [隔离七阶导数形式](new-linear-form-route-2026-10-02.md)：首边界 16/15
  与中间/无限尾全部误差控制正确。中间估计必须用已写出的 exact g'_k
  cancellation，避免额外 n^(2ρ) 损失。d_nB 的 Legendre carry 证明包含
  小素数；Lucas 的 carry 分支也使 A 单项至少有阶 2，故 p^9b≡(9/2)A_r。
  full primitive c 的分母整除 A_n，product-good-primes/A_n 下界及条件
  exception threshold 正确；该 exception mass 尚未估到阈值以下。
- [一阶任意分散极点分类](dispersed-pole-frontier-2026-10-02.md)：odd-tail
  Laurent 正性、top-two Rolle 条件和 top-four 精确乘积约束正确；m=5 三
  分支的两个有色素数区间以及全部常数反证覆盖精确零 tail 异常。有限颜色
  整数分子的固定幂高度排除只损 O(log b)，primitive 标量分母 |B 和正积分
  下界也只损 O(log b)。因此全部 m 的 uniform 整数位置量词成立。
