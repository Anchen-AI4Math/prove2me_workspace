# 奇数模型的真实连接与全部三维局部模型非奇异性

2026-09-29。本文从原始有理函数构造奇数参数的完整五维连接，并以其真实逆外积的有理窄锥证明：**所有正奇数 m 的局部矩阵 M_m 均非奇异。** 无穷参数结论来自多项式恒等式与全参数系数证书，不是有限模型扫描的外推。

M_m 沿用[奇数锚点稿](odd-anchor-extension-2026-09-29.md)的定义，行按 s=3,5,7，列按 w,w³,w⁵：

\[
 G_m(t)=\frac{(t-m)_m(t+m+1)_m}{\prod_{j=0}^m(t+j)^9},
 \quad w=2t+m,\qquad (M_m)_{s,r}=2\sum_j d_{j,s}(w^r).
\]

**定理。** 对每个正奇数 m，

\[
                 \boxed{(-1)^{(m+1)/2}\det M_m>0.}       \tag{1}
\]

暂缓 Lean；本文不证明 S、J 或 ζ(9) 无理性，也不把这套辅助奇数模型当作原来的偶参数形式格。

## 1. 奇数参数的完整形式矩阵

令 n 为正奇数，使用包含阶乘的核

\[
 R_n(t)=n!^7G_n(t),\quad u=t(t+n),\quad w=2t+n,
 \qquad\widetilde R_n(t)=wR_n(t).
\]

R_n 在 t↦−n−t 下对称，而 w 反对称，故 Rtilde_n 反对称。对 r=0,…,4，令 Ftilde_n 的第 r 行为 `Rtilde_n(t)u^r` 的完整形式向量，列为 `(B,A3,A5,A7,A9)`。反射消去偶数 ζ；无穷远至少 O(t^(−7n)) 消去一阶总残数，级数绝对收敛。常数项按原始部分分式精确取为

\[
 B=-\sum_{j=0}^n\sum_{s=1}^9 c_{j,s}H_j^{(s)}.
\]

此处不预设 Ftilde_n 可逆，也不使用 ζ 值的线性无关性。独立原始部分分式计算给

\[
                        \det\widetilde F_1=64.           \tag{2}
\]

## 2. 新离散原函数与全形式边界

沿用[真实偶连接稿](../round7/research/connection.md)的

\[
 D_n(u)=(u-n-1)^{10},\quad c_n=[(n+1)(n+2)]^7,\quad
 Z_n(u)=\prod_{a=1}^3\{u-(n+a)(2n+a)\}.
\]

中心对齐后，`2(t−1)+(n+2)=2t+n`，所以附加线性因子完全消去：

\[
 \frac{\widetilde R_{n+2}(t-1)}{\widetilde R_n(t)}
       =\frac{c_nZ_n(u)}{D_n(u)}.                       \tag{3}
\]

对 q∈Q[v]、deg q≤9，v=t(t+n−1)，定义

\[
 Q_q(t)=R_n(t)\frac{t-n-1}{(t-1)^{10}}q(v),\qquad
 \widetilde Q_q(t)=(2t+n-1)Q_q(t).                     \tag{4}
\]

记

\[
 L_a=(t-n-1)(t+n+1)^{10}[t(t+n-1)]^a,\quad
 T_a=(t+2n+1)(t-1)^{10}[(t+1)(t+n)]^a.
\]

直接相减得到

\[
 \frac{\widetilde Q_{v^a}(t)-\widetilde Q_{v^a}(t+1)}
      {\widetilde R_n(t)}
 =\frac{\widetilde H_{n,a}(u)}{D_n(u)},\qquad
 \widetilde H_{n,a}=
 \frac{(2t+n-1)L_a-(2t+n+1)T_a}{2t+n}.                \tag{5}
\]

在反射 t↦−n−t 下 L_a↦−T_a，新分子反对称，商对称。脚本进一步在 Z[n,t] 中逐项精确除以 2t+n，再按 u 的幂消元，认证全部十个 Htilde∈Z[n,u]。最高项为

\[
 \deg_u\widetilde H_{n,a}=5+a,\qquad
 [u^{5+a}]\widetilde H_{n,a}=7n+17-2a>0
       \quad(n\ge1,\ 0\le a\le9).                   \tag{6}
\]

边界对 n=1 也成立。原函数 (4) 的整数极点仅可能为 1,0,…,−n；在 t=2，`(t−n−1)_n` 有零点，故 Qtilde_q(2)=0；在无穷远，Qtilde_q(t)=O(t^(1−7n))→0。

因此差分从 t=2 起求和为零，而且是**完整形式向量逐一为零**：每阶极点的系数总和因整数平移相消，常数项等于零边界 Qtilde_q(2)。只以实数总和等于零不足以推断形式相等，这里使用的是部分分式平移恒等式。旧核缺少的 t=1 项本来为零。

## 3. 全参数有理连接与正行列式

对每个 r=0,…,4 求多项式恒等式

\[
 c_nZ_n(u)(u-n-1)^r
 =D_n(u)P_r(u)+\widetilde H_n(q_r)(u),\quad
 \deg P_r\le4,\ \deg q_r\le9.                       \tag{7}
\]

这仍是固定的 15×15 系统。令 A_old 的列按 `D_nu^0,…,D_nu⁴,Htilde_0,…,Htilde_9` 排列，系数行按 u⁰,…,u¹⁴；A_new 替换前五列为 (7) 的左边。精确无分母消元得到

\[
 \det A_{\rm old}=n^{10}(n+1)^{55}(n+2)^{45},         \tag{8}
\]

\[
 \det A_{\rm new}=21 n^{10}(n+1)^{47}(n+2)^{45}
 (3n+5)(3n+7)\!\prod_{b\in\{-1,1,3,5,9,11\}}(7n+b).
                                                               \tag{9}
\]

两者对所有实数 n≥1 均为正；脚本还直接检验 n=1+t 展开全部系数非负且常数正。消元产生的 75 个系数多项式恒等式逐一精确复核，因此连接行 P_r 是有理函数的确切解。

定义 Ctilde(n) 的第 r 行为 P_r 系数。由 (3)、(5)、(7) 及上述完整形式边界：

\[
 \boxed{\widetilde F_{n+2}=\widetilde C(n)\widetilde F_n,\quad
 \det\widetilde C(n)=
 \frac{21(3n+5)(3n+7)\prod_{b\in\{-1,1,3,5,9,11\}}(7n+b)}{(n+1)^8}>0.} \tag{10}
\]

这不循环使用 Ftilde 可逆性：先由 (8) 解出系统，再由 (2) 与 (10) 归纳证明所有正奇数 Ftilde 可逆且行列式为正。令 n=2h+1，连乘还给

\[
 \boxed{\det\widetilde F_{2h+1}
       =\frac{16(3h+2)!(7h+2)!}{(h!)^{10}},\quad h\ge0.} \tag{11}
\]

闭式可直接以 h=0 初值和相邻商 (10) 核验。

## 4. 与偶数连接相同的加权极限

Htilde_a 与旧 H_a 的差为 `−(L_a+T_a)/(2t+n)`，比旧最高总齐次项低一阶。因此令 y=u/n²，

\[
 n^{-11-2a}\widetilde H_{n,a}(n^2y)
 \longrightarrow y^a(-1-9y-26y^2-23y^3+5y^4+7y^5).
\]

旧、新输入的最高齐次项保持 y^(10+r)、(y−2)³y^r。故

\[
 \widetilde G_n=W_n^{-1}\widetilde C(n)^{-1}W_{n+2}
      \longrightarrow G,
\]

其中 G 与实际偶数连接的极限完全相同。脚本同时由已解 Ctilde 的最高次系数独立重建该极限，并逐元素对照旧证书。

这只说明可继续使用同一固定有理 Vandermonde 坐标 V。奇数连接的有限 n 矩阵不同，所以不能直接沿用偶锥不等式或偶初值。下面对奇数连接重新构造全部证书。

## 5. 真正奇连接的窄外积锥

令 Etilde_n 取 Ftilde_n⁻¹ 的第 0、4 行，Ebar_n=Etilde_n W_n。完全沿用[外积锥稿](exterior-cone-2026-09-29.md)给定的精确有理 V 与十个二元指标顺序，定义

\[
 \widetilde T(n)=-\wedge^2(V^{-1}\widetilde G_nV),\qquad
 z_n=\wedge^2(\bar E_nV),\qquad z_{n+2}=-z_n\widetilde T(n).
\]

新证书采用 N=51、q=10000。Ctilde 的公共分母为
`d(n)=(n+1)¹⁰(n+2)⁸`，令 P(n)=d(n)Ctilde(n)。Jacobi 互补三阶子式乘以 `n^(14−2ΣI)(n+2)^(2ΣJ)`，再换基并约去正公共因子，产生一个 **30 次整系数多项式矩阵** p(n)，满足

\[
 p(n)=s(n)\widetilde T(n),\qquad
 s(n)=\frac{d_Ld_R n^{14}\det P(n)}{c\,g(n)d(n)^2}>0
       \quad(n\ge51).                                \tag{12}
\]

d_L,d_R 为两个固定外积换基的正整数清分母，c 为正整数内容，g 为取正首项的公共多项式因子。证书精确验证 g(51+t)、det P(51+t) 逐系数非负且常数正，因而清因子不改变锥的方向。

在 n=51+t 展开 `p_ij=Σ_k c_ijk t^k`，所有 k=0,…,30 都满足

\[
 L_k=q c_{00k}-\sum_{i=1}^9|c_{i0k}|>0,\qquad
 L_k-q^2|c_{0jk}|-q\sum_{i=1}^9|c_{ijk}|\ge0
       \quad(j=1,\ldots,9).                           \tag{13}
\]

这些整数不等式和 t≥0 证明对**全部实 n≥51**，Ttilde(n) 保持

\[
 \mathcal C_* =\{x:x_0>0,\ |x_j|\le10^{-4}x_0\}.
\]

正标量 (12) 在齐次不等式中消去。此处只须保锥，不需要新的射影收缩定理。

## 6. 真实初值、Jacobi 指定子式与模型归一化

Ftilde_51 从原始因子逐项 Taylor 展开独立重建，未用连接运输来假定它进入锥。精确有理证书给

\[
 z_{51,0}<0,\qquad
 \max_{j\ge1}|z_{51,j}/z_{51,0}|
       =0.0000910077060476\ldots<10^{-4}.              \tag{14}
\]

置 `x_n=−(−1)^((n−51)/2)z_n`，则 x51∈C_*，且 x_(n+2)=x_n Ttilde(n)。由 (13)，所有奇数 n≥51 上 x_n∈C_*。

令 `r_i=(∧²V⁻¹)_(i,34)`。固定坐标恢复列再次经有理数计算认证

\[
 r_0>0,\qquad
 r_0-10^{-4}\sum_{i=1}^9|r_i|
       =0.000811175174891304\ldots>0.                 \tag{15}
\]

因此指定的原始外积坐标 `Σ_i z_(n,i)r_i=(∧²Ebar_n)_(34)` 非零，符号为 `−(−1)^((n−51)/2)`。令

\[
 \widetilde\Delta_n=\det\widetilde F_n[\{0,1,2\},\{1,2,3\}].
\]

Jacobi 的符号为 `(−1)^(0+1+2+1+2+3)=−1`，故

\[
 \widetilde\Delta_n=-\det\widetilde F_n\,n^{-14}
                         (\wedge^2\bar E_n)_{34}.    \tag{16}
\]

由于 (11) 为正，得到 `sign Δtilde_n=(−1)^((n+1)/2)`。

最后必须对齐原始 M_n，不能漏掉其系数 2 或阶乘。由

\[
 w^{2r+1}=w(4u+n^2)^r\quad(r=0,1,2),
\]

相应三角换基 T 的对角元为 1,4,16。R_n=n!⁷G_n，且 M 的行列约定与 Ftilde 的低三块转置，故

\[
 M_n=\frac2{(n!)^7}
       \left(T\widetilde F_n[\{0,1,2\},\{1,2,3\}]\right)^{\mathsf T},
 \qquad
 \boxed{\det M_n=\frac{512}{(n!)^{21}}\widetilde\Delta_n.} \tag{17}
\]

于是 (1) 对所有奇数 n≥51 成立。剩余 n=1,3,…,49 从各自原始部分分式重建并精确核验符号，连同初值共 26 例；其中 n≤19 的全部模型行列式与既有证书一致，n=1,3,5 的完整 M 矩阵也一致。这补齐起点以下的有限集合，完成全参数证明。

## 7. 复现、审核范围与后续应用的量词

两个独立脚本分别承担代数连接和外积锥：

- [verify_odd_model_connection.py](../scripts/verify_odd_model_connection.py)：十个整数对称生成元、两个 15×15 行列式、75 个完整多项式恒等式、同 G 极限，以及 n=1,3,5 的原始完整形式连接比较。
- [verify_all_odd_models.py](../scripts/verify_all_odd_models.py)：全实参数 n≥51 的 30 次锥证书、正标量、指定恢复坐标支配、真实 Ftilde_51 初值与完整有限前缀。

输出是 [symbolic.json](../verification/odd-model-connection-2026-09-29/symbolic.json) 和 [all-odd-models.json](../verification/odd-model-connection-2026-09-29/all-odd-models.json)，均已通过。本稿没有修改既有连接、status 或 scope。

结合[全部偶模型定理](all-even-models-2026-09-29.md)，所有固定正整数块所需三维模型现均非奇异。局部应用仍应先固定有限块截断，再排除这有限多个模型产生的有限坏素数，最后令截断趋于无穷；不能将所有模型坏素数的无限并集称作有限集合。这一成果补齐局部模型非退化假设，不自动证明整数方向变化或 ζ(9) 无理性。

独立审核记录：`independent_audit` 已全文审核并顺序重跑两个脚本，全部通过；另逐项复核当前三条哈希链、26 个 Ftilde 阶乘闭式、26 个模型的 512/(m!)²¹ 归一化。重点确认了完整形式边界、非循环可逆性、N=51 的全参数窄锥、(3,4) 恢复列严格支配和最终符号。
