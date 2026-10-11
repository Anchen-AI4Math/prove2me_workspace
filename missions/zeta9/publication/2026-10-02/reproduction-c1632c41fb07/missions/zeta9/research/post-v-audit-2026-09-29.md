# V 之后的独立审计：固定零线、分母与连接能推出什么

2026-09-29。本文是独立推导及交叉审查，不把 V 的闭合误认为无理性证明。沿用实际任务的记号；暂不涉及 Lean。结论是：V 可以将假设有理时的最短方向完全确定，但这种确定本身不矛盾。真实连接的多项式分母还能把 J 提升为无理性的等价判据；该等价性同样没有证明 J。

## 1. 将部分同余格直接放回整数输出空间

置 `A_n=E_nW_n`，`h_n=N_n/g_n`，并取 Smith 分解

\[
 U_nJ_nV_n=\operatorname{diag}(s_{1,n},s_{2,n}).
\]

这里 V_n 是 Smith 右变换，不是体积命题 V。由原始提升系数 `D_n/(s_{1,n}g_n)`，提升后的整数输出子格精确为

\[
 \mathcal H_n=\mathbb Z^2\operatorname{diag}(1,h_n)V_n^{-1}.
 \tag{1}
\]

因此 `area(H_n A_n)=h_n Xi_n=exp(2nB_n)`。若其第一长度记为 `ell_n`，则

\[
 \ell_n=\exp(n(B_n-\sigma_n)).                    \tag{2}
\]

这不是替代问题，而是同一个实际最短向量问题的正标度重写。也可完全不选 Smith：令 `M_n=J_n/s1,n`，则

\[
 \mathcal H_n=g_n^{-1}
       (\operatorname{row}_{\mathbb Z}M_n\cap g_n\mathbb Z^2).
 \tag{3}
\]

## 2. 反设有理时，没有额外的高度矛盾

暂设 `zeta(9)=c/d`，`d>0,(c,d)=1`，置 `z_*=(-c,d)`。这条 primitive 输出零线在 H_n 中的最小正倍数为

\[
 q_n=\frac{h_n}{\gcd(h_n,(z_*V_n)_2)}
 =\frac{h_n}{\gcd(h_n,(z_*\operatorname{adj}M_n)_1,
                         (z_*\operatorname{adj}M_n)_2)}.
 \tag{4}
\]

第一式来自 `z in H_n iff (z V_n)_2=0 mod h_n`；第二式来自 `g_n q z_* M_n^{-1}` 整。可能的 det(M_n) 符号不影响整性。

记实际二维输出平面上实值泛函的 Riesz 范数为 r_n。[CM](../roadmap/research/critical-polynomial-margin.md) 已证

\[
 r_n=\Theta(Z_n),\qquad
 Z_n\sim C_Z n^{-5}e^{-\alpha n},\quad\alpha>\tau.
\]

唯一零关系行的长度为 `d Xi_n r_n`。V 与 Hermite 界保证 H_n 的第一长度指数小于 tau；而任何整数输出的非零实值至少为 `1/d`，故其长度至少为 `1/(d r_n)`。因此所有充分大的 n 上，第一向量只能是

\[
 \pm q_n z_* A_n,\qquad \ell_n=q_n d\Xi_n r_n.
 \tag{5}
\]

代入 (2) 得到精确公式

\[
 B_n+\sigma_n=\frac{\log(h_n/q_n)-\log(d r_n)}{n}.
 \tag{6}
\]

由于 `h_n/q_n` 是正整数，

\[
 \liminf(B_n+\sigma_n)\ge\alpha>\tau,
 \qquad
 \liminf\sigma_n\ge\alpha-\limsup B_n>0.16904.
 \tag{7}
\]

这仅是在有理假设下得到的必要条件。当前没有已证的 sigma 上界排除 (7)，所以不能将新 V 裕量解释为矛盾。固定输出 z_* 的系数行随 n 变化，并精确满足 `z_*E_(n+2)=z_*E_n C(n)^-1`；它不是同一个固定系数多项式。逐步清分母不会自动产生一个非零整数实值，因为这里的实值恰为零。

与独立写成的[非零性路线](nonzero-route-2026-09-29.md)核对后，(1)--(7) 一致。该稿的内禀公式 (8)、指标恒等式 `q_n t_n=h_n`、最短与第二高度推导均通过审查；此处 q_n 对应该稿 q_n。

## 3. 一个同时满足严格 V 与收敛连接的有理反模型

下面是一般几何推理的反例，不是实际 zeta 格的反例。模型使用二维欧氏范数，以明确区分一般结构与真实 C(n) 所含的额外信息。

令 `n=2k`，`d_n=lcm(1,...,n)`，取整数

\[
 A=1499000000,\quad b=2,\quad L=A/b=749500000,
\]

\[
 a_n=d_n^2\left\lfloor L^k/d_n^2\right\rfloor,
 \qquad s_n=n^5b^k,
 \qquad \varepsilon_n=(-1)^k.
\]

只取充分大 n，此时 a_n>0。PNT 给 `log d_n/n -> 1`，而 `.5 log L>2`，故 `a_n/L^k -> 1`，且相对误差指数趋零。定义

\[
 \widetilde E_n=
 \begin{pmatrix}s_na_n&0\\s_na_n&\varepsilon_ns_n\end{pmatrix}.
 \tag{8}
\]

目标实数取 theta=1。线性泛函 `ell_n(x,y)=x/(s_na_n)` 使两条输出行的实值都为 1；所以 `(u,v)` 的实值精确为 `u+v`。primitive 零线为 `(-1,1)`。

这是一个合法的有理形式矩阵模型：取底格 K=I_2、`F=E^-1`、共同分母 D=s_na_n，则

\[
 J=DF=\begin{pmatrix}1&0\\-\varepsilon_na_n&\varepsilon_na_n\end{pmatrix}.
\]

Smith 因子是 `(1,a_n)`，所以 `N=a_n`，并且按任务相同规则
`g=gcd(N,d_n^2)=d_n^2`，`h=a_n/d_n^2`。面积为 `Xi_n=s_n^2a_n`。

直接算出

\[
 \alpha_0=\tfrac12\log A=10.5640320280\ldots>\tau,
\]

\[
 \lim\frac{\log\Xi_n}{2n}
   =\tfrac14\log(2A)=5.4553028091\ldots
   <\tfrac14\log(3711015000),
\]

\[
 \lim B_n=\alpha_0-1=9.5640320280\ldots<10.394960.
 \tag{9}
\]

所以该模型满足比新 V 更强的体积裕量及现有 X 的面积上界。完整整数输出格的第一向量最终永远是 `(-1,1)` 的正负号：其长度为 s_n，而任何非零实值输出长度至少为 s_na_n。

上面跨阈值的小数已用纯有理数验证：将 `log A=30 log 2+log(A/2^30)`，对每项使用 48 项 `2 sum_(j<48) x^(2j+1)/(2j+1)` 及尾界 `2x^97/[97(1-x^2)]`，其中 `x=(r-1)/(r+1)`。得到 `10.56403202803343<alpha_0<10.56403202803344` 和 `5.45530280915670<log(2A)/4<5.45530280915671`；因此 (9) 不是靠显示精度判断严格大小。

部分输出子格是 `Z x hZ`。其零线最小倍数为 h，第一长度为 hs_n；其非零实值高度为 s_na_n，两者之比恰为 `1/d_n^2 -> 0`。因此

\[
 \sigma_n=\frac{\log d_n}{n}\longrightarrow1,
 \qquad B_n+\sigma_n\longrightarrow\alpha_0>\tau.
 \tag{10}
\]

这里 J 确实失败，目标 theta 也确实有理，所有短形式可以永久为零。

此外有精确有理连接

\[
 \widetilde E_{n+2}=\widetilde E_n\widetilde G_n,
 \quad
 \widetilde G_n=
 \operatorname{diag}\left(
   \frac{s_{n+2}a_{n+2}}{s_na_n},
   -\frac{s_{n+2}}{s_n}\right)
 \longrightarrow\operatorname{diag}(A,-2).
 \tag{11}
\]

两个模态都有实际稿中的共同 n^5 因子，第二模态的绝对值大于 1，连接及其逆的实算子范数一致有界。因此增加“第二模态非零且增长”“跨 n 连接收敛”“整数输出和正确 Smith 缩放”等一般条件，仍不能推出短形式无穷非零。

**模型没有保留的实际输入：** 真实五维 C(n) 的固定有理函数表达式、其多项式分母界、原始无限正核、`d_n^9F_n` 整性和 N_n 的精细逐素数限制。尤其 (11) 的分母可能很大，不能据此声称它满足下一节的多项式互送性质。这些差别保留了继续使用真实算术结构的空间。

## 4. 真实多项式分母给出的进一步正结果

以下结论是对 local_plane 代理独立提出方案的复核，保留推导供交叉检查。正式稿 [shape-direction](shape-direction-2026-09-29.md) 第 1--4 节已完成全文独立审查并通过；其 100 格有限数据未在本审计中重复生成。令 I_n 是真实低 zeta 整核的有理输出像格，c_n 是其有理内容，`L_n=I_n/c_n`。则 L_n 是内容 1 的整数行格，面积为 N_n，且 H_n=(L_n/g_n) intersect Z^2。

取正整数 a_n,b_n，使 `a_n C(n)`、`b_n C(n)^-1` 均整。真实连接的固定有理函数表达式允许 a_n,b_n 都是 n 的多项式量级。它们给

\[
 a_n I_{n+2}\subseteq I_n,
 \qquad b_n I_n\subseteq I_{n+2}.
\]

若 `c_(n+2)/c_n=u/v` 既约，则 `u|b_n,v|a_n`。令 Q=a_nb_n，由 `a_nu/v` 和 `b_nv/u` 都整除 Q 得

\[
 QL_{n+2}\subseteq L_n,\qquad QL_n\subseteq L_{n+2}.
\]

因此 `N_(n+2)/N_n` 的既约分子、分母均整除 Q^2。令 `l=d_(n+2)/d_n`、`R=Q^2l^2`；由逐素数的 min 公式，`g_(n+2)/g_n` 的分子、分母都整除 R。于是 T=QR 满足

\[
 T\mathcal H_{n+2}\subseteq\mathcal H_n,
 \qquad T\mathcal H_n\subseteq\mathcal H_{n+2}.
 \tag{12}
\]

这里 `l|(n+1)(n+2)`，所以 T=poly(n)。真实加权连接 G_n 及其逆一致有界；令界为 C。相邻第一长度因 (12) 满足 `ell_(n+2)<=CT ell_n` 及反向不等式。如果相邻第一输出的 primitive 方向不同，则把后一第一向量乘 T 送回 n 可得独立第二向量，故

\[
 \ell_{2,n}\le C^2T^2\ell_n.
\]

而面积下界总给

\[
 e^{2n\sigma_n}
 =\frac{h_n\Xi_n}{\ell_n^2}
 \le\frac{\ell_{2,n}}{\ell_n}.
\]

因此在方向发生变化的参数必有 `sigma_n=O(log n/n)`。若变化发生无穷多次，V 立即给 J。

反过来，若 J 失败，则 V 的严格固定裕量迫使 `sigma_n>=delta>0` 最终成立；上述不等式迫相邻 primitive 第一输出方向最终相同。其真实整数形式值由 V 趋零，所以固定 primitive 输出必为精确零关系，目标 zeta(9) 有理。结合已有 `J => 无理性`，得到

\[
 \boxed{\text{在当前已证 V 和真实连接下，J 等价于 zeta(9) 无理。}}
 \tag{13}
\]

这是一条新的严格归约，不是 J 的证明。它说明在当前系统中，“证明跨 n 第一输出无穷次换向”或“证明 J”均不能只靠重新组合已知 V 自动解决根问题。

同一证明还给更精确的形状版本：Hermite 给 `sigma_n>=-O(1/n)`；无理时规范第一方向不可能最终固定，所以无穷多次换向迫 `liminf sigma_n=0`。反之该 liminf 与 V 一起给 J。因此在当前已证输入下，(13) 还等价于 `liminf_(even n) sigma_n=0`。这是子序列条件，没有证明完整 S 的 `sigma_n->0`。

## 5. 对接下来的实际研究的审计结论

1. 对实际最大外积模态构造有理不变锥是有意义的新输入；若成功，可固定目前四种候选面积率中的第一种。但仅有该实谱结论仍与 (5)--(7) 相容。
2. “反设有理后清分母”必须另给某个整数值非零的理由，或给零线倍数 q_n 与真实局部斜率无法满足的具体界。仅有分母有限、素数光滑或 q_n<=h_n 不产生矛盾。
3. 相邻格多项式互送补足了抽象收敛连接缺少的算术条件，并给 (13)。剩下的是实际第一方向无穷次变化的证明；有限换向证书不够。

截至本文写成，未证明 S、J、任何所需的无穷非零性或 zeta(9) 无理性。VC 与 V 的既有证明状态不变。

## 6. 后续真实外积锥成果的独立审核

已全文审查[真实外积不变锥稿](exterior-cone-2026-09-29.md)、`verify_exterior_cone.py` 及 `probe_exterior_cone.py`，并独立重跑主证书，结果 PASS：所有 31 层整数系数满足保锥和 1/2 收缩余量，原始部分分式重建的 F20 外积严格进锥。

Jacobi 方向独立核对如下：设 `den=(n+1)^8(n+2)^10`、`P=den C`。C^-1 的二阶子式取 P 的互补三阶子式 `P[J^c,I^c]`，符号为 `(-1)^(sum I+sum J)`。脚本乘入 `n^(14-2 sum I)(n+2)^(2 sum J)` 正是加权连接所需因子。清去共同多项式 common、整数 content，并将外积左右换基清分母为 d_L,d_R 后，得到的整数多项式矩阵是实际 T(n) 的正标量倍数，其中

\[
 s(n)=\frac{n^{14}\det(P(n))d_Ld_R}
             {\operatorname{den}(n)^2\operatorname{common}(n)
              \operatorname{content}}>0\qquad(n\ge20).
\]

因此系数不等式确实作用于真实连接，而不是错误转置的伴随矩阵。射影梯度的行绝对值和不超过 1/2，极限分母统一大于 10^9，故射影方向收敛于极限映射唯一不动点。其正特征值大于 10^9，而其余外积特征值绝对值小于 200000；所以它恰为 AB。Cesaro 对数平均给 `log Xi_n/(2n)->(1/4)log(AB)`，这里没有将有限增长下界误作精确指数。

高度推论的正确公式是 `(1/4)log(A/B)`。旧稿使用粗根区间后所写的 `<5.057` 数值不成立：该粗区间只给约 5.0632155。根代理发现并修复为 `1499365229<A<1499365230`、`2.47407884<B<2.47407885` 的更细有理根隔离，配合显式对数余项严格给出 `<5.05562`。修订后的特征多项式恒等式、端点符号、对数证书及整套外积核验均已再次独立重跑通过；核心锥定理不受旧显示值错误影响。
