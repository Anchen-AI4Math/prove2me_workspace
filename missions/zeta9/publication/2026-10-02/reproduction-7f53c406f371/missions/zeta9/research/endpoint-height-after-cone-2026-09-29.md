# 精确面积率之后：端点分母、伴随内容与尚缺的求值 gcd

2026-09-29。独立端点路线审计。本稿证明一个新的全局伴随行标度上界，厘清两种不同的分母目标，并给出固定次数对“统一求值整除”的限制。没有证明端点分母达到目标，没有证明 FD、J 或无理性；暂不涉及 Lean。

## 1. 先区分三个内容与两个指数门槛

沿用真实二维有理输出像 `I_n=K_n F_n S^T`，其中 K_n 是饱和整数低 zeta 核。设其共同分母为 D_n、Smith 因子为 s1,n 和 s2,n，定义

\[
 c_n=s_{1,n}/D_n,\qquad
 \rho_n=s_{2,n}/D_n=c_nN_n.
\]

c_n 是输出像 I_n 的有理内容；rho_n 是将逆像 E_n 的两行同时变为总体 primitive 整数行的正标度。若局部 Smith 指数为 a1<=a2，则

\[
 \boxed{v_p(c_n)=a_1(n,p),\quad
        v_p(\rho_n)=a_2(n,p),\quad v_p(N_n)=a_2-a_1.}
 \tag{1}
\]

因此控制 N/g 的界不能替代 rho 的界，更不能替代求值后的 gcd 界。饱和核的加权面积 Delta_n 满足精确关系

\[
 \boxed{\Delta_n=c_n^2N_n\Xi_n=c_n\rho_n\Xi_n,
 \quad \rho_n^2=N_n\Delta_n/\Xi_n.}                    \tag{2}
\]

把 `q=d_n^9`、`A=qF_n`，并用混合四阶子式内容 delta4* 归一化，则 [FD 算术稿](../roadmap/research/fd-arithmetic-next.md) 的整数伴随行恰为

\[
 \widetilde C_n=S\operatorname{adj}(A)/\delta_4^*
                 =\rho_n E_n.                          \tag{3}
\]

本任务 det F_n>0，故没有额外符号。其十个整数系数的 gcd 为 1。

设极限主、次特征根为 A>0 和 -B<0，置

\[
 \alpha=\tfrac12\log A,
 \quad\beta=\tfrac12\log B,
 \quad\delta=(\alpha-\beta)/2,
 \quad\kappa=2\delta=\alpha-\beta.
\]

新[外积锥证明](exterior-cone-2026-09-29.md)固定了实际第二模态。[共同 n^5 模态稿](../roadmap/research/cp-stable-next.md) 因而给

\[
 \|U_{B,n}\|\asymp n^5e^{\alpha n},\qquad
 \Xi_n\asymp n^{10}e^{(\alpha+\beta)n},\qquad
 w_n\asymp n^{-1/2}e^{-\kappa n}.                        \tag{4}
\]

这里 w_n 是五点窗宽；实际端点最终就是两侧极端采样，距离 zeta 各为 `(1/2+o(1)) w_n`。有理根证书给近似值
`alpha=10.56415384...`、`beta=0.45293407...`、`delta=5.05560988...`、`kappa=10.11121977...`。

需要分清：

* **只排除固定有理关系：** 任一严格端点的 `Q_n w_n -> 0` 即足够。一个指数充分条件是端点既约分母率严格小于 kappa，约 10.11122。
* **让所有完整格第一输出避开开窗（FC/FD）：** Hermite 与 (4) 给第一输出高度 `O(e^(delta n))`，所以只靠这一统一高度界的充分分母率是严格小于 delta，约 5.05561。

后一目标约强一倍，不能把两者混用。临界指数相等时还须保留 n^-1/2 及常数，不可只比较小数指数。

## 2. 新的 rho 全局上界：只需较大 Smith 指数

**定理。** 已证局部 jet 和反向包含给出

\[
 \boxed{\limsup_{2\mid n}\frac{\log\rho_n}{n}
 \le R:=\frac{19}{2}+\frac34\log3-\frac{\pi}{4\sqrt3}
 =9.8705093754\ldots<9.871.}                              \tag{5}
\]

这个结论不要求所有固定模型低 zeta 矩阵都非奇异。

先看 p>n。F_n 在 Z_(p) 上整，故 a1,a2>=0。[大素数平移迹](../roadmap/research/prime-valuation-attack.md) 给低三列三阶子式估值
`delta3>=floor(7n/(2p))`，而饱和核输出的行列式估值为 `a1+a2=v_p(det F)-delta3`。因此

\[
 0\le a_1+a_2\le\left\lfloor3n/(2p)\right\rfloor\le1.
\]

所以 a1=0，且

\[
 a_2\le\mathbf1_{n<p\le3n/2}.                            \tag{6}
\]

特别是 c_n 在 p>n 都是单位，rho_n 在 p>3n/2 都是单位。

对 p<=n，固定 m=floor(n/p) 后取 n 足够大。下列较大指数界都不使用固定低三行模型的逆矩阵：

* 偶数 m：整个块 `a2<=9`，来自[偶数四通道余子式](even-block-sharpening-2026-09-29.md)；
* 奇数 m、`0<r/p<1/7`：锚点余子式下界经整数连接传播，D0=4，所以 `a2<=9`；
* 奇数 m、`1/7<r/p<1/3`：[迹提升](first-block-joint-2026-09-29.md)使四通道权重和为 17，D0=5，所以 `a2<=9`；
* 奇数 m 的余段：反向偶锚点包含给 `a2<=10`。

因此在每个固定有限 y=n/p 区间上，统一上包络为 9，只有奇数块最后 2/3 的部分加 1。跳点等式可移除；r=0 的素数都整除 n，其总贡献 O(log n)。

说明截断合法性：由 `d_n^9 F_n` 整及伴随逆矩阵，所有素数都有

\[
 a_2(n,p)\le36\lfloor\log_p n\rfloor
                  +8\lfloor\log_p(7n/2)\rfloor.          \tag{7}
\]

因此 `p<=sqrt(7n/2)` 的正贡献为 o(n)。其余素数粗界为 44；`p<n/H` 的未处理尾部至多 `44 theta(n/H)=44n/H+o(n)`。先固定 H，使用各固定块上的素数定理，再令 H 趋于无穷，得到

\[
 \limsup\frac{\log\rho_n}{n}
 \le\frac12+9+\sum_{j\ge0}
     \left(\frac1{2j+4/3}-\frac1{2j+2}\right).
\]

负的 a2 项只会改善此上界。级数可写为

\[
 \int_0^1\frac{x^{1/3}-x}{1-x^2}\,dx
 =\frac32\int_0^1\frac{u}{1+u+u^2}\,du
 =\frac34\log3-\frac{\pi}{4\sqrt3},
\]

证明 (5)。这是与 N/g 预算不同的积分：这里累加的是 a2，不是 a2-a1 或其折扣。

## 3. 实际端点高度仍由求值 gcd 决定

对于真实整数样本 `t=k(k+n)`，置

\[
 P_B(t)=\widetilde C_{n,B}v(t),\quad
 P_A(t)=\widetilde C_{n,A}v(t),\quad
 G_n(t)=\gcd(P_B(t),P_A(t)).
\]

在五点统一范围中 P_B>0，约分后分母精确为

\[
 \boxed{Q_n(t)=\frac{P_B(t)}{G_n(t)}
       =\frac{\rho_n Q_n^B(t/n^2)}{G_n(t)}.}               \tag{8}
\]

五点均趋向固定鞍点，最终 Taylor 正性给 `Q_n^B(t/n^2) asy ||U_B||`。记两个端点求值 gcd 的最大值为 Gmax,n，则

\[
 \min(Q_{-,n},Q_{+,n})
       \asymp\frac{\rho_n n^5e^{\alpha n}}{G_{\max,n}}.
 \tag{9}
\]

从 (5) 只得到未计求值约分的分母上指数 `R+alpha≈20.43466321`，离固定有理关系门槛 kappa 仍很远。

结合 (4) 和 (9)，有比纯指数更精确的尺度

\[
 w_n\min(Q_{-,n},Q_{+,n})
       \asymp\frac{\rho_n n^{9/2}e^{\beta n}}{G_{\max,n}}.
 \tag{10}
\]

因此可直接研究的充分目标是

\[
 \boxed{\frac{G_{\max,n}}
              {\rho_n n^{9/2}e^{\beta n}}\longrightarrow\infty
        \quad\text{沿某个无穷子序列}.}                   \tag{11}
\]

这会使 (10) 趋零。若 zeta=c/d，有理间隔却要求 `d w_n min(Q_-,Q_+)>1`，矛盾。一个使用粗 rho 上界的指数充分条件是求值 gcd 率严格大于

\[
 R+\beta=10.32344345\ldots.                              \tag{12}
\]

这里所缺的是下界 Gmax，而不是重新降低 N/g。rho 的实际率若更低，(11) 的门槛会相应下降；(12) 只是当前统一上界给出的充分数值。

另一个自然有理逼近是[精确椭圆标准形](diophantine-normal-form-2026-09-29.md)的中心 `xi_n=<U_B,U_A>/||U_B||^2`。用 (3) 写成整数 Gram，令 `H_B=sum_r Ctilde_(B,r)^2 n^(4r)`、`H_BA=sum_r Ctilde_(B,r)Ctilde_(A,r)n^(4r)`，则其既约分母恰为

\[
 Q_{\xi,n}=H_B/\gcd(H_B,H_{BA}),\qquad H_B=\rho_n^2\|U_B\|^2.
\]

因此只用当前标度所得上指数是 `2(R+alpha)≈40.86932643`，比误差指数 kappa 更弱。高精度有理中心不会自动具有小分母；这里也必须单独控制整数 Gram 的求值内容。

对于更强的 FD，令 `mu_N=rho_n lambda1,n`。已有精确分解与 (4) 现在给双边比较

\[
 \boxed{F_n^{FD}\asymp
              \frac{\mu_{N,n}}{G_{\max,n}\sqrt n}.}       \tag{13}
\]

此前只能使用这一关系的上界；新实际第二模态非零使 `w_n||U_B||^2/Xi_n asy n^-1/2`，从而得到双边尺度。但 lambda1 仍未知。若再用 Hermite 的统一上界，则一个指数充分目标为 Gmax 率严格大于

\[
 R+\frac{\alpha+\beta}{2}=15.37905333\ldots,              \tag{14}
\]

等价于用 (9) 保证分母率小于 delta。不能把这个更强目标误当作仅排除固定有理关系所必需。

新椭圆标准形还无条件给 `lambda1,n>=Xi_n/||U_B|| asy n^5e^(beta n)`。因此 `mu_N>=rho_n n^5e^(beta n)` 乘一个固定正常数。结合 (13)，(11) 所涉及的尺度正是 FD 至少要面对的基准尺度；它不是由低于真实第一长度的虚构向量产生的。

## 4. 已知 jet 整除没有给出所需的求值下界

对饱和核 K，令 `x(t)=Kv(t)`，`c_eval(t)=gcd(x_1,x_2)`。取 Smith 左变换 U，并令 `y=Ux/c_eval` primitive。只要 x(t)非零，就有既有精确公式

\[
 G_n(t)=c_{\rm eval}(t)\gcd(N_n,y_2(t)).                  \tag{15}
\]

c_eval 是饱和核的**求值内容**，不同于 (1) 的有理输出内容 c_n。局部 a1,a2、rho、N 的界没有控制 y2(t) 与 N 的对齐，也没有控制 c_eval 的正增长。

一个简单局部例子显示这种信息不能由指数替代。固定 p^e、整数样本 t0，在底格 `K=(1,t)` 内取两组整数伴随多项式

\[
 (p^e,t-t_0),\qquad(p^e,t-t_0+1).
\]

两组的总体系数内容、行列式和 Smith 因子完全相同；若取 rho=1，则相应输出像的局部指数均为 `(-e,0)`，底格也相同。但在同一个 t0 上，求值 gcd 分别是 p^e 和 1。故仅有局部指数和饱和底格面积不能决定端点约分；需要真实取样点在局部系数方向中的位置。

还有两个对可能证明方法的统一限制。

**固定除数引理。** 对每个 n，

\[
 \gcd_{k\in\mathbb Z}
  \bigl(P_B(k(k+n)),P_A(k(k+n))\bigr)\mid8!.
 \tag{16}
\]

证明：两条次数至多 8 的 k 多项式的总体系数 gcd 仍为 1。若素数同时整除所有新系数，从最高偶次系数逐次回代，就会整除原来两条 u 多项式的所有系数，矛盾。若整数 D 整除两条多项式的所有整数取值，Newton 差分展开显示 D 整除各阶差分；乘以 8! 后所有普通系数都是这些差分的整数线性组合。因此 D 整除 8! 乘以总体系数 gcd，即 (16)。只取充分大的正整数 k 也有相同结论，平移插值即可。

**五样本共同因子引理。** 若五个整数 t_j 互异，则

\[
 \gcd_j G_n(t_j)\mid\prod_{i<j}(t_j-t_i).                \tag{17}
\]

这是五阶 Vandermonde 的伴随恒等式与 (3) 总体内容 1 的直接结果。对实际五点，`t_j-t_i=O(n^(3/2))`，故右侧为 O(n^15)。

因此不能期待有一个共同的指数大整数，统一整除这两条 primitive 伴随多项式在全部整数样本、甚至全部五个实际样本的两个取值。这不排除某个端点的 G 很大：不同样本的巨大 gcd 可以含不同素数，所以 (16)--(17) 不能反过来证明 (11) 失败。它们限定的是“忽略样本位置，只从整列 jet 提取同一个指数公共因子”的策略。

## 5. 本次结论与明确的剩余率

新全局结果是 rho 的上指数 (5)，并由实际第二模态得到 (10)、(13) 的精确尺度。现在可将端点路线集中到 (11)，或者研究 (15) 中真实端点的饱和核求值内容与 Smith 局部因子。

当前缺少约 10.32344 的求值 gcd 正指数下界（这是使用 rho 粗上界的充分目标），或另一条直接把端点既约分母压到误差指数 kappa 以下的证明。没有把 N/g 的已证上界当成这样的分母界，没有用有限样本代替无穷量词。S、J 与 zeta(9) 无理性仍开放。

## 6. 精确证书与交叉审查

[小范围证书脚本](../scripts/verify_endpoint_height.py) 已运行通过，记录位于 [certificate.json](../verification/endpoint-height-after-cone-2026-09-29/certificate.json)。它没有扩展格扫描：

* 用前 1000 项纯有理级数及单调尾积分夹界，严格得到 `9.87050929222019<R<9.87050945860945<9.871`。尾积分的对数由正 atanh 级数与显式余项处理，没有调用浮点 pi。
* 从最终外积证书的有理根区间独立重算 alpha、beta、gamma、delta，与其面积率和高度率逐项一致。两项求值 gcd 的充分指数常数分别严格小于 `10.323444`、`15.379054`；这些是充分门槛常数的上界，不是已证 gcd 增长率。
* 只读取五个已有归档 `n=12,24,48,96,192`，精确验证 `rho E` 整且总体 primitive、K 饱和、输出像内容，以及 (2) 平方后的有理面积恒等式。没有把这些尚不满足统一五点范围的参数称作真实端点测试。

local_plane 代理已全文独立复核第 2 节的全局 rho 积分和第 4 节两个固定除数引理，均通过。

另已全文交叉审核[固定方向算术稿](fixed-direction-arithmetic-2026-09-29.md)：局部 B 轴图形、前二十块对角/末位剪切、大素数顶残数、全 m 缺损 7 及固定 H 后 `1/3` 积分均通过。这控制固定输出的进入倍数，没有控制 (8) 的端点求值 gcd，两者不可混用。

还已全文审核[第二模态方向稿](second-mode-direction-2026-09-29.md)及重跑其精确脚本。非自治一阶射影引理没有遗漏二次项：固定特征坐标中极限矩阵对角，射影分母对横向坐标 e 的依赖只有 O(e/n)；先用稳定向前与不稳定向后的卷积得 e=O(1/n)，减去一阶项后相同论证给 O(1/n^2)。规范方向 `p+[pX-(pX)_4p]/n`、唯一正根偏移、固定坐标及有理中心的交替误差均通过。该稿确认本文 (4) 所用的实际第二模态，但交替逼近本身仍未控制约分分母。
