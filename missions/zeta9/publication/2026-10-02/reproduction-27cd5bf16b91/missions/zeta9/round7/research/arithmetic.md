# 第七轮：部分同余模数、严格限制与新的结构递推

本轮已证明部分模数的格包含与短向量排除准则，并建立了原五维形式映射的统一有理连接及行列式闭式。后者进一步证明 Smith 模数的全部素因子不超过 $7n/2$。尚未证明足够强的、随 $n$ 统一成立的最短向量下界，因此没有得到 $\zeta(9)$ 无理性证明。

## 1. 规范格与部分模数

沿用第六轮：$K\in\mathbb Z^{2\times5}$ 是四次低 ζ 整核的饱和整数基；$J\in\mathbb Z^{2\times2}$ 是同一正分母 $D$ 下的 $(B,A_9)$ 像。取
\[
 UJV=\operatorname{diag}(s_1,s_2),\quad s_1\mid s_2,\quad N=s_2/s_1,
 \qquad E=DJ^{-1}K.
\]
行格满足严格恒等式
\[
 \mathbb Z^2E=\frac D{s_2}\Lambda_N,
 \quad\Lambda_g=\mathbb Z^2\operatorname{diag}(g,1)UK\quad(g\mid N). \tag{1}
\]
所有长度可取同一个正定 Euclidean 度量，特别包括系数权重 $n^{2r}$。记该度量下第一、第二逐次极小值为 $\mu_i$，面积为 $\Delta$。

若 $g\mid h\mid N$，则
\[
 \Lambda_N\subseteq\Lambda_h\subseteq\Lambda_g\subseteq\mathbb Z^2K,
 \qquad g\mathbb Z^2K\subseteq\Lambda_g,
\]
从而
\[
 \mu_1(K)\le\mu_1(\Lambda_g)\le g\mu_1(K),\qquad
 \mu_1(\Lambda_N)\ge\mu_1(\Lambda_g),\qquad
 \Delta(\Lambda_g)=g\Delta(K). \tag{2}
\]
因此任一经过证明的部分模数下界直接给出
\[
 \lambda_2(E)\le\frac2{\sqrt3}\frac D{s_1}
                         \frac{\Delta(K)}{\mu_1(\Lambda_g)}. \tag{3}
\]
这里使用二维 Gauss 不等式 $\lambda_1\lambda_2\le2\Delta/\sqrt3$。完整模数 (1) 只是规范像格的 Smith 重写；式 (3) 的新增内容必须来自独立的短向量排除，不能把 (1) 本身当作排除定理。

## 2. 可检验的局部排除与其局限

对 primitive 行向量 $z\in\mathbb Z^2$，置 $a=(zU^{-1})_1$。沿实直线 $\mathbb R(zK)$，属于 $\Lambda_g$ 的最短整数倍恰为
\[
 t_g(z)zK,\qquad t_g(z)=\frac g{\gcd(g,a)}.
\]
故有精确公式
\[
 \mu_1(\Lambda_g)=\min_{z\in\mathbb Z^2,\ \gcd(z_1,z_2)=1}
             \frac g{\gcd(g,(zU^{-1})_1)}\|zK\|. \tag{4}
\]
其逐素数代价为 $v_p(t_g)=\max(0,v_p(g)-v_p(a))$，包括 $a=0$ 时 $t_g=1$。证明 $\mu_1(\Lambda_g)>H$ 时，只须排除所有原核长度不超过 $H$ 的 primitive 方向，并对每一方向检验 (4)；但不能只检查先找到的少数方向，也不能由素数数量代替这一全称量词。

由 (2)，$\log g=o(n)$ 的模数最多改善 $o(1)$ 的归一化指数。单纯的指数 $g$ 也不足：格 $g\mathbb Z\times\mathbb Z$ 仍有长度为 1 的向量。Hermite 上界
\[
 \mu_1(\Lambda_g)^2\le\frac2{\sqrt3}g\Delta(K) \tag{5}
\]
还给出达到目标下界所需的最小模数量级。若 $H^2<g\Delta(K)$，$\Lambda_g$ 中所有长度不超过 $H$ 的非零向量必共线，因为两独立向量的面积至少为 $g\Delta(K)$。这只把难点压缩为一条潜在短直线，并不自动排除它。

## 3. 一个无需枚举全部向量的 gcd—投影引理

取任一幺模核基 $b_1,b_2$，使同余条件写成
\[
 Ax+By\equiv0\pmod g,\qquad\gcd(A,B)=1,
 \qquad h=\gcd(g,A).
\]
若 $y=0$，则 $x$ 是 $g/h$ 的倍数；若 $y\ne0$，因 $\gcd(B,h)=1$，$y$ 是 $h$ 的非零倍数，而在垂直于 $b_1$ 方向上的投影长度至少为 $h\Delta(K)/\|b_1\|$。因此
\[
 \boxed{\ \mu_1(\Lambda_g)\ge
 \min\left\{\frac gh\|b_1\|,\frac{h\Delta(K)}{\|b_1\|}\right\}.\ } \tag{6}
\]
对固定 $b_1$，$h$ 和 $g/h$ 均随整除关系单调，所以这一特定粗下界在全模数 $N$ 最强。它不否定部分模数的精确最短向量计算可能比该粗界更好。

在规范格中，令 $v$ 是沿 primitive 原核方向的 primitive 格向量，则 (6) 等价于一般二维事实
\[
 \lambda_1(E)\ge\min\{\|v\|,\Delta(E)/\|v\|\},\quad
 \lambda_2(E)\le\frac2{\sqrt3}\max\{\|v\|,\Delta(E)/\|v\|\}. \tag{7}
\]
由此，一个长度在上下两边都受控制的、约为 $\sqrt{\Delta(E)}$ 的 primitive 向量足够控制两条独立方向。任意放大短向量会破坏其 primitive 性，不能制造假的平衡向量。

## 4. 有限证据的准确范围

计算代理的 [modulus-scan.json](../verification/modulus-scan.json) 对既有五个参数 $n=12,24,48,96,192$ 记录了精确 Gauss/Gram 证书，没有使用 ζ 数值来选择模数。$g=\gcd(N,d_n^2)$ 的加权增益
\[
 n^{-1}\log\{\mu_1(\Lambda_g)/\mu_1(K)\}
\]
依次约为 $0.902178,0.907103,0.969176,0.933616,0.990357$。这是五个有限格的真实改进，不是统一下界。它与 $\tfrac12n^{-1}\log g$ 接近，不能据此假设同余斜率具有随机性或均匀分布。

对同一五例，直接使用原核 Gauss 最短基向量的粗投影式 (6)，所得未加权 $n^{-1}\log\lambda_2(E)$ 上界约为 $10.54749,11.06469,11.25651,10.99030,11.19041$，均未跨旧实侧阈值 $10.43$；本轮锐化到 $10.564$ 后，只有首例跨过。该粗引理弱于部分模数上的完整有限最短向量证书；此处不把粗界失败解释为路线失败。

既有五个 $N$ 全部被 1000 以下的试除完全分解，最大素因子为 $17,31,71,139,283$，均小于 $3n/2$；“小于 $3n/2$”目前仍是有限观察。下面给出较弱但统一的 $7n/2$ 上界。

## 5. 五维行列式、子式内容与统一光滑界

[connection.md](connection.md) 证明了 $F_{n+2}=C(n)F_n$，其中 $F_n$ 是行次序 $u^0,\ldots,u^4$、列次序 $(B,A_3,A_5,A_7,A_9)$ 的完整形式矩阵，并得到
\[
 \det F_n=\frac{(3n/2)!(7n/2)!}{7n((n/2)!)^{10}}
                           \qquad(n\ge2\text{ 偶}). \tag{8}
\]
取 $q=d_n^9$。第五轮简单极点乘积与整数 Taylor 乘子论证已对全部整数四次 $W$ 证明 $A=qF_n\in\mathrm{Mat}_5(\mathbb Z)$。这里无需移植任何未证的分母猜想。

令 $L$ 为 $A$ 的三列低 ζ 系数，$\delta_3$ 为其全部 $3\times3$ 子式的 gcd；令 $\delta_4^*$ 为 $A$ 中包含这三列并另取 $B$ 或 $A_9$ 列的全部 $4\times4$ 子式的 gcd。三者均取正值。若 $J_q$ 为饱和低核 $K$ 在 $A$ 两个剩余坐标上的整数像，则
\[
 |\det J_q|=\frac{|\det A|}{\delta_3},\qquad
 s_1(J_q)=\frac{\delta_4^*}{\delta_3},\qquad
 \boxed{\ N=\frac{|\det A|\delta_3}{(\delta_4^*)^2}.\ } \tag{9}
\]
证明：对矩形矩阵 $L$ 作左右幺模 Smith 变换，使其前三行成为对角 $a_1,a_2,a_3$，后两行零。后两行给出饱和核基。展开完整行列式给 $\delta_3\det J_q$；含三列低 ζ 的四阶子式只能再取后两行之一，故其 gcd 是 $\delta_3$ 乘 $J_q$ 各项 gcd。幺模变换不改变这些子式理想。式 (9) 对清分母标度不变：$q$ 乘 $c$ 时三项指数分别为 5、3、4，完全抵消。

特别地 $|\det A|=\delta_3s_1(J_q)^2N$，故 $N\mid|\det A|$。由 (8) 得到：

**统一素数支持与指数界。** 对全部偶 $n\ge2$，
\[
 p\mid N\Longrightarrow p\le7n/2,
\qquad
 v_p(N)\le45\lfloor\log_p n\rfloor+
                         8\lfloor\log_p(7n/2)\rfloor. \tag{10}
\]
因而
\[
                         N\mid d_n^{45}d_{7n/2}^{8}. \tag{11}
\]
令 $h=n/2$。阶乘部分在每个素数幂 $P=p^a$ 的取整贡献为
\[
 \lfloor3h/P\rfloor+\lfloor7h/P\rfloor-10\lfloor h/P\rfloor
             =\lfloor3\{h/P\}\rfloor+\lfloor7\{h/P\}\rfloor\in[0,8].
\]
分母 $14h$ 只会降低估值；$q^5=d_n^{45}$ 贡献第一项，遂得 (10)。分母不引入整数商的新素因子，所以支持结论也包括 $p\mid7n$ 的情况。

由 (10)，任意**固定有限素数集**支持的 $g\mid N$ 都满足 $\log g=O(\log n)$。结合 (2)，仅使用这些素数无法获得正的渐近指数增益。这是统一限制定理；要闭合目前约一个单位的指数缺口，模数必须逐渐引入新的素数，或使用有别于单纯模数指数的结构。

主代理的独立 [minor-smoothness-audit.json](../verification/minor-smoothness-audit.json) 对五个既有参数重算全部 100 个相关子式，验证 (9)、$N\mid\det(d_n^9F_n)$ 与 (11)。这些有限检查不替代上述统一整除证明。

## 6. 尚缺的统一步骤

式 (8)–(11) 消除了巨大 $N$ 可能隐藏任意大素数的担忧，但没有决定 (4) 中的同余方向。下一步可分别研究 $\delta_3,\delta_4^*$ 的统一局部估值，以及随 $n$ 变化的低核同余斜率。行列式或素数支持给面积，不能单独给第一极小值下界。

对每个 $n$ 精确计算全部 $p\le7n/2$ 的局部数据仍只是有限证书。要证明无理性，必须给出无限参数范围上可证的 $\mu_1(\Lambda_g)$ 下界，强到经 (3) 同时产生两条独立的、整化后趋零的形式；或者找到另一条保证非零的统一机制。有限小值、有限近似“平方根指数增益”，以及连接谱本身均不能替代该步骤。
