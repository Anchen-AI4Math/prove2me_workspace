# 2026-10-01 独立审阅：右移 Mellin 算术与两平方极点全族阻碍

本审阅只修改本文件。已读取当前任务 `status.md`、`scope.json`，并按入口执行
`python scripts/workspace.py files zeta9`；只读取当前结论实际依赖的研究稿。
全参数结论的依据是下面的数学推导，不是有限算例。本轮没有 Lean 构建或外部提交。

## 1. 已审阅的对象与结论

独立阅读全文或相应依赖段落：

- [高阶调和分母稳定性](harmonic-denominator-stability-2026-10-01.md) §§1–4；
- [连续及稀疏右移算术](mellin-shift-arithmetic-2026-10-01.md)，包括新增 §5 临界尺度；
- [两平方极点全族](two-pole-family-2026-10-01.md) 全文；
- [原始 Mellin Schur 构造](alternative-route-2026-09-29.md) §§2–3；
- [Mellin 精确误差](mellin-sharp-error-2026-09-30.md)；
- [平方极点定义](modified-poles-2026-09-30.md)，以及
  [正矩泛函](positive-hankel-zeta9-2026-09-29.md) §1。

审阅结论：三份新稿的全参数数学结论通过。审阅中要求将调和数证明的有限异常条件
精确写成“εN 大于全部有限异常素因子”，并将右移稿的粗行列式论证写成
`det C<2^D`；两处已在对应稿修改。以下包含独立重构及一个额外的差分系数秩清分母界。

## 2. 调和分母主指数：固定截断顺序正确

设固定整数 s≥1，H_N^(s)=Σ_(j=1)^N j^(−s)。固定 ε∈(0,1)，对充分大的 N，
任意 εN<p≤N 的素数都满足 p>√N，k=⌊N/p⌋≤⌊1/ε⌋。精确分块为

\[
p^s H_N^{(s)}=H_k^{(s)}+p^sU_{N,p},\qquad U_{N,p}\in\mathbb Z_p.
\]

有限集合 H_1^(s),...,H_⌊1/ε⌋^(s) 的既约分子均为正整数。因此其异常素因子有限；
取 εN 大于这些素因子后，H_k 是 p-adic 单位，故 v_p(H_N)=−s。
素数定理于是给

\[
\liminf_N\frac{\log\operatorname{den}(H_N^{(s)})}{N}
\ge s(1-\varepsilon).
\]

先完成固定 ε 的 N→∞，再让 ε↓0；并用 den(H_N)|lcm(1,...,N)^s 的上界，
得到全序列极限 s。这里没有将截断阶数随 N 移动，也没有声称所有大素数块都无异常。
例如 s=9 的 H_2 分子 513 确实含 19，不影响固定截断结论。

对任意有理 h,r，q=h+r，两向整除

\[
\operatorname{den}(q)\mid\operatorname{den}(h)\operatorname{den}(r),\qquad
\operatorname{den}(h)\mid\operatorname{den}(q)\operatorname{den}(r)
\]

严格推出
`|log den(q)−log den(h)|≤log den(r)`，包括 r=0 的 den(0)=1。
故任何实际证明满足 log den(r_N)=o(N) 的有理扰动都不能约掉调和分母的主指数。
其分子可以任意大，这个结论不依赖分子高度。

## 3. 连续右移的所有矩阵与分母因子

写 N=2M，E={M,...,M+D}，D≥1。依定义

\[
q=H_N+r,\quad r=b^tC^{-1}b,\quad
b_i=H_N-H_{N+i},\quad
C_{ij}=H_{N+i}+H_{N+j}-H_{N+i+j}-H_N.
\]

C 是 x^M(x^i−1) 的严格正 Gram 矩阵，b≠0，因而 r>0。
取 ℓ=lcm(N+1,...,N+2D)、L=ℓ^9、A=LC、v=Lb，A,v 全部整数，
A 正定且 det A 为正整数。重新计算尺度：

\[
r=\frac{v^t\operatorname{adj}(A)v}{L\det A},\qquad
\operatorname{den}(r)\mid L\det A=L^{D+1}\det C.
\]

这里外面的 L 不能漏掉。分母上界完全允许分子的额外约分。

对短区间 ℓ_(N,t)=lcm(N+1,...,N+t)，逐素数的 Legendre 公式证明

\[
\ell_{N,t}\mid\binom{N+t}{t}\operatorname{lcm}(1,...,t).
\]

若区间最大 p 次幂为 p^k，a₀=⌊log_p t⌋，每个 a₀<a≤k 都在区间内恰有
一个 p^a 倍数，因此 binomial 的对应估值项为 1；其余项非负。此证明包括 N=0。
于是 log ℓ=O(D log(2+M/D))。

精确对角差给 C_ii≤i/(N+1)^9 和 C_ii≤9i²/(N+1)^10；Hadamard 乘积界正确。
用于全部参数的粗界可直接用 C_ii<ζ(9)<2，故 det C<2^D。这一粗界足以推出

\[
\log\operatorname{den}(r)=O(D^2\log(2+M/D)).
\]

因此对每一条整数参数序列 M→∞、D≥1 且
`D²log(2+M/D)=o(M)`，约分后的 P=den(q) 满足 log P/M→18。
这不是只从 (M,2M] 的素数得到的下率 9，而是调和分母稳定性的两侧极限。
条件蕴含 D=o(M)；精确 Jacobi 下界及试探 x^M 上界使 log(ζ(9)−q)=o(M)，
从而同一 primitive 正一次式满足

\[
\frac{\log(P\zeta(9)-Q)}M\longrightarrow18.
\]

D 固定、D 随 M 移动均涵盖。D=0 必须单独用 q=H_(2M) 处理，结论仍成立。
这不排除 M 有界或线性于 D 的其他区域。

## 4. Jacobi 行列式、临界尺度与稀疏量词

N≥4 时，将 x^i−1 作行列式为 1 的整数差分换基，得到 (x−1)x^(i−1)。
由 w≤x^(−4)(1−x)^7/8!，新 Gram 矩阵在正定序中小于以下 beta Gram 的 1/8! 倍：

\[
G_{kl}=\int_0^1x^{N-4+k+l}(1-x)^9\,dx,\qquad0\le k,l<D.
\]

权 x^b(1−x)^9 的 Rodrigues 多项式首项为 binom(2k+b+9,k)，平方范数为
`(k+9)!(k+b)!/[(2k+b+10)k!(k+b+9)!]`。除首项系数平方并相乘，独立得到

\[
\det C\le\frac1{(8!)^D}\prod_{k=0}^{D-1}
\frac{k!(k+9)!(k+N-4)!(k+N+5)!}
{(2k+N+5)!(2k+N+6)!}.
\]

所有 factorial 索引与 N−4 权参数吻合。矩阵序推出 determinant 序时需要两边正定；
本例两边都严格正定，因此适用。分母字符串至少 N−3，进一步给

\[
\det C\le\frac{\prod_{k=0}^{D-1}k!(k+9)!}
{(8!)^D(N-3)^{D^2+9D}}.
\]

若 D→∞ 且 M/(D²log D)→c∈(17/18,∞)，使用实际全参数上界
`∏k!(k+9)!≤(D+8)^(D²+8D)`，得到

\[
\log\operatorname{den}(r)\le(17+o(1))D^2\log D,
\qquad
\liminf\frac{\log(P\zeta(9)-Q)}M\ge18-17/c>0.
\]

18 的局部 lcm 成本与 −1 的 beta determinant 贡献产生 17；误差中的
`D²log log D` 是 o(D²log D)。推导没有误用只对固定 D 成立的渐近式。
**17/18 是本组上界提供的充分条件，不是已经证明的尖锐相变。**
当这个比例趋于无穷，原来的 o 条件成立，恢复精确率 18。

对 E={M,M+a₁,...,M+a_d}，宽度 W=a_d 与维数 d 必须分开。
相同整数矩阵和区间 lcm 推导给
`log den(q−H_(2M))=O((d+1)W log(2+M/W))`。
若该量为 o(M)，则 W=o(M)；稀疏空间包含于 x^M R[x]_(≤W)，故连续度数 W
的 Jacobi 下界仍是它的下界，试探 x^M 仍可用。分母和 primitive 正值都恢复率 18。
没有对任意稀疏模式作无条件分母增长断言。

## 5. 附加全参数界：差分系数秩给更小的清分母因子

以下是本审阅的独立加强，未替代主稿中的区间 lcm 界。
令 a_k=(N+k)^(−9)。差分换基后

\[
\widetilde C_{ij}=a_{i+j-1}-a_{i+j},\qquad
\widetilde b_i=-a_i,\qquad1\le i,j\le D,
\]

且 det C̃=det C、r=b̃ᵗC̃^(−1)b̃。令

\[
\mathcal B=\begin{pmatrix}0&\widetilde b^t\\\widetilde b&\widetilde C\end{pmatrix},
\qquad r=-\frac{\det\mathcal B}{\det C}.
\]

把 a_k 看成独立变量。它在 C̃ 中的整数系数矩阵有秩

\[
r_k=\min(k,2D+1-k),\qquad1\le k\le2D.
\]

证明并非有限模式外推：k≤D 时，系数矩阵仅支撑在前 k 行列，反对角线
`i+j=k+1` 为 +1，其一侧为 0，因此该 k 阶块可逆。k>D 时仅支撑于
索引 k−D,...,D 的末尾 r_k 行列，反对角线 `i+j=k` 为 −1，其一侧为 0，同样可逆。
在 B 中，k≤D 的支撑块增加索引 0，其反对角线 `i+j=k` 全为 −1；
k>D 没有 b 项。因此 B 的 a_k 系数秩恰为
`r*_k=r_k+1_(k≤D)`。

对于任意线性矩阵铅笔，行列式在一个变量中的次数不超过该变量系数矩阵的秩：
按列多线性展开，选取超过其秩的系数列必定线性相关。这里所有多项式系数均整数，故

\[
F\det C\in\mathbb Z_{>0},\quad F^*\det\mathcal B\in\mathbb Z,
\quad
F=\prod_{k=1}^{2D}(N+k)^{9r_k},\quad
F^*=\prod_{k=1}^{2D}(N+k)^{9r_k^*}.
\]

写 G=F*/F=∏_(k=1)^D(N+k)^9，可重新表示
`r=−(F*det B)/[(Fdet C)G]`。分母为正整数，严格得到额外界

\[
\boxed{\operatorname{den}(r)\le F^*\det C.}
\]

可以与主稿 `ℓ^(9(D+1))det C` 取较小者。由于 Σr*_k=D²+2D，结合上一节
beta 上界，对于每个固定 D≥1 有

\[
\log\operatorname{den}(r)\le(8D^2+9D)\log N+O_D(1),\qquad N\to\infty.
\]

这项额外界优化某些有限因子和固定维数的幂次数，但不宣称改变主定理的平方窗口
量级，也不将其当成 den(r) 的下界或精确渐近。

## 6. 两平方极点全族阻碍：独立重构通过

限定 `m=2,h=2,S=1`、整数 1≤a<b，令 f_a=a⁸X+β_a，
β_a=−a⁸H_a−1/8+1/(2a)、d=b²−a²。完整三个矩条目的行列式独立展开为

\[
\Delta(X)=\frac3{4d}(f_a-f_b)-f_af_b,
\qquad [X^2]\Delta=-a^8b^8.
\]

这里 μ_9(1)=3/4 来自 Bernoulli 多项式商，不能删掉。

取 p≥5、b/2<p≤b、p∤ab。若 p≤a，H_a,H_b 只含一个 p 的倍数项，所以 β_a,β_b
估值都为 −9。因为 a>p、b<2p，0<b−a<p；若 p|a+b，则 a+b=3p，且
v_p(d)=1。因此 `(3/(4d))(β_a−β_b)` 的估值至少 −10，而 β_aβ_b 为 −18。
两项不能抵消，常数系数恰为 −18 估值；一次项至少 −9，二次项为单位，primitive
标量 c 的估值恰为 18。

若 p>a，则 β_a p 整，β_b 估值 −9。整数商
`(a⁸−b⁸)/(b²−a²)=−(a⁶+a⁴b²+a²b⁴+b⁶)` 使一次系数中的商项 p 整；
其唯一 −9 项为 −a⁸β_b，因此 c 估值至少 9。这一步无需假设 p∤d。

最高系数为整数且 c[X²]Δ 也是整数，故既约 c 的分母整除 a⁸b⁸。排除的顶部半区
素数乘积最多为 ab。于是统一下界含 `9(θ(b)−θ(b/2))−17log(ab)`，
并没有漏掉 c 在其他素数的负估值。

真实 determinant 的二重正积分公式正确：外部系数 1/2，分子为 `(y²−z²)²`。
取 I=[1/4,1/2]、J=[3/4,1]，两区间对称盒子的贡献抵消 1/2；
最小平方差为 25/256，面积为 1/16。仅保留密度的 ℓ=1 项、用 3<π<4 和 e<3，
独立核对 `w_9≥1/20643840`，所以稿中的显式常数

\[
C_*=\frac{25}{4096\cdot20643840^2},\qquad
\Delta(\zeta(9))\ge C_*\,(b^2+1)^{-4}
\]

正确且与 a 无关。合并 PNT，严格推出对任意 a=a(b)、1≤a<b 的统一结果

\[
\liminf_{b\to\infty}\frac{\log(c\Delta(\zeta(9)))}b\ge\frac92.
\]

若 a/b→ρ，则保留 p≤a 的额外九次成本给精炼下界 `9max(1/2,ρ)`。
此处即使 a 有界、极点间距变化、或者 a/b 没有极限，统一 9/2 结论仍成立。
它覆盖全部该限定族的逃向无穷参数序列，不是从有限失败网格外推；也没有排除
改变 h、S 或极点数量的其他构造。有限小值 (a,b)=(1,2) 与全族渐近增长并不矛盾。

## 7. 本审阅的计算证据与边界

本审阅者额外执行了只用标准库 Fraction/int 的内联独立检查，结果 PASS：

- D=1,...,12 的全部 312 个 C/B 单极点系数秩检查；
- M=2,...,8、D=1,...,7 的 49 个 beta Gram determinant 产品及 det C 上界检查；
- 相同 49 个参数的 Fdet C 与 F*det B 整数性、`den(r)≤F*det C` 检查。

原稿代理报告 Mellin verifier 的 1584 个 lcm、11209 个 Legendre 高次项、
54 个连续和 24 个稀疏 Schur、42 个 beta determinant 与正定序检查 PASS；
两极点代理报告 280 例、686 个 eligible prime 检查（104 个 p|d）PASS。
根代理另独立运行标准库 Fraction 检查，报告 2016 对参数、10109 个 prime 检查
（591 个 p|d）、6048 个三个取值的直接 determinant 检查，以及 2016 个 primitive
下界检查 PASS。后两组记录在各自稿件及证书，本审阅者不把其他人的运行说成自己的运行。

这些有限检查验证恒等式实现；本文件的 all-D 系数秩证明、调和数固定截断证明、
临界尺度推导及两极点统一 PNT 下率才承担无穷量词。标准 PNT 是外部已证明数学输入，
没有在本任务中 Lean 重建。旧 S/J 条件、未覆盖的 Mellin 参数区域和 ζ(9) 无理性仍开放。
