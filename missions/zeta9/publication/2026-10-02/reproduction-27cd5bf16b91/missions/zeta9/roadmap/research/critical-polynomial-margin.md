# 第二逐次极小值的临界多项式裕量

记 `\Lambda_n=\mathbb Z^2E_nW_n⊂\mathbb R^5` 的两项欧氏逐次极小值为 `\lambda_{1,n}≤\lambda_{2,n}`，Gram 面积为 `\Xi_n`。本文把[真实高斯矩渐近](moving-short-sign-next.md)、[Taylor 最终正性](taylor-connection-next.md)及[面积上界](inverse-area-rate.md)合用，给出一个**等价于无理性**的临界判据。它不是 `\zeta(9)` 无理性的证明；现有连接/Smith 上界没有提供判据需要的第二极小值估计。

令

\[
 \alpha=-f_*,\qquad T_n=n^5e^{\alpha n},\qquad
 C_Z=\frac{(2\pi)^4g(x_*)}{\sqrt a}>0,\qquad
 v_*=(1,y_*,y_*^2,y_*^3,y_*^4),\qquad
 \gamma=\tfrac14\log(3\,711\,015\,000)<\alpha.
\]

高斯矩结论给 `Z_n\sim C_Z/T_n`。下文的极限均沿偶数 `n→∞`。

## 1. 两条固定输出行恰在临界尺度

置 `A_n=(1,0)E_nW_n`、`B_n=(0,1)E_nW_n`。对 `y_{n,k}=k(k+n)/n²`，令

\[
 v_n=\left(\sum_{k>n}\mu_n(k)y_{n,k}^r\right)_{r=0}^4
 \longrightarrow v_*.
\]

完整输出值的精确关系为

\[
 Z_nv_n\cdot A_n=1,\qquad Z_nv_n\cdot B_n=\zeta(9).
\tag{1}
\]

故 Cauchy–Schwarz 已给 `\|A_n\|,\|B_n\|\gg Z_n^{-1}`。反向上界需要真实方向信息：令 `s_n=u_{0,n}/n²→2`，把两行变换成归一化 Taylor 系数 `A_nB(s_n),B_nB(s_n)`。TA 已证这十个系数对全部充分大偶数 `n` 严格为正。对应的非归一化正矩

\[
 h_{j,n}=\sum_{k>n}R_n(k)(y_{n,k}-s_n)^j
 \quad(0≤j≤4)
\]

满足 `h_{j,n}/Z_n→(y_*-2)^j>0`，因为 `x_*>1`。输出恒等式给 `\sum_j(A_nB(s_n))_j h_{j,n}=1` 和第二行的相同和等于 `\zeta(9)>0`。逐项正性遂给每个 Taylor 系数 `O(Z_n^{-1})`；`B(s_n)^{-1}` 一致有界。因此

\[
 \boxed{\|A_n\|=\Theta(T_n),\qquad\|B_n\|=\Theta(T_n).}
\tag{2}
\]

特别地，单独用精确连接去证明这两条固定生成行是 `o(T_n)` 不可能：式 (1) 已给出相反的下界。第二极小值的临界改进必须来自**随 `n` 变化的整数线性组合**。

面积界给 `\Xi_nZ_n^2→0`，因为 `\limsup\log\Xi_n/(2n)≤\gamma<\alpha`。将 (2) 中两行乘 `Z_n` 后，它们有界、第一行范数远离零，且外积范数趋零。再用 (1) 固定两行的输出比值，得到

\[
 \boxed{Z_n\|B_n-\zeta(9)A_n\|\longrightarrow0.}
\tag{3}
\]

具体地，写 `Z_nB_n=t_nZ_nA_n+r_n` 且 `r_n⊥A_n`。面积给 `\|r_n\|=Z_n²\Xi_n/\|Z_nA_n\|→0`；(1) 给 `\zeta(9)-t_n=v_n\cdot r_n→0`，从而 (3)。

## 2. 临界第二极小值恰好判别有理性

**定理。** 在上述已证事实下，

\[
 \boxed{\displaystyle
 \zeta(9)\notin\mathbb Q
 \quad\Longleftrightarrow\quad
 \lambda_{2,n}=o(T_n)
 \quad\Longleftrightarrow\quad
 \liminf_{\substack{n\to\infty\\2\mid n}}\frac{\lambda_{2,n}}{T_n}=0.}
\tag{4}
\]

实际上只要沿某个无穷偶数子序列有 `\lambda_{2,n}/T_n→0`，就足以推出无理性。

若 `\zeta(9)` 无理，则对任意 `\varepsilon>0`，可取两个**固定且线性无关**的整数对 `z_i=(b_i,a_i)`，使 `|b_i+a_i\zeta(9)|<\varepsilon`；例如取足够后的两个相邻连分数渐近分数。由 (2)–(3)，

\[
 Z_n\|z_iE_nW_n\|
 \le |b_i+a_i\zeta(9)|Z_n\|A_n\|
 +|a_i|Z_n\|B_n-\zeta(9)A_n\|
 \le C\varepsilon+o(1).
\]

两个像向量仍线性无关，因为 `E_nW_n` 行秩二；令 `\varepsilon→0`，得到 `\lambda_{2,n}Z_n→0`，等价于右边的 `o(T_n)`。

反之，若 `\zeta(9)=c/d` 为既约有理数，`d>0`，则任意两个线性无关的整数输出中至少一个满足 `db+ca≠0`。该输出的真实值绝对值至少 `1/d`；由 (1) 对任意整数对成立的线性形式及 Cauchy–Schwarz，

\[
 \boxed{\displaystyle
 \liminf_{n\to\infty,\,2\mid n}
 \frac{\lambda_{2,n}}{T_n}
 \ge\frac{1}{dC_Z\|v_*\|}>0.}
\tag{5}
\]

这给出式 (4) 的逆向，也说明有理性假设下存在临界尺度的**固定正下界**。

## 3. 可检查的几何形式及仍缺的工作

二维格的逐次极小值与面积满足通用比较

\[
 \Xi_n\le\lambda_{1,n}\lambda_{2,n}
 \le\frac4\pi\Xi_n;
\tag{6}
\]

左边来自独立格向量的外积，右边是二维 Minkowski 第二定理。因此 (4) 也等价于

\[
 \boxed{\displaystyle
 \frac{\lambda_{1,n}}{\Xi_n Z_n}\longrightarrow\infty.}
\tag{7}
\]

在假设 `\zeta(9)=c/d` 时，固定 primitive 零方向 `z_*=(-c,d)` 的行向量垂直于输出线性泛函在二维行平面上的 Riesz 向量。平面面积公式精确给

\[
 \|z_*E_nW_n\|
 =d\Xi_n\,\|L_n|_{\operatorname{row}(E_nW_n)}\|
 \le d\Xi_nZ_n\|v_n\|.
\]

故 `\lambda_{1,n}/(\Xi_nZ_n)≤d\|v_n\|=O(1)`，与 (7) 正好相反。现有面积**上界**和 Smith 模数恒等式没有给出 (7) 的下界；它们允许第一方向在有理性假设下沿固定零关系缩得足够快。因此仅把连接谱的主指数 `\alpha=-f_*` 与面积指数相比较，不能关闭临界的 `n^5` 裕量。

### 有理假设下的精确格形

上面的必要估计还可以精确化。令 `P_n=row(E_nW_n)`，并把输出线性泛函在这个二维平面上的 Riesz 范数记为

\[
 \mathfrak r_n=\|L_n|_{P_n}\|
 =Z_n\|\operatorname{proj}_{P_n}v_n\|.
\]

由 `L_n(A_n)=1` 及 (2)，`\mathfrak r_n≥1/\|A_n\|\gg Z_n`；Cauchy–Schwarz 给 `\mathfrak r_n≤Z_n\|v_n\|=O(Z_n)`，故 `\mathfrak r_n=\Theta(Z_n)`。仍假设 `\zeta(9)=c/d`，置 `k_n=(-c,d)E_nW_n`。取固定 Bézout 整数对 `(b_0,a_0)` 使 `db_0+ca_0=1`，其像 `w_n=(b_0,a_0)E_nW_n` 与 `k_n` 构成完整格的整基。因为 `L_n(k_n)=0`、`L_n(w_n)=1/d`，第二基向量对零方向的垂直高度为 `h_n=1/(d\mathfrak r_n)`，并有精确面积关系

\[
 \|k_n\|=d\Xi_n\mathfrak r_n,\qquad
 \frac{\|k_n\|}{h_n}=d^2\Xi_n\mathfrak r_n^2
 \le d^2\Xi_nZ_n^2\|v_n\|^2\longrightarrow0.
 \tag{8}
\]

任意**形式值非零**的整数输出长度至少 `h_n`，而形式值为零的整数向量恰为 `k_n` 的整数倍。因此全部充分大偶数 `n` 上，最短向量**恰是** `±k_n` 且 `\lambda_{1,n}=\|k_n\|`。在第二基向量上加减整数倍 `k_n`，可把平行分量减到 `\|k_n\|/2` 以内，故

\[
 h_n\le\lambda_{2,n}
 \le\sqrt{h_n^2+\|k_n\|^2/4},\qquad
 \boxed{\lambda_{2,n}\sim\frac1{d\mathfrak r_n},\quad
 \frac{\lambda_{1,n}\lambda_{2,n}}{\Xi_n}\to1,\quad
 \frac{\lambda_{1,n}}{\Xi_nZ_n}
 =d\frac{\mathfrak r_n}{Z_n}=\Theta(1).}
 \tag{9}
\]

这里得到的是零方向**相对**第二方向和面积尺度短：`\lambda_{1,n}^2/\Xi_n=d^2\Xi_n\mathfrak r_n^2→0`；没有证明 `\lambda_{1,n}→0`。事实上仅由当前面积上界可得 `\limsup n^{-1}\log\lambda_{1,n}≤2\gamma-\alpha`，这个上界为正。

具体下一步可直接使用精确 Gauss/Smith 行计算 `\lambda_{1,n}` 与 `\Xi_n`，并研究**整个无穷偶数序列**上的比值 `\lambda_{1,n}/(\Xi_nZ_n)`。证明它趋于无穷（甚至沿某无穷子序列趋于无穷）即可完成无理性证明；有限参数上的上升趋势没有此效力。另一条等价路线是直接证明相应子序列 `\lambda_{2,n}Z_n→0`。两条路线都需要超出现有面积/谱上界的整数方向控制。
