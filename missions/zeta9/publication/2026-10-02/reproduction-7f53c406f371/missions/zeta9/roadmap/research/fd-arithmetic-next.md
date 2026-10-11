# 五点端点求值 gcd 的 Smith 分解与 FD 的真实算术因子

本笔记对 [FC](t5-arithmetic-next.md) 的实际端点分母作进一步**精确分解**，并结合[五点窗的多项式增益](five-point-polynomial-gain.md)隔离 FD 真正需要的求值内容。它不是 FD、T5 或根定理的证明；所有渐近充分条件仍开放。以下统一使用实际 `p=9,m=n,deg W≤4` 矩阵，且 `n` 为偶数。

## 1. 原始伴随行恰是完整同余格的整数基

置 `q=d_n^9`、`A=qF_n∈Mat₅(Z)`、`C=S adj(A)`，并令 `δ₃`、`δ₄*` 为第七轮定义的低列最高子式内容与混合四阶子式内容。令 `\widetilde C=C/δ₄*∈Mat_{2×5}(Z)`。沿用饱和低核 `K`，原始二元像 `J=D K F Sᵀ`，Smith 等式 `UJV=diag(s₁,s₂)`，以及 `N=s₂/s₁`。则有矩阵的**精确等式**

\[
 \boxed{\quad
 \widetilde C
 =\operatorname{sgn}(\det A)\frac{s_2}{D}E
 =\operatorname{sgn}(\det A)
 V\operatorname{diag}(N,1)UK.
 \quad} \tag{1}
\]

因而 `\widetilde C` 的两行，不仅总体内容为 `1`，而且是完整同余格 `Λ_N` 的一组整数基，可能同时差一个负号。这比把十个条目仅解释为混合子式更具体。

**证明。** `F=A/q` 给 `E=S F^{-1}=qC/\det A`。由第七轮 `|\det A|=δ₃s₁(J_q)^2N`、`s₁(J_q)=δ₄*/δ₃`，及 FC 已证 `D/s₁=qδ₃/δ₄*`，逐项得到

\[
 \frac{|\det A|}{qδ₄*}
 =\frac{Nδ₄*}{qδ₃}=\frac{s_2}{D}.
\]

所以第一等式成立。再由 `E=DJ^{-1}K=(D/s₂)Vdiag(N,1)UK` 得第二等式。□

## 2. 求值 gcd 分裂成核内容与一个 Smith 局部因子

对**任意整数** `t`，令 `v(t)=(1,t,t²,t³,t⁴)ᵀ`、`x(t)=K v(t)∈Z²`；`x(t)≠0`，因为 `K` 两行线性独立的四次多项式不能有共同的复根并非自动成立，故这里若发生 `x(t)=0` 则以下公式只对 `x(t)≠0` 使用。设

\[
 c(t)=\gcd(x_1(t),x_2(t))>0,
 \qquad y(t)=Ux(t)/c(t)∈Z².
\]

因 `U` 幺模，`y(t)` primitive。令 `G(t)=gcd((\widetilde C_Bv(t)),(\widetilde C_Av(t)))`，取非负 gcd，则

\[
 \boxed{\quad G(t)=c(t)\gcd(N,y_2(t)).\quad} \tag{2}
\]

由此，对每个素数 `p`，

\[
 v_p(G(t))=v_p(c(t))+
 \min\{v_p(N),v_p(y_2(t))\}. \tag{3}
\]

这里 `v_p(0)=+∞`。尤其 **所有超出饱和核求值内容 `c(t)` 的约分只由 `p|N` 产生**，其素数不超过 `7n/2`，且额外指数不超过第七轮的 `v_p(N)` 界。这是实际矩阵的局部消去限制；它不控制 `c(t)` 自身，也不给 FD 所需的 gcd 指数下界。

**证明。** 式 (1) 与左侧 `V` 的幺模性给 `G(t)=gcd(N(Ux)_1,(Ux)_2)`。写 `Ux=c(y_1,y_2)`，则 `gcd(y_1,y_2)=1`，从而 `gcd(Ny_1,y_2)=gcd(N,y_2)`。式 (2)–(3) 随即成立。□

这个分解也有不用选 Smith 变换的形式。令 `M=J/s₁`，则 `M` 的 Smith 因子为 `1,N`，而[全局伴随生成式](shape-or-j-next.md)给

\[
 \boxed{\quad
 G(t)=\gcd\bigl((\operatorname{adj}M\,x(t))_1,
                 (\operatorname{adj}M\,x(t))_2\bigr).
 \quad} \tag{4}
\]

因为 `adj(M)=±Vdiag(N,1)U`，式 (4) 与 (2) 相同。这使每个实际样本 `t=k(k+n)` 的 gcd 可用 `K,M` 两个整数对象直接核算，不必构造五阶伴随矩阵。`c(t)` 还等于矩阵 `[L\mid v(t)]` 的全部 `4×4` 子式 gcd 除以 `δ₃(L)`，其中 `L` 是 `A` 的三列低 ζ 列。该等式对 `L` 作 Smith 变换：前三行给对角 `e₁,e₂,e₃`，后两行给 `K`，于是四阶子式内容为 `e₁e₂e₃ gcd(Kv(t))`。它是基础内容 `c(t)` 的另一种内禀表达，不是其增长上界。

若 `B(t)=\widetilde C_Bv(t)≠0`，实际比值 `r(t)=\widetilde C_Av(t)/B(t)` 的既约分母因此恰为

\[
 \boxed{\quad Q(t)=\frac{|B(t)|}{c(t)\gcd(N,y_2(t))}.\quad} \tag{5}
\]

这里 `B(t)` 是整数伴随行求值，和 DAG 的算术基线 `B_n` 名称不同。

## 3. 与第一输出高度和五点窗宽的精确结合

现在令 `n` 在 FQ/FI 的统一五点范围，`t_j=k_{n,j}(k_{n,j}+n)`，端点样本记为 `j_-`、`j_+`，并写 `G_±=G(t_{j_±})`。因为 (1) 给

\[
 |B(t_j)|=\frac{s_2}{D}\,Q_n^B(y_{n,j}),
\]

而最终正 Taylor 行的五个坐标彼此有统一有界比、`x_{n,j}=y_{n,j}-s_n` 位于正的固定紧区间，存在固定常数 `0<c_*<C_*`，对全部五点有

\[
 c_*\|U_{B,n}\|_2\le Q_n^B(y_{n,j})
 \le C_*\|U_{B,n}\|_2. \tag{6}
\]

式 (6) 可直接由正 Taylor 展开 `Q_n^B=Σ_i(u_n)_ix^i` 和有界可逆的 Taylor 换基得到，常数与 `j,n` 无关。于是端点既约分母的真实量级被**两个求值 gcd**完全隔离：

\[
 c_*\frac{s_2}{D}\frac{\|U_B\|}{\max(G_-,G_+)}
 \le\min(Q_-,Q_+)
 \le C_*\frac{s_2}{D}\frac{\|U_B\|}{\max(G_-,G_+)}. \tag{7}
\]

令 `\mu_N` 为 `Λ_N` 的加权第一极小值；第七轮格等式给 `\mu_N=(s₂/D)\lambda_{1,n}`。将式 (7) 代入 FC 的 FD 乘积，并记 `\eta_n=w_n\|U_B\|²/\Xi_n`，得到统一常数下的双边比较

\[
 c_*\frac{\mu_N\eta_n}{\max(G_-,G_+)}
 \le
 \frac{\lambda_{1,n}\|U_B\|}{\Xi_n}
 w_n\min(Q_-,Q_+)
 \le C_*\frac{\mu_N\eta_n}{\max(G_-,G_+)}. \tag{8}
\]

[五点多项式增益](five-point-polynomial-gain.md)给 `\eta_n\le C_1/\sqrt n`，所以一个**仍开放、但只含真实求值内容的充分目标**是

\[
 \max(G_-,G_+)\ge C_*C_1\,\mu_N/\sqrt n
 \quad\text{无穷次}. \tag{9}
\]

若 (9) 成立，式 (8) 的 FD 乘积至多 `1`，继而 T5 成立。式 (9) 需要指数级的实际 gcd，不能由“超出 `c(t)` 的因子只支持于 `N`”自动推出。当前没有 `\eta_n` 的相反下界，也不能从 (8) 推断 (9) 是 FD 的必要条件。

## 4. 精确有限探针与不能外推的现象

只读第六轮五个冻结 `search-input-n*.json.gz` 和第七轮 Smith 证书，直接从 `A=qF` 构造 `\widetilde C`。在 `n=12,24,48,96,192` 各自的 `k=n+1,n+2,n+5`，式 (1) 的行格标度及 (2)/(4) 的求值 gcd 全部以整数核对通过。特别地，`n=48,k=53,t=5353` 时 `c(t)=1`，而 `\gcd(N,y_2(t))=67`；所以“求值后的额外 Smith 约分只含 `p≤n`”这一自然简化在真实矩阵上**严格为假**。这并非合格的五点端点，也不否定对最终端点可能存在更强的局部结论。

这些冻结参数尚未进入 FQ 的统一五点范围，故这里没有报告其 `Q_-`、`Q_+` 或 FD 乘积。对接近 `k=n+1` 的几个普通整数样本，`​log|B(t)|/n` 约为 `20`，而 `log G(t)/n` 在这些有限规模远小于 `20`；此诊断提示式 (9) 的难度，但不构成任意渐近上下界。根定理、FD 及真实端点的统一 gcd 估计保持开放。
