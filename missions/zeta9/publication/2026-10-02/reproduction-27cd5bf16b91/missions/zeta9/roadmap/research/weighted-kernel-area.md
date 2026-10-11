# 饱和整数核的加权面积恒等式

这是 `V` 的一个新代数输入，适用于任意 `5×3` 满秩整数矩阵；它没有给出 `V` 所需的渐近上界。

## 定理

设 `L∈Z^{5×3}` 的列秩为三，`δ₃>0` 是十个最高阶三阶子式的 gcd。令 `K∈Z^{2×5}` 的两行构成饱和整数核 `ker_Z(Lᵀ)` 的一组基。对任意正对角矩阵 `W=diag(w₀,…,w₄)`，记 `Δ(KW)` 为两行张成的二维面积，则

\[
\boxed{\quad
\Delta(KW)^2=
\frac{(\prod_{r=0}^4w_r)^2}{\delta_3^2}
\det(L^{\mathsf T}W^{-2}L).
\quad} \tag{1}
\]

等价的完全整数形式是

\[
\boxed{\quad
\delta_3^2\Delta(KW)^2
=\sum_{\substack{J\subset\{0,1,2,3,4\}\\|J|=3}}
\det(L_J)^2\prod_{i\notin J}w_i^2.
\quad} \tag{2}
\]

这里 `L_J` 按自然行序取 `3×3` 子矩阵。式 (2) 不需要平方根或实数近似，适合整数证书。

## 证明

对 `L` 作整数 Smith 变换：存在幺模 `P∈GL₅(Z)`、`Q∈GL₃(Z)`，使 `PLQ=[diag(e₁,e₂,e₃);0]`，其中 `e_i>0`。最高阶子式生成的理想在幺模变换下不变，故 `δ₃=e₁e₂e₃`。`P` 的最后两行构成 `ker_Z(Lᵀ)` 的饱和基：若 `xL=0`，把 `x` 写为 `yP`，则 `y[diag(e_i);0]=0` 强制前三个 `y_i=0`。任何别的饱和基只相差一个 `GL₂(Z)` 变换，不改变各二阶子式的绝对值。

设 `I` 是两个行指标、`J=Iᶜ`。Jacobi 互补子式恒等式应用于幺模 `P`，结合 `L=P⁻¹[diag(e_i);0]Q⁻¹`，得到

\[
|\det K_I|=\frac{|\det L_J|}{\delta_3}. \tag{3}
\]

由 Cauchy–Binet，`Δ(KW)²=det(KW²Kᵀ)=Σ_{|I|=2} det(K_I)²∏_{i∈I}w_i²`。代入 (3) 即为 (2)。再对 `LᵀW⁻²L` 使用 Cauchy–Binet，并乘 `(∏w_i)²/δ₃²`，恰得 (1)。证毕。

## 套用到 ζ(9)

取 `q_n=d_n⁹`、`A_n=q_nF_n∈Mat₅(Z)`，令 `L_n` 为 `A_n` 的 `A₃,A₅,A₇` 三列。第七轮的 `K_n` 正是 `ker_Z(L_nᵀ)` 的饱和基。令 `W_n=diag(1,n²,n⁴,n⁶,n⁸)`，则 `∏w_i=n²⁰`，从 (1) 得

\[
\log\Delta_n=20\log n-\log\delta_{3,n}
+\tfrac12\log\det(L_n^{\mathsf T}W_n^{-2}L_n). \tag{4}
\]

它将 `V` 的面积率转成一个**固定 `3×3` Gram 行列式**与三阶子式 gcd 的估计。式 (4) 本身不能推出 `limsup B_n<10.564`。后续的[Smith 内容消去式](volume-cancellation.md)把这里的 `D_n/s₁,n` 与面积一起化简，继而由[逆像面积统一界](inverse-area-rate.md)控制几何部分；目前还须估计 `N_n/g_n` 的算术指数。

具体地，DAG 中的算术基线可重写为

\[
B_n=\frac1n\left\{
\log\frac{D_n}{s_{1,n}}+10\log n
-\frac12\log\delta_{3,n}
+\frac14\log\det(L_n^{\mathsf T}W_n^{-2}L_n)
-\frac12\log g_n\right\}. \tag{5}
\]

`10 log n/n→0`。这条分项公式仍可用于逐素数分析，但不能单独把 `δ₃` 的增长当作结论，因为 Gram 行列式和 `g_n` 可能抵消它。上面链接的消去式给出更简洁的等价组合。

[有限整数核验](../verification/finite-audit.json)从第六轮冻结的完整有理形式矩阵独立构造 `L_n`，对 `n=12,24,48,96,192` 逐一检查式 (2)。五例是实现回归；定理对所有满秩矩阵的证明在上文 Smith、Jacobi、Cauchy–Binet 三步。
