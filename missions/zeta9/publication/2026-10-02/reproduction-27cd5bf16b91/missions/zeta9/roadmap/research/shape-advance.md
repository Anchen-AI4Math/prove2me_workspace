# S 的内禀局部斜率与一个结构限制

本笔记推进 [shape-obligation.md](shape-obligation.md) 的第 1 步：把依赖 Smith 左变换的同余写成可由原始整数像直接计算的条件。另给出一个抽象格族，严格说明 Smith 模数、部分模数、面积甚至固定底格本身都不足以推出 `S`。它不是实际 ζ(9) 格族的反例；`S`、`J` 和根定理仍开放。

## 内禀整数矩阵与逐素数单列判据

固定任一偶数 `n≥2`，暂略下标。沿用 `J=D K F Sᵀ∈Mat₂(Z)`、`s₁|s₂`、`N=s₂/s₁`。置

\[
M=J/s₁\in\operatorname{Mat}_2(\mathbb Z),\qquad
\det M=\pm N,\qquad \gcd(M_{11},M_{12},M_{21},M_{22})=1. \tag{1}
\]

因此 `M` 的 Smith 因子为 `1,N`。对任意 `g|N` 和任意 `z∈Z²`，

\[
\boxed{\quad zK\in\Lambda_g\ \Longleftrightarrow\ zM\equiv(0,0)\pmod g.\quad} \tag{2}
\]

对 primitive `z`，记 `c(z)=gcd((zM)_1,(zM)_2)`，取非负 gcd 并约定 `gcd(0,0)=0`。则第七轮的最小倍数有完全不依赖 Smith 变换的表达：

\[
\boxed{\quad t_g(z)=\frac g{\gcd(g,c(z))},\qquad
\mu_1(\Lambda_g)=\min_{z\text{ primitive}}
\frac g{\gcd(g,c(z))}\,\|zK\|.\quad} \tag{3}
\]

实际计算 `M` 时可直接取 `q=d_n^9` 的清分母像 `J_q=q K F Sᵀ`，再除以其四项的 gcd：`M=J_q/s₁(J_q)`。这是因为 `J_q=(q/D)J`，而正有理公共标度在除去矩阵内容后抵消。`K` 更换幺模行基只会同时更换 `z` 坐标，不改变 (2)–(3) 的格或极小值。

更局部地，令 `p^e|g`，从 `M` 选一列 `C_p∈Z²`，要求该列至少有一项不被 `p` 整除。这种列总存在，因为 `M` 四项的 gcd 为 1 且其 Smith 第一因子为 1。对每个 `0≤k≤e`，

\[
zM\equiv0\pmod{p^k}
\quad\Longleftrightarrow\quad z\cdot C_p\equiv0\pmod{p^k}. \tag{4}
\]

于是令 `v_p(0)=+∞`，精确地有

\[
v_p(t_g(z))=e-\min\{e,v_p(z\cdot C_p)\}. \tag{5}
\]

这把 [原逐素数目标](shape-obligation.md) 的每个局部项缩成一条由正整数矩阵 `J_q/s₁(J_q)` 给出的线性形式；选择哪一列或哪组 Smith 变换均不影响截断估值。具体说，`S` 等价于：对每个 `η>0`，所有充分大的偶数 `n` 和所有 primitive `z`，

\[
\log\|zK_n\|_n+
\sum_{p|g_n}\left(e_{p,n}-\min\{e_{p,n},v_p(z\cdot C_{p,n})\}\right)\log p
\ge\tfrac12\log(g_n\Delta_n)-\eta n. \tag{6}
\]

式 (6) 仍保留对所有短 primitive 方向的全称量词，不能仅凭局部表达证明 `S`。

**证明。** 任取 Smith 等式 `UJV=diag(s₁,s₂)`，得 `M=U⁻¹diag(1,N)V⁻¹`。令 `zU⁻¹=(a,b)`，则 `zM=(a,Nb)V⁻¹`。因 `g|N`，`zM≡0 mod g` 当且仅当 `a≡0 mod g`，这与 `\Lambda_g` 的定义等价；幺模右乘保持整数分量生成的理想，故 `gcd(g,c(z))=gcd(g,a)`，得到 (2)–(3)。对 (4)，`det M` 被 `p^e` 整除；若 `C_p` 的某项是模 `p` 单位，则对每个 `k≤e`，另一列因行列式为零而在 `Z/p^kZ` 中是 `C_p` 的倍数。因此一个点积消失就等于两个点积同时消失。(5) 随即由模 `p^k` 的最大消失阶数得到，(6) 再由 (3) 与 `S` 的原等价式得到。

## 斜率自由度：相同模数和面积可以有相反的指数形状

以下是一般二维 Smith 同余格的**结构限制例**，不是 ζ(9) 的 `K_n,J_n`。令偶数 `n` 趋于无穷，设

\[
m_n=\prod_{p\le n}p,\qquad g_n=N_n=m_n^2,
\qquad K=I_2,\quad \Delta=1,
\qquad J_{R,n}=\begin{pmatrix}1&0\\R&m_n^2\end{pmatrix}. \tag{7}
\]

每个 `J_{R,n}` 都有 Smith 因子 `1,m_n²`，且 `m_n|d_n`，故 `g_n=gcd(N_n,d_n²)=m_n²`，恰满足路线图使用的部分模数规则。由 (2)，

\[
\Lambda_{g_n}(R)=\{(x,y)∈Z²:x+Ry\equiv0\pmod{m_n²}\}. \tag{8}
\]

取 `R=0` 时，`(0,1)∈\Lambda` 且 `\mu_1=1`，所以 `\sigma_n=\log m_n/n→1`（素数定理）。取 `R=m_n` 时，任一格点可写为

\[
(x,y)=(m_n(m_nk-y),y),\qquad k,y∈Z.
\]

非零格点若 `m_nk-y≠0`，则 `|x|≥m_n`；否则 `|y|≥m_n`。而 `(0,m_n)` 在格中，故 `\mu_1=m_n=\sqrt{g_n\Delta}`，从而 `\sigma_n=0`。两族甚至使用相同的 `K`、`N`、`g`、`\Delta` 和素数估值 `e_{p,n}`；只改变局部同余斜率，`S` 的真值就不同。

这种自由度逐素数仍然存在。给定任意 `g|N` 和每个 `p^e||g` 的剩余类 `r_p mod p^e`，中国剩余定理给出 `R mod g`，使 `J_R=[[1,0],[R,N]]` 的局部条件同时为 `x+r_p y≡0 mod p^e`。因此从 `e_{p,n}` 或 `N_n` 的增长本身无法推断实际斜率与加权底格的相对位置。下一步须在真实 `J_{q_n}/s₁(J_{q_n})` 的单列形式上建立统一的跨素数或短方向约束；有限样本和本抽象例都不能裁决实际 `S`。
