# 完整输出格的精确椭圆范数与两种极小值行为

2026-09-29。本稿使用新证明的真实面积指数，把完整整数输出格的范数和
剩余固定方向问题写成一个统一的二维形式。这里的格是 Z²E_nW_n，
不是部分同余输出子格 H_n；两者的极小值不能混用。

令 θ=ζ(9)，U_n=(1,0)E_nW_n、V_n=(0,1)E_nW_n，
D_n=V_n−θU_n，Xi_n=||U_n∧V_n||。定义正数与有理数

\[
t_n=\|U_n\|,\qquad s_n=\frac{\Xi_n}{t_n},\qquad
\xi_n=\frac{\langle U_n,V_n\rangle}{t_n^2}\in\mathbb Q,
\qquad\eta_n=\frac{s_n}{t_n}>0.
\]

符号 t_n、s_n 仅在本稿表示实尺度，不是 Smith 因子、同余倍数或旧 Taylor
移位。η_n² 是有理数，η_n 本身不必有理。

## 1. 不含误差项的范数恒等式

对所有实数 b,a，正交分解 V_n=ξ_nU_n+V_n^⊥ 给出

\[
\boxed{\|(b,a)E_nW_n\|^2
=t_n^2\bigl((b+a\xi_n)^2+\eta_n^2a^2\bigr).}           \tag{1}
\]

因为 ||V_n^⊥||=Xi_n/t_n，式 (1) 是精确恒等式。其全部系数 t_n²、ξ_n、
η_n² 均可直接从有理 F_n 求出，完全不需要 ζ 的数值。

[实际面积下界稿](../roadmap/research/inverse-area-lower-next.md)已证明
U_n 与 D_n 的夹角远离 0 和 π。结合 `Xi_n=||U_n∧D_n||` 得
`||D_n||≤C s_n`。因此

\[
\kappa_n:=\frac{\xi_n-\theta}{\eta_n}
=\frac{\langle U_n,D_n\rangle}{\Xi_n}
\quad\text{一致有界}.                                    \tag{2}
\]

置 x=t_n(b+aθ)、y=s_na，则 (1) 变为 `(x+κ_n y)²+y²`。
矩阵 `[[1,κ_n],[0,1]]` 及其逆的范数一致有界，故存在与 n、a、b 无关
的常数 c,C>0，使所有充分大偶数 n 与所有实数输出满足

\[
\boxed{c\{t_n|b+a\theta|+s_n|a|\}
\le\|(b,a)E_nW_n\|
\le C\{t_n|b+a\theta|+s_n|a|\}.}                         \tag{3}
\]

这是对**所有移动输出方向**统一的比较，不只是固定 (b,a) 的渐近。
它仍保留 θ；不能将此恒等式当成 θ 无理的证明。

## 2. 两个实尺度现在都已确定

记 A=λ1>0、B=|λ2|，以及

\[
\alpha=\tfrac12\log A,\quad\beta=\tfrac12\log B,
\quad\gamma=\tfrac14\log(AB),\quad\delta=\tfrac14\log(A/B).
\]

因此 α=γ+δ、β=γ−δ。已有固定行尺度及
[新外积定理](exterior-cone-2026-09-29.md)给

\[
\log t_n/n\to\alpha,\qquad\log s_n/n\to\beta,
\qquad\log\eta_n/n\to-2\delta.
\]

数值约为 α=10.5641538376，β=0.4529340708，γ=5.5085439542，
δ=5.0556098834。更完整的 n⁵ 渐近由已证
[共同模态定理](../roadmap/research/cp-stable-next.md)与确定第二模态的
新面积定理合用：t_n∼C_t n⁵A^(n/2)，s_n∼C_s n⁵B^(n/2)，C_t,C_s>0。

于是 (1) 也说明 ξ_n 是误差 O(η_n) 的有理中心，但小误差并未同时给
既约分母的充分上界。比如偶数 n 上 `θ=1, ξ_n=1+(-1)^(n/2)/2^n` 本身就能有
交替且指数收缩的有理中心；必须另外使用真实族的算术。

## 3. 对全部非零整数输出的新统一下界

若 a≠0 为整数，(1) 立即给 `||(b,a)E_nW_n||≥s_n`。
若 a=0、b≠0 为整数，则长度至少 t_n。又 t_n/s_n→∞，故对充分大 n

\[
\boxed{\lambda_{1,n}\ge s_n
\sim C_s n^5 B^{n/2}.}                                  \tag{4}
\]

特别地，所有非零整数输出的逆像范数均趋于无穷，且
`liminf log λ1,n/n≥β>0.4529`。这与其**实值线性形式**趋于零不冲突：
实值泛函自身按 n⁻⁵A^(−n/2) 衰减。

另一方面，二维 Hermite 界给 `λ1,n≤C sqrt(Xi_n)`。面积与独立格向量
长度积比较，以及两个固定坐标输出行，给

\[
\beta\le\liminf\frac{\log\lambda_{1,n}}n
\le\limsup\frac{\log\lambda_{1,n}}n\le\gamma,
\]

\[
\gamma\le\liminf\frac{\log\lambda_{2,n}}n
\le\limsup\frac{\log\lambda_{2,n}}n\le\alpha.             \tag{5}
\]

这里不能在无证明时把 λ1 的上指数写成每个 n 的增长率。

## 4. 固定方向与无穷换向对应不同端点

**若 θ=c/d 有理（既约且 d>0），** 由已证临界格形结论，充分大 n 的
唯一 primitive 第一输出为 ±(−c,d)。若实际泛函的平面 Riesz 范数为
r_n，则 r_n=Θ(n⁻⁵A^(−n/2))，且

\[
\lambda_{1,n}=d\Xi_n r_n,\qquad
\lambda_{2,n}\sim1/(d r_n).
\]

所以两个指数极限都存在，并且

\[
\boxed{\log\lambda_{1,n}/n\to\beta,
\qquad\log\lambda_{2,n}/n\to\alpha.}                   \tag{6}
\]

**若 θ 无理，** 每个第一整数输出对应的实值都以固定指数趋零：这是
Hermite、γ<τ 与既有统一解析界的直接后果。因此其 primitive 输出方向
不可能最终固定，否则某个固定非零整数形式值须等于零。方向必无穷次改变。

令真实加权连接及其逆的算子范数最终都不超过 C。完整输出格在相邻 n
使用相同 Z² 坐标，故 λ1,n+2≤C λ1,n。若相邻第一输出不同向，将后一个
输出放回前一个参数就给

\[
\lambda_{2,n}\le C\lambda_{1,n+2}\le C^2\lambda_{1,n}.
\]

结合 `Xi_n≤λ1,n λ2,n` 和 Hermite，这些换向参数同时满足
`C⁻¹ sqrt(Xi_n)≤λ1,n≤C' sqrt(Xi_n)`，λ2,n 亦与 sqrt(Xi_n) 可比。
于是

\[
\boxed{\limsup\log\lambda_{1,n}/n=\gamma,
\qquad\liminf\log\lambda_{2,n}/n=\gamma.}               \tag{7}
\]

式 (6) 与 (7) 有 δ≈5.05561 的明确间隔。反过来，任一 (7) 的等式
也排除有理性，因为 β<γ<α。因此它们是新的**等价诊断**，而非无理性
证明。本轮没有证明实际 λ1 的 limsup 到达 γ，也没有证明 λ2 的 liminf
降至 γ。已经证明的是 (1)–(5) 的无条件结构及 (6)–(7) 的严格条件分支。

## 5. 这怎样约束下一步

式 (3) 把难点保留得很清楚：找到非零且足够小的整数输出，需要控制
`|b+aθ|` 与 `|a|` 的平衡。纯实连接已确定两个尺度；尚缺真实整数方向
不能最终精确落在 `b+aθ=0` 上的理由。把实模态、正性或面积再精细化，
不能独自提供这个理由。应继续检验真实局部同余斜率和约分后的分母，
并把任何有限证据与无穷量词分开。

## 6. 精确核验

[verify_output_normal_form.py](../scripts/verify_output_normal_form.py)在五个真实
参数 n=2,12,20,48,96 上，以有理数核对整个 Gram 椭圆恒等式、完整 Z²
输出的精确 Gauss 规约、第一极小值下界及 Hermite 界。指数常数使用已隔离
根的有理区间与带显式余项的对数级数核验，保存于
[证书](../verification/output-normal-form-2026-09-29/certificate.json)。
这些有限检查只检验公式和实现；第 1–4 节的全参数结论由上述代数与几何
证明承担。全文已获独立代理审查，尚未 Lean 形式化。
