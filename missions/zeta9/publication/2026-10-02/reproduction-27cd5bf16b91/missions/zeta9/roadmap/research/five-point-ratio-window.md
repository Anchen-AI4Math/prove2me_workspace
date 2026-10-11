# 五点比值窗：严格夹逼、谱宽界与弱同号的端点

本文只用 [TA](taylor-connection-next.md) 的最终 Taylor 正性及 [FQ 五点精确正求积](moving-short-sign-next.md#6-五个预定实际取样点的精确正求积)，证明五点比值窗的非退化、严格夹逼和宽度界。弱同号允许端点，故其准确条件是避开**开区间**；避开闭区间对应五项严格同号。

## 定义与统一参数范围

记 `χ=-f''(x_*)>0`，并取 FQ 的预定实际样本

\[
 k_{n,j}=\left\lfloor nx_*+j\sqrt{n/\chi}+\frac12\right\rfloor,
 \qquad y_{n,j}=\frac{k_{n,j}(k_{n,j}+n)}{n^2},\qquad -2\le j\le2.
\]

令 `q_{n,z}(y)=Σ_{r=0}^4(zE_n)_r n^{2r}y^r`，并记

\[
 Q_n^B=q_{n,(1,0)},\qquad Q_n^A=q_{n,(0,1)},\qquad
 s_n=\frac{(n+1)(2n+1)}{n^2}.
\]

存在一个与输出 `z` 无关的偶数 `N`，使全部偶数 `n≥N` 同时满足：TA 的十个 Taylor 系数 `α_{r,n},β_{r,n}` 严格正；FQ 的五个权重 `ω_{n,j}` 严格正；五个 `k_{n,j}` 互异且严格大于 `n+1`。最后一项由 `x_*>1` 和 `k_{n,-2}=nx_*+O(√n)` 得到。因此 `y_{n,j}>s_n`。

下文一律在这个统一范围内。Taylor 展开给

\[
 Q_n^B(y)=\sum_{r=0}^4 n^{2r}\alpha_{r,n}(y-s_n)^r,
 \qquad
 Q_n^A(y)=\sum_{r=0}^4 n^{2r}\beta_{r,n}(y-s_n)^r.
\tag{1}
\]

所以五个分母 `Q_n^B(y_{n,j})` 和分子 `Q_n^A(y_{n,j})` 全部严格正，且为有理数。定义

\[
 r_{n,j}=\frac{Q_n^A(y_{n,j})}{Q_n^B(y_{n,j})},\qquad
 \ell_n=\min_j r_{n,j},\quad h_n=\max_j r_{n,j}.
\]

## 非退化与严格夹住 ζ(9)

设 `Z_n=Σ_{k>n}R_n(k)>0`。分别把 FQ 用于 `Q_n^B,Q_n^A`，由两个输出的真实值 `1,ζ(9)`，得到

\[
 1=Z_n\sum_j\omega_{n,j}Q_n^B(y_{n,j}),\qquad
 \zeta(9)=Z_n\sum_j\omega_{n,j}Q_n^A(y_{n,j}).
\]

置 `θ_{n,j}=Z_nω_{n,j}Q_n^B(y_{n,j})`，便有

\[
 \theta_{n,j}>0,\qquad \sum_j\theta_{n,j}=1,\qquad
 \zeta(9)=\sum_j\theta_{n,j}r_{n,j}.
\tag{2}
\]

五个比值不能全相同：否则某个 `r` 使次数至多四的 `Q_n^A-rQ_n^B` 在五个不同 `y_{n,j}` 上为零，故该多项式恒零，与 `E_n` 的两行线性独立矛盾。因此 `ℓ_n<h_n`，而 (2) 给

\[
 \boxed{\ell_n<\zeta(9)<h_n.}
\tag{3}
\]

不需要各比值按 `j` 排序，也不要求它们两两不同；最小值或最大值可以重复出现。

## 五点窗严格位于 Taylor 窗内

记 `ρ_{r,n}=β_{r,n}/α_{r,n}`，以及 TA 的端点

\[
 L_n=\min_r\rho_{r,n},\qquad H_n=\max_r\rho_{r,n},\qquad I_n=H_n-L_n>0.
\]

由 (1)，每个 `r_{n,j}` 是五个 `ρ_{r,n}` 的加权平均，权重正比于

\[
 n^{2r}\alpha_{r,n}(y_{n,j}-s_n)^r>0.
\]

五个 Taylor 比值不全相同，同样由行秩二得到。因此每个平均都严格位于 Taylor 两端之间，故

\[
 \boxed{L_n<\ell_n<\zeta(9)<h_n<H_n,\qquad
 0<h_n-\ell_n<I_n.}
\tag{4}
\]

由[已证 Taylor 谱率](taylor-window-rate.md)，随即有

\[
 \limsup_{\substack{n\to\infty\\2\mid n}}
 \frac{\log(h_n-\ell_n)}n
 \le\limsup\frac{\log I_n}n<-10.1109.
\tag{5}
\]

所以对每个 `κ<10.1109`，最终有 `h_n-ℓ_n≤e^{-κn}`，以及全部 `|r_{n,j}-ζ(9)|≤e^{-κn}`。这里没有证明五点窗自身在 `n→n+4` 下嵌套：它位于各自参数的 Taylor 窗内，不足以推出两个不同参数的五点窗包含关系。

## T5 的精确斜率条件及端点反例

任取非零整数输出 `z=(b,a)`。对每个五点样本，

\[
 q_{n,z}(y_{n,j})=Q_n^B(y_{n,j})(b+a r_{n,j}).
\tag{6}
\]

若 `a=0`，则 `b≠0`，五项全部严格同号，符号就是 `sign b`；不定义斜率。

若 `a≠0`，置 `p=-b/a`。正分母及 (6) 给准确等价式

\[
 \boxed{\begin{aligned}
 \text{五项弱同号}&\iff p\le\ell_n\ \text{或}\ p\ge h_n
                    \iff p\notin(\ell_n,h_n),\\
 \text{五项严格同号}&\iff p<\ell_n\ \text{或}\ p>h_n
                    \iff p\notin[\ell_n,h_n].
 \end{aligned}}
\tag{7}
\]

`a<0` 只把所有符号同时翻转，不影响“同号”的等价式。若 `p∈(ℓ_n,h_n)`，取达到最小值和最大值的样本即可得到严格异号。若 `p` 等于某个端点，至少一个样本为零、至少一个样本非零，其余全部弱同号；非退化 (3) 排除五项全零。

“弱同号等价于避开闭窗”不仅存在形式漏洞，而且在实际输出格上有端点反例。因为 `ℓ_n` 是有理数，写成既约 `P/Q`（`Q>0`），取 primitive 整数输出 `(-P,Q)`，则其斜率恰为 `ℓ_n`，五项弱同号且至少一项严格正，故满足五点符号条件，却没有避开闭窗。此反例没有断言该输出是第一极小向量，也没有给它所需的短度。

因此，无穷第一输出目标 T5 的正确重述是：存在无穷多个偶数 `n`，可在该 `n` 的第一极小输出中选择一个 `(b_n,a_n)`，使 `a_n=0`，或使 `-b_n/a_n∉(ℓ_n,h_n)`。第一输出可有多个，量词是“存在一个”，不要求任意选择都满足。上述所有等价式在同一个统一 `N` 之后适用于全部输出。

最后，若反设 `ζ(9)=c/d`，则零关系方向 `(-c,d)` 的斜率由 (3) 必须严格位于开窗 `(ℓ_n,h_n)`，其五点值必同时有正值和负值。这是有理性假设下的必要条件，与目前的谱宽上界相容；本文没有排除该情况，没有证明 T5 或根定理。
