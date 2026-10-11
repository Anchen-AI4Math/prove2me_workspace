# VC 中间素数预算的一个严格平均界

本稿把[合并极点局部界](intermediate-prime-attack.md)中的余数依赖保留到素数求和，而不是先统一替换为 `38`。得到对全部趋于无穷的偶数 `n` 成立的严格上界

\[
\boxed{\displaystyle\limsup_{2\mid n,\ n\to\infty}
       \frac{\mathcal E_n^{\rm mid}}n<\frac{112}{5}=22.4.} \tag{1}
\]

这比仅用 `v_p(N_n)\le38` 得到的 `27` 小，但仍远高于 VC 所需的 `0.61071436947`；**VC 保持开放**。证明没有把有限的 `N_n` 估值样本外推。

## 1. 局部界的周期包络

记 `Y_n=√(7n/2)`。对 `Y_n<p≤n`，写 `y=n/p`，`r=n-p⌊y⌋`，并定义

\[
D_0(y)=\left\lfloor\frac{3y}{2}\right\rfloor+
       \left\lfloor\frac{7y}{2}\right\rfloor-
       10\left\lfloor\frac y2\right\rfloor,
\qquad
g_0(y)={\bf1}_{\{y\}\ge2/3},
\qquad
f(y)=19+D_0(y)-5g_0(y).                                      \tag{2}
\]

命题 3 给出 `v_p(N_n)≤30+D_{n,p}−5g_{n,p}`，其中
`D_{n,p}=D_0(n/p)−v_p(7n)` 且
`g_{n,p}={\bf1}_{3r\ge2p-1}`。显然 `D_{n,p}≤D_0(y)`；若
`{y}=r/p≥2/3`，则 `3r≥2p>2p−1`，故 `g_{n,p}≥g_0(y)`。于是逐素数有

\[
 (v_p(N_n)-11)_+\le f(n/p).                                  \tag{3}
\]

式 (3) 右边确实非负：写 `y=2k+t`、`0≤t<2`，则
`D_0(y)=⌊3t/2⌋+⌊7t/2⌋∈[0,8]`，所以 `14≤f(y)≤27`。
此外 `D_0` 以 `2` 为周期，`g_0` 以 `1` 为周期，故 `f` 以 `2` 为周期。

## 2. 素数定理给出的平均常数

令 `θ(x)=Σ_{p≤x}log p`，并置

\[
 C=\int_1^\infty\frac{f(y)}{y^2}\,dy.                     \tag{4}
\]

积分收敛，因为 `14≤f≤27`。对任意固定整数 `M≥2`，区间
`n/M<p≤n` 上的 `f(n/p)` 只有有限个跳点。这些跳点来自
`y=2j/3`、`y=2j/7`、`y=k+2/3` 以及整数端点。素数定理
`θ(cx)/x→c` 对每个固定 `c>0` 成立，所以在每个定值小区间
`a<y<b` 中，带 `log p` 的素数和除以 `n` 趋于
`1/a−1/b=∫_a^b y^{-2}dy`。恰在跳点的素数至多有限个，贡献
`O_M(log n)/n→0`。因此

\[
 \frac1n\sum_{n/M<p\le n}f(n/p)\log p
 \longrightarrow \int_1^M\frac{f(y)}{y^2}\,dy.                  \tag{5}
\]

在剩余区间，非负性和 `f≤27` 给出
`Σ_{Y_n<p≤n/M} f(n/p)log p≤27 θ(n/M)`，其归一化上极限
至多 `27/M`。让固定的 `M→∞`，并用积分尾界
`∫_M^∞ f(y)y^{-2}dy≤27/M`，便得到包络素数和的极限为 `C`。
结合 (3)，

\[
 \limsup_{2\mid n,\ n\to\infty}
       \frac{\mathcal E_n^{\rm mid}}n\le C.                  \tag{6}
\]

## 3. 有理数证书：`C<22.4`

只须截到 `M=100`：尾积分至多 `27/100`。下列纯标准库
Python 使用 `Fraction` 对 `(1,100)` 的每个常值段做精确积分，
不读取任何有限 `N_n` 样本。`S<2213/100` 是有理数严格比较，
故 `C≤S+27/100<112/5`。

```python
from fractions import Fraction as Q

S = Q(0)
for k in range(1, 100):
    cuts = {Q(k), Q(k + 1), Q(k) + Q(2, 3)}
    for d in (3, 7):
        cuts.update(Q(2*j, d)
                    for j in range(d*k//2, d*(k+1)//2 + 2)
                    if k < Q(2*j, d) < k+1)
    cuts = sorted(cuts)
    for a, b in zip(cuts, cuts[1:]):
        y = (a + b) / 2
        D = (3*y)//2 + (7*y)//2 - 10*(y//2)
        g = int(y - (y//1) >= Q(2, 3))
        f = 19 + D - 5*g
        assert 14 <= f <= 27
        S += f * (1/a - 1/b)
assert S < Q(2213, 100)
print('exact rational inequality verified')
```

式 (1) 只是现有局部界的加权平均改进；它没有提供接近 VC
阈值所需的低 ζ 子式消去。特别地，`n=234,p=29` 的指数 `13`
以及 `n=258,p=257` 的指数 `12` 说明不能用早先猜想的
逐素数 `≤12`、`p>n/2` 时 `≤11` 来替换上述求和证明。
