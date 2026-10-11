# 折扣后中间素数预算：带符号归约与周期积分的严格收紧

本文沿用 [精确折扣恒等式](prime-discount-identity.md)、[合并极点局部界](intermediate-prime-attack.md)及[预算求和](vc-budget-sum-next.md)的记号。只得到一个严格但很小的统一改进：

\[
\boxed{\displaystyle
 \limsup_{\substack{n\to\infty\\2\mid n}}
 \frac{\mathcal E_n^{\rm mid}-\mathcal U_n}{n}
 \le C < \frac{22337}{1000}=22.337.}
\tag{1}
\]

这比已证的 `<22.4` 严格更强，仍远高于所需的 `0.61071437`。改进仅来自对**现有局部包络**的积分尾段做精确周期估计，没有证明折扣的正渐近下界。

## 1. 折扣后的精确带符号形式

令 `Y_n=√(7n/2)`，对 `Y_n<p≤n` 记 `v=v_p(N_n)`。这里 `a_p=1`，故逐素数有

\[
 (v-11)_+-\min\{(11-v)_+,9\}=\max\{v,2\}-11.
\tag{2}
\]

小素数折扣 `\mathcal U_n^{\rm small}` 至多

\[
 9\sum_{p\le Y_n}a_p\log p
 \le 9\pi(Y_n)\log n
 \le 9Y_n\log n=o(n).
\tag{3}
\]

因此 `(\mathcal E_n^{\rm mid}-\mathcal U_n)/n` 与
`n^{-1}\sum_{Y_n<p\le n}(\max\{v_p(N_n),2\}-11)\log p`
相差 `o(1)`。式 (2) 是研究折扣时应控制的带符号和；现有非负包络 `f(y)≥14` 仍允许 `v_p(N_n)>11`，所以单靠这条局部**上界**无法推出正折扣。舍去 `\mathcal U_n≥0` 后，已有求和证明仍给出式 (1) 的第一个不等号，其中

\[
 C=\int_1^\infty \frac{f(y)}{y^2}\,dy,\quad
 f(y)=19+\left\lfloor\frac{3y}{2}\right\rfloor
       +\left\lfloor\frac{7y}{2}\right\rfloor
       -10\left\lfloor\frac y2\right\rfloor
       -5\mathbf1_{\{y\}\ge2/3}.
\tag{4}
\]

## 2. 周期尾段的严格界

`f` 以 `2` 为周期。在一个周期 `[0,2]` 上，它的常值段与数值依次是

| 区间 | `[0,2/7)` | `[2/7,4/7)` | `[4/7,2/3)` | `[2/3,6/7)` | `[6/7,1)` | `[1,8/7)` | `[8/7,4/3)` | `[4/3,10/7)` | `[10/7,5/3)` | `[5/3,12/7)` | `[12/7,2)` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `f` | 19 | 20 | 21 | 17 | 18 | 23 | 24 | 25 | 26 | 21 | 22 |

直接积分得周期平均 `\mu=\frac12\int_0^2f(y)dy=64/3`。置

\[
 F(t)=\int_0^t(f(y)-\mu)\,dy\quad(0\le t\le2),
\]

则逐个端点计算给出 `-50/21≤F(t)≤0`；区间内 `F` 线性，故端点检查足够。`F(0)=F(2)=0`，可作 `2` 周期延拓。对任意正偶整数 `M`，分部积分于是给出

\[
 \int_M^\infty\frac{f(y)}{y^2}\,dy
 =\frac{\mu}{M}+2\int_M^\infty\frac{F(y)}{y^3}\,dy,
\quad
 \frac{\mu}{M}-\frac{50}{21M^2}
 \le \int_M^\infty\frac{f(y)}{y^2}\,dy
 \le\frac{\mu}{M}.
\tag{5}
\]

取 `M=100`，将 `[1,100]` 的每个跳点精确切开，记其有理数积分为 `S`。下列标准库程序同时核对周期原函数界和最终的**严格有理数**比较：

```python
from fractions import Fraction as Q

cuts = {Q(0), Q(1), Q(2), Q(2, 3), Q(5, 3)}
for d in (3, 7):
    cuts.update(Q(2*j, d) for j in range(d+1)
                if 0 < Q(2*j, d) < 2)
cuts = sorted(cuts)
F = Q(0)
for a, b in zip(cuts, cuts[1:]):
    y = (a+b)/2
    f = 19 + (3*y)//2 + (7*y)//2 - 10*(y//2) \
        - 5*int(y-y//1 >= Q(2, 3))
    F += (b-a)*(f-Q(64, 3))
    assert -Q(50, 21) <= F <= 0
assert F == 0

S = Q(0)
for k in range(1, 100):
    cuts = {Q(k), Q(k+1), Q(k)+Q(2, 3)}
    for d in (3, 7):
        cuts.update(Q(2*j, d)
                    for j in range(d*k//2, d*(k+1)//2+2)
                    if k < Q(2*j, d) < k+1)
    cuts = sorted(cuts)
    for a, b in zip(cuts, cuts[1:]):
        y = (a+b)/2
        f = 19 + (3*y)//2 + (7*y)//2 - 10*(y//2) \
            - 5*int(y-y//1 >= Q(2, 3))
        S += f*(1/a-1/b)

assert Q(22336, 1000) < S + Q(16, 75) - Q(50, 210000)
assert S + Q(16, 75) < Q(22337, 1000)
print('22.336 < C < 22.337')
```

这里 `16/75=(64/3)/100`。下界仅说明**当前包络积分**约为 `22.336…`，不是实际折扣后预算的下界。要逼近目标阈值，必须得到原 Smith 子式的额外消去、异常素数的加权稀疏性，或 `\mathcal U_n` 的正线性下界；式 (2) 和现有上界没有提供这些结论。有限 `N_n` 数据未被用于证明。
