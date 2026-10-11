# VC：两个逐素数候选界的精确反例

本稿只使用主线 `p=9,m=n,deg W<=4` 的原始五维形式。以下用 `ell` 表示素数，以免与极点阶数 9 混淆。

**结论：** [中间素数稿](intermediate-prime-attack.md) §6 提出的两个充分条件，按其逐点表述都不成立：

| 偶数 `n` | 素数 `ell` | 范围 | 精确结果 |
|---|---|---|---|
| 234 | 29 | `29^2=841>819=7n/2`，`29<=n` | `v_29(N_234)=13>12` |
| 258 | 257 | `257>n/2=129`，`257<=n` | `v_257(N_258)=12>11` |

这些是由有限精确计算证明的反例。它们否定对应的全称局部命题，**不否定 VC 的渐近加权总和条件**，也不说明这样的异常有正密度。两例本身不能排除“忽略有限例外后成立”的版本。

## 1. 使用的恒等式与标度

令 `F=F_n`，行对应 `1,u,...,u^4`，列次序为 `(B,A_3,A_5,A_7,A_9)`，完全沿用[第五轮](../../round5/research/arithmetic.md)和[第七轮](../../round7/research/arithmetic.md)。对当前素数置

\[
                         G=\ell^9 F.
\]

因为 `ell^2>7n/2>2n`，`v_ell(d_n)=1`，且第五轮证明 `d_n^9 F` 为整数矩阵。因此 `G` 属于 `Mat_5(Z_(ell))`。它与第七轮的整数矩阵 `A=d_n^9F` 相差一个 `ell` 进单位标量，故所有同阶子式的最低估值相同。

记 `e_3` 为 `G` 三列 `(A_3,A_5,A_7)` 的十个三阶子式的最小估值；`e_4` 为包含这些列且另加 `B` 或 `A_9` 的十个四阶子式的最小估值。第七轮恒等式给出

\[
                  v_\ell(N_n)=v_\ell(\det G)+e_3-2e_4.       \tag{1}
\]

在两例中分别得到

\[
\begin{array}{c|rrrr}
(n,\ell)&v_\ell(\det G)&e_3&e_4&v_\ell(N_n)\\\hline
(234,29)&45&22&27&13\\
(258,257)&49&25&31&12
\end{array}                                                     \tag{2}
\]

也可不整化而使用 `F`：对应的 `(v(det F),e_3(F),e_4(F))` 为 `(0,-5,-9)` 与 `(4,-2,-5)`。式 (1) 中标度的贡献 `45+27-72` 恰为零。

## 2. 全部子式的局部证书

下表中的 `(e,a)` 表示子式 `D` 满足 `v_ell(D)=e` 且 `ell^(-e)D ≡ a (mod ell)`。所有 `a` 都非零。行编号从 0 到 4，与单项式次数一致。

三阶子式的列固定按 `(A_3,A_5,A_7)` 排列：

| 行集合 | `n=234,ell=29` | `n=258,ell=257` |
|---|---|---|
| 012 | (22,17) | (25,20) |
| 013 | (22,28) | (25,208) |
| 014 | (22,20) | (25,201) |
| 023 | (22,12) | (25,208) |
| 024 | (22,5) | (25,244) |
| 034 | (22,18) | (25,36) |
| 123 | (22,6) | (25,181) |
| 124 | (22,10) | (25,69) |
| 134 | (22,6) | (25,145) |
| 234 | (22,7) | (26,112) |

四阶子式的列按 `(A_3,A_5,A_7,C)` 排列；这里把额外列放在最后，明确固定符号：

| 行集合 | `C` | `n=234,ell=29` | `n=258,ell=257` |
|---|---|---|---|
| 0123 | B | (28,13) | (31,243) |
| 0123 | A9 | (37,6) | (40,228) |
| 0124 | B | (27,22) | (31,20) |
| 0124 | A9 | (36,28) | (40,225) |
| 0134 | B | (27,26) | (31,66) |
| 0134 | A9 | (36,12) | (40,100) |
| 0234 | B | (27,7) | (31,19) |
| 0234 | A9 | (36,1) | (40,21) |
| 1234 | B | (27,18) | (31,255) |
| 1234 | A9 | (36,15) | (40,106) |

完整行列式保持原列次序，其证书分别为 `(45,12)`、`(49,208)`。阶乘闭式独立给出相同估值：

\[
\begin{split}
D_{234,29}&=\lfloor351/29\rfloor+\lfloor819/29\rfloor
                 -10\lfloor117/29\rfloor=12+28-40=0,\\
D_{258,257}&=\lfloor387/257\rfloor+\lfloor903/257\rfloor
                 -10\lfloor129/257\rfloor=1+3=4.
\end{split}
\]

两例的素数均不整除 `7n`，故无需再减该分母估值。

## 3. 为什么模素数幂计算构成精确证书

固定极点 `-j`，设 `z=ell*x`，写

\[
 S_j(x)=(\ell x)^9 R_n(-j+\ell x),\qquad
 T_{j,r}(x)=S_j(x)\bigl(-j(n-j)+\ell(n-2j)x+\ell^2x^2\bigr)^r.
\]

精确乘积为

\[
 S_j(x)=C_j
 \prod_{a\in\{1,\ldots,n,-2n,\ldots,-n-1\}}
       \left(1+\frac{\ell x}{-j-a}\right)
 \prod_{\substack{0\le i\le n\\i\ne j}}
       \left(1+\frac{\ell x}{i-j}\right)^{-9},
\]

\[
 C_j=(-1)^j\binom nj^9\binom{n+j}{n}\binom{2n-j}{n}.
\]

全部非零距离绝对值不超过 `2n<ell^2`，因此 `ell/d` 属于 `Z_(ell)`。这些乘积可在 `Z/(ell^55)[x]/(x^9)` 中合法计算，负九次幂的系数为 `(-1)^h binom(8+h,h)`，不需要除以阶乘。令 `t_(j,r,h)=[x^h]T_(j,r)`，则

\[
 t_{j,r,9-s}=\ell^{9-s}c^{u^r}_{j,s},\qquad
 h_{j,s}=\sum_{k=1}^j(\ell/k)^s=\ell^s H_j^{(s)}.
\]

于是

\[
 G_{r,0}=-\sum_{j=0}^n\sum_{s=1}^9t_{j,r,9-s}h_{j,s},\qquad
 G_{r,k}=\ell^s\sum_{j=0}^nt_{j,r,9-s}
 \quad(s=3,5,7,9;\ k=1,2,3,4).                         \tag{3}
\]

故下面程序逐项返回真实 `G` 的模 `ell^55` 剩余，而不是一个近似矩阵。行列式是条目中的整系数多项式，得到的子式同余也精确。所有显示估值均小于 55；首个非零的 `ell` 进位因此确定真实有理数的精确估值，不受被截掉的更高位影响。

## 4. 自包含复核程序

Python 标准库即可；无需读取旧证书、安装依赖、计算 ζ 值或写文件。两例合计在本机约 6 秒。`certificate` 返回的三组数据就是以上表格。

```python
from math import comb
from itertools import combinations

def certificate(n, p):
    assert n % 2 == 0 and p*p > 7*n//2 and p <= n
    M = p**55

    def mul(a, b):
        c = [0]*9
        for i, x in enumerate(a):
            for j, y in enumerate(b[:9-i]):
                c[i+j] = (c[i+j] + x*y) % M
        return c

    def pd(d):
        assert d and abs(d) < p*p
        # Exact residue of p/d; the inverted denominator is a unit.
        return (pow(d//p, -1, M) if d % p == 0
                else p*pow(d, -1, M)) % M

    F = [[0]*5 for _ in range(5)]
    H = [0]*10
    for j in range(n+1):
        if j:
            v = pd(j)
            for s in range(1, 10):
                H[s] = (H[s] + pow(v, s, M)) % M
        S = [(-1)**j * comb(n,j)**9 * comb(n+j,n)
             * comb(2*n-j,n) % M] + [0]*8
        for root in list(range(1,n+1)) + list(range(-2*n,-n)):
            S = mul(S, [1, pd(-j-root)])
        for i in range(n+1):
            if i != j:
                v = pd(i-j)
                S = mul(S, [(-1)**h * comb(8+h,h) * pow(v,h,M) % M
                            for h in range(9)])
        W = [1] + [0]*8
        for r in range(5):
            T = mul(S,W)
            F[r][0] = (F[r][0] - sum(T[9-s]*H[s]
                                      for s in range(1,10))) % M
            for k,s in enumerate((3,5,7,9),1):
                F[r][k] = (F[r][k] + p**s*T[9-s]) % M
            W = mul(W, [-j*(n-j), p*(n-2*j), p*p])

    def det(A):
        if len(A) == 1:
            return A[0][0]
        return sum((-1)**j * A[0][j]
                   * det([r[:j]+r[j+1:] for r in A[1:]])
                   for j in range(len(A))) % M

    def witness(z):
        assert z, 'Increase the precision before drawing a conclusion'
        e = 0
        while z % p == 0:
            z //= p
            e += 1
        return (e, z % p)

    low = [witness(det([[F[i][j] for j in (1,2,3)] for i in I]))
           for I in combinations(range(5),3)]
    mixed = [witness(det([[F[i][j] for j in (1,2,3,c)] for i in I]))
             for I in combinations(range(5),4) for c in (0,4)]
    full = witness(det(F))
    return low, mixed, full

for n,p,expected in ((234,29,13), (258,257,12)):
    low,mixed,full = certificate(n,p)
    exponent = full[0] + min(e for e,a in low) - 2*min(e for e,a in mixed)
    assert exponent == expected
    print(n,p,low,mixed,full,exponent)
```

此外，另用冻结的 `round6/scripts/independent_audit.py` 中 `independent_columns` 从原乘积重建两个完整**有理数**矩阵，直接计算全部上述子式；结果与模素数幂程序完全一致。该路径没有使用 `n -> n+2` 连接。初始发现来自已证连接的精确连乘，最终反例不依赖该搜索路径。

有理矩阵按行依次取 25 个条目的规范约分字符串，每条之后一个换行，所得 SHA-256 为：

- `F_234`: `77302d49584d02a0792ba84ea26d995f8d8bf09f7473c0162fcc93c8a0ad90d5`
- `F_258`: `69d51ac099d7289328dafd5ace79e400cce42739f1a6ce6d55d52c4880f88847`

哈希仅标识本次独立重建结果；反例的可复核证书是式 (3) 和自包含程序。

## 5. 对后续 VC 工作的限制

统一上界 `11` / `12` 的直接路线须修改。可以研究比例区间上的更弱界、异常集合的加权总贡献，或允许显式例外的估值定理。当前两例没有给出异常集合的大小、无限性或密度，因此没有新的 VC 渐近结论。本稿未修改冻结轮次、平台或原始证书。
