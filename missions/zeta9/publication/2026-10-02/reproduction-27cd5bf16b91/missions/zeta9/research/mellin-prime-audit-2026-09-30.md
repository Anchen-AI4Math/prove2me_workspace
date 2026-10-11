# Mellin Gram 分母的局部素数审计（2026-09-30）

## 问题与约定

以下局部推导对任意连续指数集 $E_D=\{0,1,\ldots,D\}$ 与素数 $D<p\le2D$ 成立；精确数值审计只计算到 $D\le12$。令

\[
H_n=\sum_{j=1}^n j^{-9},\qquad
C_D=(H_i+H_j-H_{i+j})_{1\le i,j\le D},\qquad
b_D=(-H_i)_{1\le i\le D}.
\]

由 Mellin Gram 的 Schur 公式，(q_D=b_D^tC_D^{-1}b_D=Q_D/P_D)（既约，(P_D>0)）。本记录检查区间 (D<p\le2D) 内的素数是否整除 (P_D)，并分析 (p^9C_D\pmod p) 的结构。计算完全使用有理数；脚本见 [`probe_mellin_primes.py`](../scripts/probe_mellin_primes.py)。

## 反对角阶梯与精确下降

取素数 (D<p\le2D)，令
\[
k=p-D-1,\qquad r=D-k=2D-p+1.
\]
按指标 (1,\ldots,k\) 与 (k+1,\ldots,D) 分块写 (C_D=\begin{pmatrix}A&B\\B^t&T\end{pmatrix})，并相同分块 (b_D=(b_L,b_H)^t)。由于 (i,j<p)，和式中分母含 (p) 的唯一项是 (i+j\ge p) 时 (H_{i+j}) 里的 (p^{-9})。所以
\[
p^9(C_D)_{ij}\equiv-\mathbf 1_{i+j\ge p}\pmod p.
\]
这给出阈值反对角阶梯矩阵 (U)。它有 (k) 个零行；余下 (r) 行线性无关，故秩恰为 (r=2D-p+1)。右下 (r\times r) 块的指标从 $p-D=k+1$ 到 $D$。把行列指标分别写成 $i=p-D+a$、$j=p-D+b$，其中 $a,b=0,\ldots,r-1$，则非零区域恰由 $a+b\ge r-1$ 给出；反序列后为三角矩阵，对角元全为 $-1$。因此该块的行列式是单位，
\[
T=p^{-9}U_H+V,\qquad v_p(\det T)=-9r,
\]
其中 (V) 的元素均在 (\mathbb Z_p)，且 (T^{-1}\in p^9M_r(\mathbb Z_p))。交叉块 (B) 和向量 (b_H) 都是 (p)-整的，因为低指标 (i\le k) 与高指标 (j\le D) 满足 (i+j\le p-1)。

若低块 (A=C_k) 的行列式不是 (p) 的倍数，Schur 补
\[
S=A-BT^{-1}B^t
\]
满足 (S\equiv A\pmod {p^9})，故 (S^{-1}\) 也是 (p)-整的。分块逆公式给出
\[
q_D=(b_L-BT^{-1}b_H)^tS^{-1}(b_L-BT^{-1}b_H)
      +b_H^tT^{-1}b_H
\equiv b_L^tA^{-1}b_L=q_k\pmod {p^9\mathbb Z_p}.
\]
这里 (k=0) 时约定 (q_0=0)、空矩阵行列式为 1。于是得到一个严格的充分条件：

> **局部下降准则。** 若 (D<p\le2D) 且 (p\nmid\det C_{p-D-1})，则 (p\nmid P_D)，并且 (v_p(\det C_D)=-9(2D-p+1))。

这个结论只在低块非奇异的前提下成立；下面给出覆盖部分奇异低块的更强赋值估计。

## 低块奇异时的赋值递归

令 $a=v_p(\det A)\ge0$，暂设 $k>0$。$A,S,b_L,b'=b_L-BT^{-1}b_H$ 都是 $p$-整矩阵或向量，并且 $S-A,b'-b_L\in p^9\mathbb Z_p$。行列式、伴随矩阵都是整数系数多项式，故令
\[
d=\det A,\quad d'=\det S,\quad N=b_L^t\operatorname{adj}(A)b_L,\quad
N'=b'^t\operatorname{adj}(S)b'
\]
便有 $d'-d,N'-N\in p^9\mathbb Z_p$。尾块项 $h=b_H^tT^{-1}b_H\in p^9\mathbb Z_p$，所以全量 Schur 分子 $M=N'+h d'$ 仍满足 $M-N\in p^9\mathbb Z_p$。若 $a<9$，则 $v_p(d')=v_p(d)=a$。写 $e_k=v_p(P_k)=\max(0,a-v_p(N))\le a$，其中 $q_k=N/d$。

若 $v_p(N)<a$，因 $N'-N\in p^9$ 且 $a<9$，有 $v_p(M)=v_p(N)$，故 $q_D=M/d'$ 与 $q_k=N/d$ 有相同的负赋值；若 $v_p(N)\ge a$，则 $v_p(M)\ge a$，两者都 $p$-整。因此对全部 $a<9$，
\[
\boxed{v_p(P_D)=v_p(P_k).}
\]
相同分子、分母估计还给出数值误差的精确下界：
\[
M d-N d'=(M-N)d+N(d-d')\in p^{9+a}\mathbb Z_p+p^{9+v_p(N)}\mathbb Z_p,
\]
从而
\[
\boxed{v_p(q_D-q_k)\ge9-a-e_k.}
\]
由 $e_k\le a$ 可恢复粗界 $q_D-q_k\in p^{9-2a}\mathbb Z_p$。当 $k=0$ 时 $q_k=0$，且 $q_D=b_H^tT^{-1}b_H\in p^9\mathbb Z_p$，故分母递归同样成立，误差阶至少为 9。

分母赋值递归覆盖全部 $a=0,\ldots,8$；当 $a=5,\ldots,8$ 时，误差下界 $9-a-e_k$ 可能为负数，不能据此声称 $q_D-q_k$ 是 $p$-整或有正阶同余。若 $a\ge9$，行列式稳定和分母递归的论证不再适用。当前 $D\le12$ 数值样本没有 $a\ge5$ 的行。

六个低块奇异行的精确递归数据如下。所有行 $v_p(q_k)=-1$、$e_k=1$，且分母赋值保持为 1：

| $D$ | $p$ | $k$ | $a=v_p(\det C_k)$ | $v_p(q_D-q_k)$（下界 $9-a-e_k$） | $v_p(P_k)=v_p(P_D)$ |
|---:|---:|---:|---:|---:|---:|
| 5 | 7 | 1 | 1 | 8（下界 7） | 1 |
| 6 | 11 | 4 | 3 | 9（下界 5） | 1 |
| 7 | 11 | 3 | 2 | 9（下界 6） | 1 |
| 7 | 13 | 5 | 2 | 9（下界 6） | 1 |
| 8 | 11 | 2 | 1 | 9（下界 7） | 1 |
| 8 | 13 | 4 | 1 | 10（下界 7） | 1 |

## 精确有限检查

每个表项按 `p:k, det(C_k) mod p, rank(p^9 C_D mod p), v_p(P_D), q_D-q_k∈p^9 Z_p` 排列。`yes` 项同时由脚本直接用既约有理数核验；低块奇异处标成 `n/a`。

| (D) | (D<p\le2D) 的全部素数检查 |
|---:|---|
| 1 | `2:0, 1, 1, 0, yes` |
| 2 | `3:0, 1, 2, 0, yes` |
| 3 | `5:1, 3, 2, 0, yes` |
| 4 | `5:0, 1, 4, 0, yes`; `7:2, 3, 2, 0, yes` |
| 5 | `7:1, 0, 4, 1, n/a` |
| 6 | `7:0, 1, 6, 0, yes`; `11:4, 0, 2, 1, n/a` |
| 7 | `11:3, 0, 4, 1, n/a`; `13:5, 0, 2, 1, n/a` |
| 8 | `11:2, 0, 6, 1, n/a`; `13:4, 0, 4, 1, n/a` |
| 9 | `11:1, 10, 8, 0, yes`; `13:3, 8, 6, 0, yes`; `17:7, 15, 2, 0, yes` |
| 10 | `11:0, 1, 10, 0, yes`; `13:2, 2, 8, 0, yes`; `17:6, 15, 4, 0, yes`; `19:8, 10, 2, 0, yes` |
| 11 | `13:1, 6, 10, 0, yes`; `17:5, 4, 6, 0, yes`; `19:7, 5, 4, 0, yes` |
| 12 | `13:0, 1, 12, 0, yes`; `17:4, 2, 8, 0, yes`; `19:6, 7, 6, 0, yes`; `23:10, 6, 2, 0, yes` |

所有模 $p$ 阶梯矩阵的秩都等于 $2D-p+1$。对全部 $a<9$，分母赋值由 $q_k$ 严格递归；六个奇异低块行均由此解释，且其低维分母均含一次 $p$。本有限计算范围内没有未解释的分母素因子。尚未覆盖的是 $a\ge9$ 的分母递归，以及任何随 $D\to\infty$ 的结论。

## 复现与结论边界

在 zeta9 目录运行：

```powershell
C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe scripts/probe_mellin_primes.py
```

脚本以整数分母清除后的精确行列式求 $q_D$，验证阶梯矩阵逐项同余、秩公式、既约分母的 $p$-进赋值；逐行计算 $a=v_p(\det C_k)$ 与 $v_p(q_D-q_k)$，检查 $a<9$ 时的两条误差界及分母递归；在低块非奇异样本还验证 $q_D-q_k\in p^9\mathbb Z_p$ 和 $v_p(\det C_D)=-9r$。运行输出末行为 `PASS`，精确 $P,Q$ 与局部数据保存在 [`certificate.json`](../verification/mellin-prime-audit-2026-09-30/certificate.json)。没有扫描 $D>12$，也没有从有限表格声称渐近规律或关于全部素数的分母定理。

