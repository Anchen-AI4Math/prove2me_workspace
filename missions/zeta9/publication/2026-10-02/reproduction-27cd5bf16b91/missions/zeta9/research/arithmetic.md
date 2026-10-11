# ζ(9) 首轮：单值线性形式与有限算术证书

本笔记独立证明本轮短零区构造的代数恒等式、有限整化与公因子渐近。
它不预设 ζ(9) 无理；任何有限数值检查都不代替无穷序列的衰减和非零性证明。
实现位于 `scripts/linear_arithmetic_certificate.py`，与精确系数计算脚本分开。

## 1. 构造与确切的 ζ 支持

所有 Pochhammer 符号采用 rising 约定 \((t)_m=t(t+1)\cdots(t+m-1)\)。
取偶数 \(n\ge2\)、整数 \(m\ge1\)，满足 \(14m\le3n+1\)。定义

\[
 R_{n,m}(t)=\frac{n!^3}{m!^{14}}
 \frac{[(t-m)_m(t+n+1)_m]^7}{(t)_{n+1}^3},\qquad
 L_{n,m}=\frac1{6!}\sum_{k=1}^{\infty}R_{n,m}^{(6)}(k).
\]

分子、分母次数差为 \(14m-3n-3\le-2\)，故 \(R=O(t^{-2})\)，导数级数绝对收敛。
实际上 \(n\) 为偶数使这个次数差为奇数，因此至多 −3。
\(t=1,\ldots,m\) 均为七重零点，前 \(m\) 个六阶导数项严格为零。
只有 \(t=0,-1,\ldots,-n\) 的三阶极点。

写出唯一部分分式

\[
 R(t)=\sum_{j=0}^{n}
 \left(\frac{C_j}{(t+j)^3}+\frac{D_j}{(t+j)^2}+\frac{E_j}{t+j}\right).
\]

在 \(t=-j\) 消去三阶极点并求对数导数，得到

\[
 C_j=(-1)^{m+j}\binom nj^3\binom{j+m}{m}^7\binom{n-j+m}{m}^7\in\mathbb Z,
\]
\[
 D_j=C_ju_j,\qquad E_j=\frac{C_j}{2}(u_j^2+v_j),
\]
\[
 u_j=10H_j-10H_{n-j}-7H_{j+m}+7H_{n-j+m},
\]
\[
 v_j=10H_j^{(2)}+10H_{n-j}^{(2)}-7H_{j+m}^{(2)}-7H_{n-j+m}^{(2)}.
\]

这里 \(H_0^{(r)}=0\)。第一公式的符号来自分子 \((-1)^{7m}\) 与分母
\((-1)^{3j}\)；其余阶乘合并恰好给出三个二项式。

由于 \(R(t)=O(t^{-2})\)，无穷远展开的 \(t^{-1}\) 系数为零，即
\(\sum E_j=0\)。反射 \(R(-n-t)=-R(t)\) 给出
\(D_{n-j}=-D_j\)，所以 \(\sum D_j=0\)。对有限部分分式六次求导后逐项求和，
三种系数依次为 \(\binom66=1\)、\(\binom76=7\)、\(\binom86=28\)，因此

\[
 \boxed{L_{n,m}=A_{n,m}\zeta(9)+B_{n,m}},\qquad
 A_{n,m}=28\sum_{j=0}^{n}C_j,
\]
\[
 B_{n,m}=-\sum_{j=0}^{n}
 \left(E_jH_j^{(7)}+7D_jH_j^{(8)}+28C_jH_j^{(9)}\right)\in\mathbb Q.
\]

这里消去的是 ζ(7)、ζ(8)，没有以数值接近零替代系数恒等式。
上述结论也不自动保证 \(A\ne0\) 或 \(L\ne0\)；这两项必须另行核验。

**2026-09-28 补充：** [全参数非零性证明](short-zero-coefficient-nonvanishing.md)
现已证明 `sgn(A)=(-1)^(m+n/2)` 并给出显式下界，关闭这里的 `A≠0` 缺口。
`L≠0` 仍开放；本补充是书面证明，尚未 Lean 形式化。

## 2. 覆盖整个系数向量的有限乘子

令
\[
 d=\operatorname{lcm}(1,\ldots,n+m),\qquad G=\gcd(|C_0|,\ldots,|C_n|)>0.
\]

分母上限是 **n+m**，不能未经证明换成 n。因为
\(du_j\in\mathbb Z\)、\(d^2v_j\in\mathbb Z\)，故

\[
 C_j/G\in\mathbb Z,\quad dD_j/G\in\mathbb Z,\quad 2d^2E_j/G\in\mathbb Z.
\]

又 \(d^rH_j^{(r)}\in\mathbb Z\) 对 \(j\le n\) 成立，于是

\[
 \boxed{t_{n,m}:=2d^9/G,\qquad
 t_{n,m}A_{n,m}\in\mathbb Z,\quad t_{n,m}B_{n,m}\in\mathbb Z.}
\]

所有小素数已经包括在这个初等证明中。\(t\) 可以是有理数；允许负素数指数正是
除去公因子的作用，不能把这些指数截成非负数。

### 2.1 更强的有限乘子：\(d_n^9/G\)

上述初等乘子还不是本族可直接证明的最好版本。记
\(d_n=\operatorname{lcm}(1,\ldots,n)\)。本参数域满足 \(m\le3n/14<n/4\)，可以证明

\[
 \boxed{t^\sharp_{n,m}=d_n^9/G,\qquad
 t^\sharp_{n,m}(A_{n,m},B_{n,m})\in\mathbb Z^2.}
\]

证明分两步，均对所有素数适用。

**去掉因子 2。** 令 \(z=t+j\)，在极点附近有正式幂级数恒等式
\[
 (t+j)^3R(t)=C_j\prod_{a\in\mathcal A_j}(1+z/a)^{e_a},
 \qquad e_a\in\{7,-3\},\quad a\in\mathbb Z\setminus\{0\},\quad |a|\le n+m.
\]
其中两个分子块给出指数 7，其余分母因子给出指数 −3；若某个 a 重复，可保留为多重集合。
各一次系数为 \(e_a/a\)，其中 \(e_a\) 是整数；二次系数由
\(\binom{e_a}{2}/a^2\) 和 \(e_ae_b/(ab)\) 相加。
\(\binom e2\) 对负整数 e 同样是整数。因此
\(dD_j/G\)、\(d^2E_j/G\) 已经是整数，粗估中的因子 2 不必保留。

**把 d 的上限降到 n。** 固定素数 p。若
\(\lfloor\log_p(n+m)\rfloor=\lfloor\log_pn\rfloor\)，已证结论直接适用。
否则令 \(P=p^a\in(n,n+m]\)。因 \(n+m<2n\)，这样的 prime-power level 至多一个，
且 \(a-1=\lfloor\log_pn\rfloor\)。

考察整数指标区间
\[
 J=[n+m-P+1,\ P-m-1]\cap\mathbb Z.
\]
它在 \([0,n]\) 内，其中每个 \(j'\) 满足 \(j'+m<P\)、\(n-j'+m<P\)。
其整数个数为 \(2P-n-2m-1\)。由于 \(P\ge n+1\) 且 \(m\le3n/14\)，
\[
 |J|-P/2=3P/2-n-2m-1\ge n/2-2m+1/2>0.
\]
故 J 包含每个模 \(P/p=p^{a-1}\) 的剩余类。

如果原指标 j 的两个分子块均不含 \(\pm P\)，那么其全部 a 因子的 p-adic 阶
至多 a−1，故 Taylor 系数的分母由 \(d_n\)、\(d_n^2\) 控制。
否则取 \(j'\in J\) 且 \(j'\equiv j\pmod{p^{a-1}}\)。第 4 节 floor 表达在低于 a 的
所有层只依赖 j 的相应剩余类，因此这些层在 j、j′ 相同。
第 a 层的 \(\binom nj\) carry 为零，两个分子块至多一个产生 carry，因为
\(n+2m<2P\)；此时其贡献恰为 7，而 j′ 的最高层为零。更高层全零。
所以
\[
 v_p(C_j)-v_p(C_{j'})=7,\qquad v_p(C_j/G)\ge7.
\]
一次、二次 Taylor 系数即使分别损失 a、2a 阶，也仍满足
\[
 v_p(D_j/G)\ge7-a\ge-(a-1),\quad
 v_p(E_j/G)\ge7-2a\ge-2(a-1).
\]
这包含 p=2，且已经避免二次导数公式的表面因子 2。
对所有 p 得到 \(d_nD_j/G,d_n^2E_j/G\in\mathbb Z\)。又所有调和指标 j≤n，
最终 \(d_n^9B/G\)、\(d_n^9A/G\) 均为整数。证毕。

两套有限证书严格满足
\[
 t/t^\sharp=2(d/d_n)^9\in\mathbb Z_{>0}.
\]
新证书不能改变已经求出的 primitive 多项式，只能缩小已证明估计相对于 primitive 的 gap。

## 3. Primitive 整化为何最优、gap 如何定义

设非零有理多项式 \(F(X)=AX+B\)。令 \(D\) 为两个系数分母的最小公倍数，
\(g=\gcd(|DA|,|DB|)\)，并定义

\[
 m_{\rm prim}=D/g>0,\qquad P=m_{\rm prim}F\in\mathbb Z[X].
\]

\(P\) 的系数最大公因子为 1。若正有理数 \(t\) 满足 \(tF\in\mathbb Z[X]\)，
则 \((t/m_{\rm prim})P\) 整系数；取 primitive 系数的 Bezout 整数线性组合可知
\(t/m_{\rm prim}\in\mathbb Z_{>0}\)。反过来也成立。因此 primitive scale 是
全系数整数化所能采用的最小正倍数；任何另一个有效倍数都不能产生更小的
\(|P(\zeta(9))|\)。这只比较同一个 F，不排除改变构造。

本轮有确切可验证的有限 gap

\[
 g_{n,m}=\frac1n\log\frac{t_{n,m}}{m_{\rm prim}}\ge0.
\]

整除用 Fraction 验证，不能用浮点接近整数判定。自然尺度是 n，已经不是旧 Hankel
构造的 \(K^2\)。若 \(A=B=0\)，应记作恒零退化案例，不定义 primitive scale。

## 4. 全部素数的精确阶乘公式

记 \(v_p\) 为 p-adic 估值。对所有素数、所有允许 j，

\[
 v_p(C_j)=3v_p(n!)+7v_p((j+m)!)+7v_p((n-j+m)!)
 -10v_p(j!)-10v_p((n-j)!)-14v_p(m!).
\]

特别地
\[
 \nu_p:=v_p(G)=\min_{0\le j\le n}v_p(C_j),\qquad
 v_p(t)=\mathbf1_{p=2}+9\lfloor\log_p(n+m)\rfloor-\nu_p.
\]

Legendre 公式将每个 \(v_p(C_j)\) 写成
\(\sum_{k\ge1}\phi(n/p^k,m/p^k,j/p^k)\)，其中

\[
 \phi(x,a,z)=3\lfloor x\rfloor+7\lfloor z+a\rfloor+7\lfloor x-z+a\rfloor
 -10\lfloor z\rfloor-10\lfloor x-z\rfloor-14\lfloor a\rfloor.
\]

这里不能一般性地把 \(\min_j\sum_k\) 换成 \(\sum_k\min_j\)。脚本对小素数保持
前一种正确次序，且独立使用整数 C 的 gcd 核验。
所有分母素数都不超过 n+m；\(G\mid C_0=\pm\binom{n+m}{m}^7\)，其素因子也不超过此界。

## 5. 大素数公因子的完全显式公式

以下引理只需 \(n\ge2m\)，故覆盖本轮所有参数，包括端点。

**引理。** 若 \(p^2>n+m\)，令 \(r=n\bmod p\)、\(s=m\bmod p\)，则

\[
 \boxed{v_p(G)=7\mathbf1_{r+2s\ge2p-1}.}
\]

证明：当 \(p\le n\)，全部剩余类 \(u=j\bmod p\) 都由某个 \(0\le j\le n\)
实现；由于 \(p^2>n+m\)，只剩第一层 factorial floor。三个二项式的 carry 公式给出

\[
 v_p(C_j)=3\mathbf1_{u>r}+7\mathbf1_{u+s\ge p}
 +7\mathbf1_{((r-u)\bmod p)+s\ge p}.
\]

若 \(u\le r\)，取得零估值恰好要求某个整数 u 满足
\[
 \max(0,r+s-p+1)\le u\le\min(r,p-s-1).
\]
此区间非空当且仅当 \(r+2s\le2p-2\)。若此条件失败，取 \(u=0\) 恰好得到 7。
而 \(u>r\) 若要得到比 7 小的值，只能让后两个 carry 同时为零；这要求
\(r+s+1\le u\le p-s-1\)，即 \(r+2s\le p-2\)，与失败条件矛盾。
故失败时的最小值恰为 7。

当 \(p>n\)，取 \(j=\lfloor n/2\rfloor\)；\(n\ge2m\) 保证三个二项式均无 carry，
故 \(v_p(G)=0\)。同时 \(r=n,s=m\)，且 \(n+2m<2p-1\)，右侧也为零。证毕。

## 6. 统一公因子渐近与全部小素数

固定有理 \(0<\alpha\le3/14\)，沿偶数 \(n\) 且 \(m=\alpha n\in\mathbb Z\) 的序列。
小素数满足

\[
 0\le\nu_p\le v_p(C_0)\le7\lfloor\log_p(n+m)\rfloor,
\]
\[
 \sum_{p\le\sqrt{n+m}}\nu_p\log p=O(\sqrt n\log n)=o(n).
\]

大素数精确阈值与连续 floor 条件只有一个可能差别：
\(r+2s=2p-1\)。这时 \(p\mid n+2m+1\)，所以所有边界差别的总贡献不超过
\(7\log(n+2m+1)=o(n)\)。因此

\[
 \log G=7\sum_{p\le n}
 \mathbf1_{\{n/p\}+2\{m/p\}\ge2}\log p+o(n).
\]

对 \(p/n\ge\epsilon>0\)，被积函数只有有限个断点，可以直接用素数定理。
\(p\le\epsilon n\) 部分至多 \(7\vartheta(\epsilon n)\)，归一化后再令
\(\epsilon\downarrow0\)。得到完整极限

\[
 \boxed{\lim\frac{\log G}{n}=\Gamma(\alpha)
 =7\int_1^\infty\frac{\mathbf1_{\{x\}+2\{\alpha x\}\ge2}}{x^2}\,dx.}
\]

准确恒等式为 \(\log d=\psi(n+m)=\sum_{p^k\le n+m}\log p\)，不是只求和一次素数的
\(\vartheta(n+m)\)。由 \(\psi(x)\sim x\)，于是给出

\[
 \boxed{\lim\frac{\log t_{n,m}}n=9(1+\alpha)-\Gamma(\alpha).}
\]

第 2.1 节更强证书则满足
\[
 \boxed{\lim\frac{\log t^\sharp_{n,m}}n=9-\Gamma(\alpha).}
\]

这些是对实际 G、实际有限乘子的极限，不是未经证实的最佳 primitive scale 渐近。
还可立即得到 \(0\le\Gamma(\alpha)\le14\alpha\)：当 \(x<1/(2\alpha)\) 时指示函数为零。
所以原始乘子的渐近成本至少 \(9-5\alpha\ge111/14\)，更强乘子的渐近成本至少
\(9-14\alpha\ge6\)。这都是算术成本的下界，不是实际线性形式大小的下界。

端点 \(\alpha=3/14\) 在本节完全合法：\(R\) 的次数差恰为 −3，整数化证明仍有
\(m<n/4\) 的严格余量，公因子极限只用固定有理比例和有限 floor 断点。
这不授权在解析侧照搬内部参数的鞍点或无穷远尾部估计，后者仍须独立处理。

对 \(\alpha=a/b\)（既约），指示函数以 b 为周期。每个由整数 x 与整数
\(\alpha x\) 划分的区间中，条件简化为
\((1+2\alpha)x\ge\lfloor x\rfloor+2\lfloor\alpha x\rfloor+2\)。
因此一个周期的支持是显式有理端点区间的有限并。脚本累加 R 个周期的
\(1/l-1/r\)，每个倒数在整数格 \(10^{-32}\mathbb Z\) 上向外取整。
若一周期支持长度为 \(\ell\)、周期为 b，则未乘 7 的尾部有严格界

\[
 \frac{\ell}{b^2(R+1)}\le
 \int_{Rb}^{\infty}\frac{\mathbf1_{\{x\}+2\{\alpha x\}\ge2}}{x^2}\,dx
 \le\frac{\ell}{b^2}\left(\frac1R+\frac1{R^2}\right).
\]

这提供不依赖浮点特殊函数的可核验有理区间。

## 7. 当前证明边界

本族在中心变量下属于 Zudilin 导数线性形式的技术谱系，对应 a=3、b=7、
c=1+2α。原文的 c≥3 奇整数参数域不覆盖这里，故没有沿用其 Π 公因子或鞍点定理。
[原始来源：Zudilin 2001，§3–4](https://arxiv.org/pdf/math/0104249)。

本笔记已独立闭合代数和算术部分。其整性以及 G 的渐近公式并不证明 \(L\ne0\)，
也不证明整化后衰减。若精确 primitive 值未显示衰减，不能用有限样本否定整个族。
若要严格排除当前 t 所生成的序列，需要额外证明实际 \(L\) 的渐近下界或非零主项，
不能把 \(\sum|R^{(6)}(k)|\) 的增长误当成 \(|L|\) 的下界。

## 8. 本轮有限比较与严格区间结果

原乘子结果保存在 `verification/arithmetic-certificates.json`；更强乘子以及只读导入的
独立精确系数比较另存为 `verification/arithmetic-improved-certificates.json`，没有覆写
精确计算代理的系数文件。命令为

```
python missions/zeta9/scripts/linear_arithmetic_certificate.py --improved --compare-exact missions/zeta9/verification/linear-results.jsonl --output missions/zeta9/verification/arithmetic-improved-certificates.json
```

全部 18 个主网格案例，以及三个 m=0 控制案例，均严格通过以下 Fraction 检查：
\(t^\sharp A,t^\sharp B\in\mathbb Z\)，\(t^\sharp/m_{\rm prim}\in\mathbb Z_{>0}\)，
且复算的 C-gcd、A 与独立 exact 文件一致。m=0 控制有 G=1，基本 Taylor 证明仍适用。
这些检查是实现一致性证据，统一定理依赖前面的证明。

下表 Gamma 与成本使用有理区间的向外简写，不把打印的小数当成证明输入。

| α | Gamma(α) 的严格包围 | lim log(t-sharp)/n 的严格包围 |
|---:|---:|---:|
| 1/28 | [0.14171563, 0.14171565] | [8.85828435, 8.85828438] |
| 1/14 | [0.28254068, 0.28254070] | [8.71745930, 8.71745933] |
| 3/28 | [0.42662800, 0.42662801] | [8.57337199, 8.57337200] |
| 1/7 | [0.57820646, 0.57820651] | [8.42179349, 8.42179354] |
| 5/28 | [0.70905586, 0.70905588] | [8.29094412, 8.29094414] |
| 3/14 | [0.85210820, 0.85210822] | [8.14789178, 8.14789180] |

在 n=224 的六个主参数上，primitive gap 与数值率如下。后两列是浮点报告数，
其正负和 |P|>1 的判断由精确代理的 Arb 区间另行证明。

| α | log(t-sharp/m-prim)/n | log\|P(ζ9)\|/n | 推得 log\|L\|/n |
|---:|---:|---:|---:|
| 1/28 | 0.858914 | 8.273517 | 0.536460 |
| 1/14 | 0.714172 | 8.657046 | 1.019452 |
| 3/28 | 0.714292 | 9.101122 | 1.455122 |
| 1/7 | 0.669464 | 9.337972 | 1.862306 |
| 5/28 | 0.623150 | 9.507511 | 2.243896 |
| 3/14 | 0.736385 | 9.790245 | 2.616494 |

因此更强乘子确实削减了理论成本，但现有主网格的 primitive 值仍全部大于 1；
没有负余量候选，也没有由这些样本升级到 n=448。特别是本次改进不是新的实数逼近，
也不能通过再次乘一个有效整数化因子修复相同有限 primitive 多项式的大小。

独立审计记录：主代理和解析代理均检查了第 2.1 节的中央指标区间、p=2、a=1、
唯一最高 carry 与二阶 Taylor 整系数论证；精确计算代理另外核验全部 21 个案例的
最终系数整数化。讨论中纠正了 `log lcm = theta` 的文字误写，实际恒等式是 psi，
有限脚本始终使用全部 prime powers，已报告的极限与数值未因此改变。
