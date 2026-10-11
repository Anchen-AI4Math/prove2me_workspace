# 2026-10-01 前沿推导独立复核记录

本记录由根代理维护，区分书面证明、有限精确检查和仍未解决的渐近问题。
本轮没有 Lean 编译或外部提交；“通过”指所述数学推导已独立审阅、脚本已复跑，
不表示 ζ(9) 无理性已证明。

## 1. 方向与移动有理投影

审阅 [direction-frontier-2026-10-01.md](direction-frontier-2026-10-01.md)
及其实际依赖的方向、输出标准形和固定轴论文。

- 原有 V 与 transport 结论下，J、liminf σ=0、最短本原整数输出不最终固定
  与 ζ(9) 无理性等价。S 的全序列 σ→0 是更强条件；没有把所有开放 DAG 节点
  计为独立障碍，也没有把原已证明的 CP 等价性记为新成果。
- 整数 common scale 下 T=||u||²、C=〈u,v〉、Ω²=TR−C²、G=gcd(T,C)，
  reduced projection denominator Q=T/G，且 Q²η²=Ω²/G²，均由直接约分核验。
- κ 的交替非零极限保证 Qζ(9)−P 最终非零。
  |Qζ(9)−P|²=κ²/(G²/Ω²) 是精确恒等式，故趋零需要新的 gcd/面积增长条件。
  没有从实面积变小或 Smith 指标单独推断该增长。
- 10 个实际参数、4 次相邻误差变号和 23 个 Smith/gcd 对照被根代理独立复跑。
  所有 finite checks 通过，当前参数没有 primitive 值小于 1。

## 2. Mellin 矩形子式与约分

审阅 [mellin-unshifted-frontier-2026-10-01.md](mellin-unshifted-frontier-2026-10-01.md)。

- 正交多项式恒等式 p_n(1)∫p_n τ=∫p_n²τ>0 排除增量为零。
  Schur complement 与 mixed minor 给出严格平方增量，含 N=0 的可积性。
- 矩形 powered Hilbert 矩阵与 [bᵀ;C] 的整数 unimodular 行变换保持 maximal-minor
  ideal。所有大素数分母都是单位，约分后 numerator gcd 的定义与局部赋值匹配。
- Jacobi 恒等式的所选对角项证明 v_p(P)≥max(0,d−2δ)，不依赖简单根或 rank-one。
  δ=0 时的精确保留，以及全局 F | P_large J²、P≥F/J² 都通过。
- Beta/Jacobi norm 公式和实权夹逼给出 raw determinant 二次率；没有误用为
  reduced numerator 的渐近下界。
- 根代理复跑 24 个未平移和 23 个不同的固定/线性右移参数，全部通过。
  独立 reviewer 又用标准库 Fraction 核实 N=6,D=3,p=19 的完全抵消反例。
  D=7,...,24 的 J=1 是这些有限参数的全部大素数结论，不是任意 D 的定理。

## 3. 固定维数、分子与任意有效极点

审阅 [pole-dimension-frontier-2026-10-01.md](pole-dimension-frontier-2026-10-01.md)。

- Lagrange 加 tail 基覆盖整个 h 维多项式空间；完整多项式商被保留，最高系数
  det K_B ∏a_i⁸S(−a_i²) 非零。primitive 倍率可能是有理数，已控制其分母。
- 半区素数下一个平方类最多四个代表，丢失一个高极点常数至多省去三次差的赋值，
  而损失九次调和负赋值；主子式的唯一最低项因此仍成立。
- 固定维数正 Gram 的区间积分下界只损失 O(log b)，不会抵消半区素数成本。
  移动 h 或移动 numerator degree 时，这个固定复杂度结论不能直接推广。
- 已核查 m≥deg S+2h+4 时全部 X 矩消失；primitive 常数 1 不能作为趋零证据。
  h=1,m=5 相邻族的非零 X 系数与独立共同调和素数证明也通过。
- 根代理复跑 87 例，包括 61 个 good prime、32 个碰撞和 6 个最大四点碰撞；全部通过。

## 4. 可移动低高度正分子

根代理推导 [bounded-numerator-barrier-2026-10-01.md](bounded-numerator-barrier-2026-10-01.md)，
arithmetic_review 与 small_polynomial_family 分别独立全文审阅通过。

- 对固定 h≥m、固定 degree bound，整数 clearer、tail determinant 与极点评价的
  高度上界统一损失至多 h log H；所有异常素数乘积由明确非零整数控制。
- 非负单位系数多项式的闭锥球面截面紧致。每个非零成员在固定区间的 Gram 积分
  严格正，连续性给统一正下界。不能以有限 positive sample 代替此紧集步骤。
- 合并 arithmetic loss 与真实积分的 h log H 后，得到
  log P≥9(θ(b)−θ(b/2))−9mh log H−O(log b)，而非猜测的最优高度阈值。
- 根代理运行 204 例，检查完整单项式 matrix、插值 determinant、独立 basis product
  泛函与 matrix congruence、全部 primitive 系数、469 个 prime valuations，
  其中 54 个碰撞。全部通过。

## 5. 聚簇统一公式与相邻极点的完整次数分类

根代理阅读全文并独立重构
[cluster-pole-frontier-2026-10-01.md](cluster-pole-frontier-2026-10-01.md) 与
[consecutive-pole-frontier-2026-10-01.md](consecutive-pole-frontier-2026-10-01.md) 的证明。

- 聚簇稿保留完整 quotient 和全部 residues。明确整数 L 清 centered R 与 B，
  log L 由短区间 lcm 熵界控制。对每个 p，binomial 的各层倍数计数差为 0 或 1，
  直接证明 lcm(a+1,...,b) | binom(b,b−a)lcm(1,...,b−a)。因此 W=o(b)
  已足够，不必再要求 W log b=o(b)。
- 正确的小素数损失是 9π(√a)log a，包含高次幂；不能写成未经证明的 9ψ(√a)。
  大坏素数损失至多 9log(L|A_d|)。primitive 倍率分母整除 |A_d|，正整数
  L^h T^d 直接给上界，故 log c=d log T+o(b)。次数 d 的变化被统一控制。
- 固定次数非负分子与单位 p 向量的紧集正性给所有实 Gram eigenvalues 的统一
  下界；全部固定 moments 给上界。两边都只贡献 o(b)，因此精确公式
  log P/b−9deg P→0 成立。d=0 必须单列为 primitive 常数 1。
- 相邻 S=1 稿的全 rank 公式已核查：m≤h 的 Vandermonde 分解；h<m≤h+4
  的 Jacobi–Trudi 与严格正 Schur 表；低秩前零块和 active 反对角 1；
  m≥2h+4 全 X 矩消失。Schur 行反转的符号也逐项核对。
- G(ζ9)>0 与 B 对称保证 deg det G=rank B，避免只看 B 的秩却忽略最高系数
  消失。相邻 centered entries 是 Q(M)，具体多项式 clearer 使坏素数损失仅
  O(log²b)。真实 Gram 的控制收敛给 Δ∼M^(-2mh)det H_h>0。
- 固定正分子与固定偏移仅声称 centered 系数是有理函数、次数最终稳定；
  没有把 S=1 的显式 rank 公式误套到任意分子。

两稿全参数数学推导通过。根代理运行聚簇验证的 20 例、17 个 good-prime checks，
并接手完成相邻 verifier：181 例、464 个 whole-harmonic prime checks，含 20 个
次数零例，全部通过。独立 Schur 表分支递归用于核对 Jacobi–Trudi 符号与值。
算术 reviewer 与 Mellin 作者分别独立全文审阅了两稿；原 pole 作者因运行容量
中断未完成 verifier，其数学稿保留，脚本与证书由根代理完成。
算术 reviewer 随后又独立读审根代理完成的相邻 verifier，确认 Schur 分支、
完全齐次递推、entry clearer 与 whole-harmonic 归一化边界均通过，未发现 issue。

## 6. 交叉审阅的归属

arithmetic_review 在方向稿 §8 记录对另外三稿的独立审阅；Mellin 与 pole 作者
也分别交流和核查关键公式。根代理逐稿重新检查上述数学节点并独立运行脚本。
书面证明仍以既有正泛函、Gram 积分与标准素数定理为依赖；精确脚本不证明这些
无穷命题。所有尚未关闭的方向、gcd 渐近和复杂度增长范围都保留其开放状态。
