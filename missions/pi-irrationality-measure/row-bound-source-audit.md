# 平台行界叶子与 OpenAI 源结果的接口核对

核对对象：平台快照 `platform/leaf-5b9ab31c-d24b-4336-adec-68429fdf66ff.json`，即 `actual_minor_row_l1_exp_bound`。这是 2026-10-07 20:01 UTC 保存的前沿，后续查询失败时不把该快照当作最新状态。

OpenAI 原始提交为 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。其 [AnalyticAggregate.lean 的原定理](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L53-L72) 控制的是

$$
\frac{\log\lVert\det M\rVert}{\#\mathrm{Row}\cdot H}
\leq E_d(H),
$$

并显式要求该子式的行列式非零。源证明先作平移行列式展开，再控制展开项的行列式，最后求和；碰撞收益在这些行列式估计中出现。相关源接口为 [norm_actual_summand_le](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L201) 与 [translated_summand_bound](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean#L80)。

平台新叶子要求每个原始子式行满足

$$
\sum_j\lVert M_{ij}\rVert\leq \exp(H E_d(H)),
$$

而且列选择是任意函数，没有非零行列式条件。这需要独立论证，不能把源行列式定理直接充当这个行界。列选择允许重复，使得逐行估计与非零子式估计的区别尤其重要。

这个核对不是新叶子的反证：`FixedData` 本身包含强逼近及参数条件，不能在未构造满足全部条件的数据之前声称存在反例。

当前移植路线保留源 `LiteralAnalytic.actual_minor_analytic_bound` 的准确条件，通过 `analyticAggregate` 与几何插值构造 `pi_approximation_determinant_sequences`，再连接上界 2。新增的通用行列式行和不等式是独立有效的矩阵引理；它的完成不代表上述逐行指数界已经完成。
