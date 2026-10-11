For a square complex matrix $A$ indexed by any finite type $I$, including the empty type, we prove

$$
|\det A| \leq \prod_{i\in I}\left(\sum_{j\in I}|A_{ij}|\right).
$$

The determinant expansion selects one entry in each row and column. Taking absolute values removes the permutation signs. The resulting nonnegative sum is bounded by the sum obtained by allowing all choices of a column in each row, with no injectivity restriction.

Apply the Leibniz formula to the transpose, whose determinant equals that of $A$, and then the triangle inequality:

$$
|\det A| = |\det A^{\mathsf T}|
\leq \sum_{\sigma\in\operatorname{Sym}(I)}
\prod_{i\in I}|A_{i,\sigma(i)}|.
$$

The map from a permutation to its underlying function is injective. Every summand is nonnegative, so enlarging its image to the set of all functions gives

$$
\sum_{\sigma\in\operatorname{Sym}(I)}\prod_{i\in I}|A_{i,\sigma(i)}|
\leq \sum_{f:I\to I}\prod_{i\in I}|A_{i,f(i)}|.
$$

Finite distributivity identifies the last sum with the required product of row sums:

$$
\sum_{f:I\to I}\prod_{i\in I}|A_{i,f(i)}|
=\prod_{i\in I}\sum_{j\in I}|A_{ij}|.
$$

Empty sums and products are interpreted by their usual conventions, so no nonemptiness assumption is needed.
