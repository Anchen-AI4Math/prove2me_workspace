# 原源算术下界的四段路线

原目标 `DeterminantContradiction.actual_minor_arithmetic_lower_bound` 在本次已保存的实际平台 graph 中有同名 Proved 节点 `bd566832-025d-4e8f-95cf-c42d37b6db92`，但它导入社区 `FixedDeterminantFamily`。该目标不能用于源固定数据；新目标采用同 namespace 的 `_source017`。平台通用辅助结论仍须由 root 查重并核对完整类型。

机械图闭包为 125 个 CI 名字，其中 51 个由现有实际源 provider 声明提供。其余 73 个 helper CI 名字对应 68 个原 AST 命令，另有五个真正的 lazy equation CI，不能把它们误当遗漏的五个源码证明命令。完整 AST 字节区间、原/port 哈希、实际各步停靠接口和 equations 名字见 `arithmetic-route.json`。

已有 port 中 `Arithmetic.lcm_mul_log_coeff_gaussian` 的一条版本适配将 `ite_eq_right hk0` 换为 `if_neg hk0`，陈述未改。路线 JSON 明确记录此唯一命令差异，不将它宣称为逐字原始 proof。未来 stage 必须保留 original/port 哈希与该差异，并对实际源/生成证明进行 Std3 检查；本次没有改动原 port。

| 可复用结论 | 新 AST 命令数 | 原证明/数据行数 | 数学作用 |
|---|---:|---:|---|
| `Arithmetic.shifted_truncation_product_coeff_gaussian` | 9 | 89 | 截断对数多项式积乘源公分母后的系数属于高斯整数 |
| `InterpolationMatrix.entry_truncatedLog_cleared_gaussian` | 14 | 185 | 将上一步与原 RowTranslation 系数展开应用到实际矩阵条目 |
| `MatrixArithmetic.selectedMinor_arithmetic_lower_bound` | 43 | 435 | 对选定方形子式清分母，估计行列代价并除以正行数和高度 |
| `DeterminantContradiction.actual_minor_arithmetic_lower_bound_source017` | 3 | 17 | 把一般矩阵下界代入原固定 admissible data |

第一、二组适合先以完整源切片尝试 whole-file 300 秒预检。第三组若超限，可在真实的 `selectedMinor_clearing_bound`（MatrixArithmetic AST 16341:17643，337–358 行）再拆一项实质定理，然后证明其成本估计与归一化；不把每个低层代数计算独立发布。时间上限仍须由实际 root-only 编译决定，这里没有宣称任何未编译组已通过预算。

第一段可直接开始：无需新 data provider。后续切片内保留原 RowTranslation 的 `multiIndex/shift/shiftCoefficient` 和 MatrixArithmetic 的 `columnScale/rowScale/denominator/columnCost/rowCost` 定义，或在需要稳定公开接口时将这些纯数据定义单独发布；不能将复杂证明塞入 Def。

对应原源源码 imports 是 Arithmetic 的七个实际 Mathlib 模块、InterpolationMatrix 已 Published 数据、以及原 RowTranslation 切片所需实际 Mathlib 模块。未来 stage 应选这个原 import 闭包或已证完备子集，而非 blanket `Mathlib`。AP8 full-minor 和 AP11 collision-rate 是未来 NoFixedData 的真正父项；它们不参与这个算术下界，所以此阶段不为 graph 人为导入它们。
