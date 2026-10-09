# Stage 7：数学证明网络与形式化对应关系

基于 `1d14c145e8d447efe040e30b18c52e543f6cf49e`，继续 `codex/jsp001022-exposition-stage1`。

本轮完成[第五章](../papers/jsp001022_exposition/sections/05-formalization.tex)、[数学网络 A 的 TikZ 源码](../papers/jsp001022_exposition/figures/stage7-math-network.tex)和[源码调用网络 B 的 TikZ 源码](../papers/jsp001022_exposition/figures/stage7-source-network.tex)。B 分四个连续面板，重复编号是同一节点的跨面板端口。主 LaTeX 文件仅增加 TikZ 宏包和 `arrows.meta` 库；没有改前四章、Lean、锁文件或审计文件，没有运行 Lean 或生成 PDF。

第五章由名称列表改为数学总览、Prim 已有模块、扩展接口、两类网络及核查范围。本文没有补齐一个原本缺失的 Prim 概率证明：固定 Prim 已有完整整除链构造；扩展补充 Abel 密度路线及陈述接口。

## 1. 版本、方法与箭头含义

- P 文件：[Prim 固定提交](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean)，14592 行，Git blob `2253ddbb66acd78b36395d3e678e2cf7cc51c107`。
- E 文件：[扩展固定证明提交](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean)，1200 行，Git blob `b1e1c5452b1b475db5da8d0c514feebaf3398105`。
- 数学来源为 Alexeev 等人 [arXiv:2605.00301v1](https://arxiv.org/pdf/2605.00301v1)，特别是 Example 2.8 与第 9 节；本轮使用前几阶段保存的论文及固定源码。

先去掉 Lean 注释（包括嵌套块注释）和字符串，定位声明及证明体中的标识符，再核读实际引用行。Blueprint 说明里的名称不算调用。以下“直接引用”特指证明体显式出现的声明名，不包括策略展开、实例搜索、简化器自动依赖或编译证明项的完整依赖。源码检索不能替代 `Expr.getUsedConstants` 审计，也没有重新运行历史验证。

图 A 的箭头是数学命题连接，可包含正文已经完成的多步论证。图 B 的箭头一律是 **被引用声明 → 引用者**；不画没有直接名称引用的假设传递边，也不把间接路径画成直接边。图 B 保留所选 34 个 P 定理与全部 15 个 E 声明之间的全部 52 条直接引用边；并未包含所有 Prim 定义、辅助引理或 Mathlib 节点。两图都是有向无环图。

## 2. 数学网络 A：逐条连接依据

图中左路是密度转换，右路是独立构造的概率模型，二者在正密度与矩估计下汇合。随机模型本身不需要 A 的正密度。选择的路径可以依赖 A，但不能随 x 改变。

| 图中连接 | 正文依据与使用条件 |
| --- | --- |
| 原假设 → 有限 Abel 与主项 | 第二章 `lem:eventual` 把正 liminf 转为最终前缀界；`eq:finite-abel` 和 `eq:main-term` 给出整数尺度下界。 |
| 有限 Abel 与主项 → Δ(A)>0 | `prop:bridge`，包括有限前缀损失、取整误差及严格截断转换。 |
| 权重及严格入流 → 伴随核与路径空间 | `prop:mangoldt-inflow`、`eq:upward-normalization`、`eq:chain-cylinders`；权重严格正，核非负归一化，离散可测性允许路径测度构造。 |
| 路径空间 → 访问及权重比较模块 | `prop:visit-identity` 使用路径数据及有限递推；该模块同时使用权重定义的解析误差 `eq:weight-summable-error`，得到 `eq:mangoldt-density-equality`。这不是声称任意随机链自动满足权重比较。 |
| 访问及权重比较 → 矩与尺度 | `eq:first-moment-weight`、`eq:moment-terminal-bound`、`eq:omega-erdos-product`、Mertens 估计合成 `eq:moment-goals`；再按 `eq:fatou-scale-sequence` 选择尺度。 |
| Δ(A)>0 → 固定样本选择 | 提供有限目标 d=Δ(A)>0；它与矩输入共同使用，并非单独蕴含随机变量路径下界。 |
| 矩与尺度 → 固定样本选择 | `eq:uniform-integrable-tail`、`eq:truncated-reverse-fatou`、`eq:fatou-extended-expectation`，以及随后用 d−F 的反证，得到存在 ω₀ 达到完整 d。 |
| 固定样本 → 固定环境链 | 令 m_i=X_i(ω₀)，由序列尺度与全尺度比较得 `eq:ambient-hits`；绝非对所有随机路径的断言。 |
| 固定环境链 → 集合内子链 | `lem:extract`；枚举命中指标、传递整除关系并保持截断计数。 |
| Δ(A)>0 → 集合内子链 | 正下界排除只有有限次命中的情形，保证抽取的链无限。 |
| 集合内子链 → 指标及截断转换 | 第四章：a_i≥i 与 b_j≥j+1 保证有限截断，唯一逆像指标严格递增；改为严格截断并处理扩展非负上极限。 |
| 转换 → JSP-001022 | `thm:main`，下界仍为完整 Δ(A)，不是辅助 c 或 c/2。 |

图中合流节点须同时使用其输入及该节点标明的正文命题。图 A 不用于反推某条 Lean 直接引用。

## 3. Prim 节点索引

从 P30 反向追溯，P28/P29 给出环境链与子链；P28 再通过 P12/P27 接到权重比较与模型选择；P27 通过 P24/P26 接到模型存在性及路径提取。P24 将构造数据、二阶矩、Fatou 原则同时打包，是真实源码中的合成位置。

| 编号 | 准确声明名 | 数学职责 | 固定起始行 |
| --- | --- | --- | --- |
| P01 | `mangoldt_weight_incoming_integral_bridge` | 入流积分桥梁 | [8610](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L8610) |
| P02 | `mangoldt_weight_reciprocal_zeta_endpoint_evaluation` | 倒数 ζ 端点 | [9395](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9395) |
| P03 | `mangoldt_weight_von_mangoldt_invariant_recurrence` | 严格入流递推 | [9423](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9423) |
| P04 | `mangoldt_von_mangoldt_downward_kernel_invariant_exists` | 下降核 | [9521](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9521) |
| P05 | `mangoldt_adjoint_kernel_package_exists` | 伴随向上核 | [9677](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9677) |
| P06 | `mangoldt_adjoint_kernel_path_data_exists` | 无限路径数据 | [9900](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9900) |
| P07 | `mangoldt_adjoint_visit_identity_from_kernel_path_data` | 访问恒等式 | [10232](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10232) |
| P08 | `mangoldt_adjoint_constructed_path_data_from_kernel_path_data` | 构造数据转换 | [14217](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14217) |
| P09 | `mangoldt_adjoint_constructed_path_data_exists` | 构造数据存在 | [14246](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14246) |
| P10 | `mangoldt_weight_erdos_pointwise_error_bound` | 权重点态误差 | [7703](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7703) |
| P11 | `mangoldt_weight_erdos_summable_error` | 误差可求和 | [7727](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7727) |
| P12 | `mangoldt_weight_aggregate_comparison` | 密度比较 | [7962](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7962) |
| P13 | `mangoldt_adjoint_card_factors_erdos_real_terminal_sum_bound_local` | Erdős 终端矩界 | [12489](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12489) |
| P14 | `mangoldt_adjoint_mangoldt_positive_part_le_erdos_local` | 权重点态支配 | [12629](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12629) |
| P15 | `mangoldt_adjoint_card_factors_weighted_terminal_sum_bound` | Mangoldt 终端矩界 | [12817](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12817) |
| P16 | `mangoldt_adjoint_two_point_divisor_bound_from_constructed_path_data` | 二点计数界 | [10913](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10913) |
| P17 | `mangoldt_adjoint_second_moment_bound_from_two_point_divisor_bound` | 终端界转二阶矩 | [12870](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12870) |
| P18 | `mangoldt_adjoint_second_moment_bound_from_constructed_path_data` | 构造数据的二阶矩 | [14149](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14149) |
| P19 | `mangoldt_adjoint_normalized_hit_expectation_limsup_from_visit_identity` | 一阶矩上极限 | [12941](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12941) |
| P20 | `mangoldt_adjoint_hit_count_moment_bridge_from_first_second` | 计数与积分桥梁 | [13677](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L13677) |
| P21 | `mangoldt_adjoint_reverse_fatou_bridge_from_uniform_integrability` | 截断反向 Fatou | [13831](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L13831) |
| P22 | `mangoldt_adjoint_reverse_fatou_extraction_principle_from_constructed_path_data` | 构造数据的提取原则 | [14182](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14182) |
| P23 | `mangoldt_adjoint_random_model_from_constructed_path_data` | 模型打包 | [14276](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14276) |
| P24 | `mangoldt_adjoint_random_model_exists` | 随机模型存在 | [14328](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14328) |
| P25 | `mangoldt_adjoint_reverse_fatou_extraction_principle_from_model` | 模型性质投影 | [14302](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14302) |
| P26 | `mangoldt_adjoint_reverse_fatou_path_extraction` | 固定路径提取 | [14366](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14366) |
| P27 | `mangoldt_adjoint_chain_density_selection` | 环境链选择 | [14397](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14397) |
| P28 | `probabilistic_dense_ambient_chain` | 原权重环境链 | [14423](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14423) |
| P29 | `dense_hits_subchain_in_set` | 集合内子链 | [14464](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14464) |
| P30 | `erdos_sarkozy_szemeredi_1217` | Prim 最终定理 | [14584](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14584) |
| P31 | `mangoldt_log_reciprocal_main_term_bound` | 离散双对数主项 | [11114](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11114) |
| P32 | `mangoldt_log_reciprocal_floor_loglog_bound` | 取整误差 | [11545](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11545) |
| P33 | `mertens_prime_reciprocal` | 素数 Mertens | [11826](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11826) |
| P34 | `mangoldt_adjoint_card_factors_erdos_natural_product_bound_local` | 素数幂乘积界 | [12317](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12317) |

P 文件另在第 6813 行定义 `mangoldt_weight`。图 B 选取定理节点，不把定义展开画成一条统一“权重 → 一切”的箭头。P01、P02、P10 等节点的解析输入见第 6 节。

## 4. 扩展 E01–E15：职责与直接引用

表中名称保留完整命名空间。第三列为其余 E 声明的直接引用；第四列为全部直接显式引用的 Prim **定理**，Prim 定义展开单列于下一表。Mathlib 常量未逐项列出。

| 编号与固定位置 | 声明及准确职责 | 直接 E 引用 | 直接 Prim 定理 |
| --- | --- | --- | --- |
| E01 [7](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L7) | `LeanCompletion.jsp_001022_eventual_lower_bound`：正下极限的最终正下界 | — | — |
| E02 [38](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L38) | `LeanCompletion.jsp_001022_finite_abel_lower_bound`：非负序列有限 Abel 下界 | — | — |
| E03 [112](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L112) | `LeanCompletion.jsp_001022_reciprocal_weight_specialization`：倒数指示权专门化 | E02 | — |
| E04 [155](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L155) | `LeanCompletion.jsp_001022_natural_loglog_lower_bound`：整数尺度双对数下界 | E03 | P31 |
| E05 [198](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L198) | `LeanCompletion.jsp_001022_eventual_to_finite_prefix`：最终界转有限前缀假设 | — | — |
| E06 [246](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L246) | `LeanCompletion.jsp_001022_density_to_natural_erdos_lower_bound`：组合整数尺度密度下界 | E01, E04, E05 | — |
| E07 [293](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L293) | `LeanCompletion.jsp_001022_density_bridge`：正下密度推出正加权密度 | E06 | P31, P32 |
| E08 [428](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L428) | `LeanCompletion.erdos_1217_explicit`：展开 Prim 整除链结论 | — | P30 |
| E09 [447](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L447) | `LeanCompletion.jsp_001022_chain_strict_cutoff`：链计数严格截断 | — | — |
| E10 [528](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L528) | `LeanCompletion.jsp_001022_reciprocal_strict_cutoff`：倒数和严格截断 | — | — |
| E11 [649](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L649) | `LeanCompletion.jsp_001022_erdos_strict_cutoff`：Erdős 和严格截断 | — | P31 |
| E12 [868](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L868) | `LeanCompletion.jsp_001022_erdos_density_ennreal`：实数与 ENNReal 加权上极限 | E11 | P31 |
| E13 [1029](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1029) | `LeanCompletion.jsp_001022_positive_enumeration_sums`：正整数枚举及有限求和 | — | — |
| E14 [1077](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1077) | `LeanCompletion.jsp_001022_positive_subsequence_indices`：子序列指标与精确计数 | — | — |
| E15 [1136](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1136) | `LeanCompletion.jsp_001022_original_enumeration_chain`：原问题枚举形式 | E07, E08, E09, E10, E12, E13, E14 | — |

E01 使用正 liminf 的一半作为最终下界；正文则允许任意 0<c<下对数密度。E02 内部的强化归纳保留终点 S(t)/log t；导出的类型为较弱的有限不等式。E07 仅声明正密度蕴含，不声明正文的完整常数比较。

E08 将上游结构化链结论展开成后续可用的严格单调、整除、成员关系与密度界。E09 的计数 limsup 在 ENNReal 中处理；E10 的倒数和处理实数 liminf；E11 的 Erdős 和处理实数 limsup；E12 在加权目标有限后连接实数与 ENNReal。E13 对一般权重证明枚举求和，并包含无限性与有限截断条件；E14 通过唯一逆像形成正整数指标并保持精确计数。E15 才组合这些接口。

| E 声明 | 证明体还显式引用或展开的 Prim 定义 |
| --- | --- |
| E01 | `real_initial_segment` (6783) |
| E02 | — |
| E03 | `erdos_weight` (13) |
| E04 | `erdos_weight` (13) |
| E05 | `real_initial_segment` (6783) |
| E06 | `erdos_sum` (22), `erdos_sum_up_to` (6792), `erdos_weight` (13), `real_initial_segment` (6783) |
| E07 | `erdos_sum` (22), `erdos_sum_up_to` (6792), `erdos_weight` (13), `real_initial_segment` (6783), `upper_doubly_log_density` (6802) |
| E08 | `chain_count_up_to` (6849), `chain_in_set` (6841), `erdos_sum_up_to` (6792), `real_initial_segment` (6783), `upper_chain_density` (6858), `upper_chain_density_at_least` (6871), `upper_doubly_log_density` (6802) |
| E09 | — |
| E10 | `real_initial_segment` (6783) |
| E11 | `erdos_sum` (22), `erdos_sum_up_to` (6792), `erdos_weight` (13), `real_initial_segment` (6783) |
| E12 | `erdos_sum` (22), `erdos_sum_up_to` (6792), `erdos_weight` (13), `real_initial_segment` (6783), `upper_doubly_log_density` (6802) |
| E13 | — |
| E14 | — |
| E15 | `erdos_sum` (22), `erdos_sum_up_to` (6792), `erdos_weight` (13), `real_initial_segment` (6783), `upper_doubly_log_density` (6802) |

上表限定证明体，不把声明类型中的每个定义列为调用边。横线仅表示在这一范围内没有相应引用；不能解读为该声明无基础库依赖。

## 5. 源码网络 B：全部 52 条箭头的证据

每行的引用行位于**箭头终点**的证明体；该行是直接名称引用的证据。表中 P/E 行号分别链接固定 P/E 文件。重复节点在四个面板之间只起连接作用。

| 箭头 | 调用位置 | 所传递或使用的结论 |
| --- | --- | --- |
| E01 → E06 | [E:255](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L255) | 正下极限的最终正下界 |
| E02 → E03 | [E:149](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L149) | 非负序列有限 Abel 下界 |
| E03 → E04 | [E:181](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L181) | 倒数指示权专门化 |
| E04 → E06 | [E:259](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L259) | 整数尺度双对数下界 |
| E05 → E06 | [E:257](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L257) | 最终界转有限前缀假设 |
| E06 → E07 | [E:302](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L302) | 组合整数尺度密度下界 |
| E07 → E15 | [E:1165](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1165) | 正下密度推出正加权密度 |
| E08 → E15 | [E:1166](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1166) | 展开 Prim 整除链结论 |
| E09 → E15 | [E:1197](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1197) | 链计数严格截断 |
| E10 → E15 | [E:1164](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1164) | 倒数和严格截断 |
| E11 → E12 | [E:1023](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1023) | Erdős 和严格截断 |
| E12 → E15 | [E:1196](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1196) | 实数与 ENNReal 加权上极限 |
| E13 → E15 | [E:1154](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1154) | 正整数枚举及有限求和 |
| E14 → E15 | [E:1170](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1170) | 子序列指标与精确计数 |
| P01 → P03 | [P:9431](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9431) | 入流积分桥梁 |
| P02 → P03 | [P:9432](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9432) | 倒数 ζ 端点 |
| P03 → P04 | [P:9569](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9569) | 严格入流递推 |
| P04 → P05 | [P:9681](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9681) | 下降核 |
| P05 → P06 | [P:9906](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9906) | 伴随向上核 |
| P06 → P09 | [P:14249](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14249) | 无限路径数据 |
| P07 → P08 | [P:14226](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14226) | 访问恒等式 |
| P08 → P09 | [P:14252](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14252) | 构造数据转换 |
| P09 → P24 | [P:14331](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14331) | 构造数据存在 |
| P10 → P11 | [P:7729](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7729) | 权重点态误差 |
| P10 → P14 | [P:12632](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12632) | 权重点态误差 |
| P11 → P12 | [P:7970](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7970) | 误差可求和 |
| P12 → P28 | [P:14430](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14430) | 密度比较 |
| P13 → P15 | [P:12827](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12827) | Erdős 终端矩界 |
| P14 → P15 | [P:12825](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12825) | 权重点态支配 |
| P15 → P17 | [P:12877](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12877) | Mangoldt 终端矩界 |
| P16 → P18 | [P:14155](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14155) | 二点计数界 |
| P17 → P18 | [P:14154](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14154) | 终端界转二阶矩 |
| P18 → P24 | [P:14332](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14332) | 构造数据的二阶矩 |
| P19 → P22 | [P:14192](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14192) | 一阶矩上极限 |
| P20 → P22 | [P:14191](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14191) | 计数与积分桥梁 |
| P21 → P22 | [P:14189](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14189) | 截断反向 Fatou |
| P22 → P24 | [P:14334](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14334) | 构造数据的提取原则 |
| P23 → P24 | [P:14337](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14337) | 模型打包 |
| P24 → P27 | [P:14402](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14402) | 随机模型存在 |
| P25 → P26 | [P:14375](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14375) | 模型性质投影 |
| P26 → P27 | [P:14403](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14403) | 固定路径提取 |
| P27 → P28 | [P:14433](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14433) | 环境链选择 |
| P28 → P30 | [P:14591](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14591) | 原权重环境链 |
| P29 → P30 | [P:14592](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14592) | 集合内子链 |
| P30 → E08 | [E:436](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L436) | Prim 最终定理 |
| P31 → E04 | [E:171](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L171) | 离散双对数主项 |
| P31 → E07 | [E:364](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L364) | 离散双对数主项 |
| P31 → E11 | [E:724](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L724) | 离散双对数主项 |
| P31 → E12 | [E:943](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L943) | 离散双对数主项 |
| P32 → E07 | [E:415](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L415) | 取整误差 |
| P33 → P13 | [P:12496](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12496) | 素数 Mertens |
| P34 → P13 | [P:12556](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12556) | 素数幂乘积界 |

本轮补正原第五章的不完整表述：**P31 → E07 也是直接引用**（E:364），不是只有 P32 → E07；P31 对 E04、E11、E12 的边也保留。E15 没有直接引用 E11，故不画 E11 → E15，而保留 E11 → E12 → E15。

以下看似自然的箭头刻意不画：

- P06 → P07：P07 假设给定路径数据，未调用路径存在定理；实际调用合成在 P08、P09。
- P07 → P19：P19 从 `hdata` 的访问性质出发，未再次调用访问恒等式定理。
- P18 → P22：P22 接收 `hsecond` 作为参数；P24 同时调用 P18 和 P22 并传参。
- P22 → P25：P25 只是模型合取性质的投影；P24 负责先构造含该性质的模型。
- P24 → P26：P26 假设已有模型；P27 调用 P24 后把所得模型交给 P26。

这些例子说明源码 DAG 不等于一条顺序执行的数学推导链，也避免把传参接口误称为循环论证。

## 6. 主图未画出的关键输入及概率边界

主图是所选定理的直接引用子图，以下下层模块仍是证明的一部分，不是新增的待证假设。

| 主图入口 | 下层源码入口与数学作用 |
| --- | --- |
| P01 | `mangoldt_weight_incoming_integral_bridge_lhs_laplace` (8440) 与 `mangoldt_weight_incoming_integral_bridge_rhs_laplace` (8129)；非负交换求和、Laplace 表示及导数恒等式合成入流积分桥梁。 |
| P02 | `reciprocal_zeta_derivative_integral_one` (9237)、`mangoldt_weight_reciprocal_zeta_integration_by_parts` (9302)；分别处理 n=1 的端点总量与 n≥2 的分部积分。更下层使用 ζ 正则性及端点极限。 |
| ζ 分析 | `mangoldt_dirichlet_series_eq_zeta_log_derivative` (1286) 为 Dirichlet 级数与 ζ 对数导数的入口；相关导数恒等式在 8101 等处调用它。 |
| P04、P05、P07 | `von_mangoldt_divisor_sum` (153) 和 `mangoldt_weight_positive` (9468) 分别支撑归一化与正分母。 |
| P06 | 9947 行调用 `ProbabilityTheory.Kernel.trajMeasure`；使用离散核、初始 Dirac 质量及轨迹测度的有限维性质，随后限制到从 1 出发、每步有效的全测度样本集合。正文对应 Ionescu–Tulcea 构造。 |
| P10、P11、P12 | 点态误差来自倒数 ζ 与 Laplace 估计；P12 还直接使用 `summable_error_limsup_transfer` (7895)。全体 A 的统一截断误差不是由访问独立性得到。 |
| P16 | `mangoldt_adjoint_pair_measure_tsum_le_index` (10661) 与 `mangoldt_adjoint_weighted_hit_tsum_le_divisor_sum` (10718)；后者使用 `mangoldt_adjoint_index_le_card_factors_of_strict_chain` (10573)，即链长≤Ω。 |
| P34 | 素数幂计数 (11950)、倍数权重求和 (12085)、几何和比较 (12221) 合成 Erdős 终端乘积界。 |
| P33 | `mangoldt_log_reciprocal_partial_summation` (11611) 与 `prime_reciprocal_mangoldt_log_bridge` (11666)；更下层回到 `mertens_von_mangoldt_reciprocal` (181) 等。正文的初等 Chebyshev/Mertens 推导与该形式化路线不同。 |
| P20 | 可测性 (13341)、一阶积分 (13367)、二阶积分 (13466) 以及有限计数桥梁；把计数矩改写为随机变量积分条件。 |
| P21 | 13944 行的 `MeasureTheory.limsup_lintegral_le` 处理截断反向 Fatou，14119 行的 `MeasureTheory.exists_lintegral_le` 用于有限分支样本提取；证明还分离无穷情形，不能把后者单独视为全部提取论证。 |

正文中的二阶矩常数可取为对 A 一致，但部分 Prim 外层类型采用 `∀ A, ∃ C, ...` 和最终成立的界。正文显式给出的 x≥e^e 统一估计，不能不加说明地逐字写成每个上游 Lean 定理的类型。同样，正文使用 `E min(F,M)≥d−C_*/M` 加单调收敛；Prim 用截断余项、可测代表和积分 limsup 定理实现对应目标。两者逻辑职责一致，而非逐行对应。

## 7. 贡献、未覆盖部分与验证范围

- **原论文**：提供不变权重、概率整除链及其密度结论的数学来源。
- **Prim**：固定源码已有权重、核、无限路径、访问与矩估计、Fatou 选择、环境链及集合内子链的完整形式化路线。
- **当前扩展**：E01–E07 的有限求和及密度接口，E08 的结果展开，E09–E14 的截断、值域与枚举接口，E15 的最终组合。
- **本文阐释**：中文数学推导、强于 E07 类型的常数比较、若干替代分析证明及依赖网络整理；这些不因写入文章就自动成为新 Lean 声明。

未覆盖：全部 Mathlib 常量、类型类及策略自动引入的依赖、完整编译证明项、公理闭包的新检查、历史验证重新执行、1966 年历史原文页面重新核对。第五章保留已有工作与历史验证的边界说明，不声称首次形式化、数学优先权或新的独立机器验证。

静态检查范围：图 A 的 12 条数学连接有上表依据；图 B 的 52 条边均定位到固定证明体引用行，所选节点间无遗漏引用且无环；检查 LaTeX 标签、环境、输入路径、Markdown 本地链接和受保护文件未改。仅添加两份手工组织的 TikZ 网络源码、第五章、必要的导言区加载及本说明；临时源码索引和检索输出不入库。

**未解决事项**：本轮未发现新的数学闭环问题。由于按要求不生成 PDF，图的字体大小、箭头交叉和分页尚未经渲染检查；最终编辑阶段应在 Linux 编译后检查。主文件原有阶段摘要、统一术语和参考文献整理也留到该阶段，本轮仅修改其图依赖加载。没有提前发布论文或进行其他项目工作。
