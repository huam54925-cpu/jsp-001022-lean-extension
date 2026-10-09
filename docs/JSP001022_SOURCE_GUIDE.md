# JSP-001022 源码阅读指南（第一阶段）

本指南整理已核对的固定源码入口和它们的数学职责，供后续逐节写作。阅读入口不等于对全部证明体的完整人工审计。下载源码只用于本地阅读，本分支通过固定链接引用已有代码。

## 固定版本

| 来源 | 版本 | 用途 |
| --- | --- | --- |
| 本扩展 | `3992abb235729e5ebd0359d897470d6101acf908` | 十五个补充声明 |
| Prim | `a303f6bd23bb8f29a833d1d70327528359180995` | 离散主项、随机链和最终整除链定理 |
| plby/lean-proofs | `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` | 已有密度比较及集合形式链定理 |
| 扩展的审计与说明文档 | `424d5037538ff29201998528bb6265901b2a3880` | 保存于较晚文档提交的既有材料 |

## 十五个补充声明

末列只表示这十五个声明之间在源码中显式出现的直接引用；空白不表示不存在库依赖。条目由去除注释、字符串后的标识符索引定位，并核读主要调用处。未运行策略展开后的依赖审计。

| 编号 | 固定源码 | 直接引用的扩展声明 |
| --- | --- | --- |
| E01 | [`LeanCompletion.jsp_001022_eventual_lower_bound`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L7-L33)（L7） | — |
| E02 | [`LeanCompletion.jsp_001022_finite_abel_lower_bound`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L38-L108)（L38） | — |
| E03 | [`LeanCompletion.jsp_001022_reciprocal_weight_specialization`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L112-L151)（L112） | E02 |
| E04 | [`LeanCompletion.jsp_001022_natural_loglog_lower_bound`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L155-L193)（L155） | E03 |
| E05 | [`LeanCompletion.jsp_001022_eventual_to_finite_prefix`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L198-L242)（L198） | — |
| E06 | [`LeanCompletion.jsp_001022_density_to_natural_erdos_lower_bound`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L246-L289)（L246） | E01, E04, E05 |
| E07 | [`LeanCompletion.jsp_001022_density_bridge`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L293-L424)（L293） | E06 |
| E08 | [`LeanCompletion.erdos_1217_explicit`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L428-L443)（L428） | — |
| E09 | [`LeanCompletion.jsp_001022_chain_strict_cutoff`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L447-L524)（L447） | — |
| E10 | [`LeanCompletion.jsp_001022_reciprocal_strict_cutoff`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L528-L645)（L528） | — |
| E11 | [`LeanCompletion.jsp_001022_erdos_strict_cutoff`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L649-L864)（L649） | — |
| E12 | [`LeanCompletion.jsp_001022_erdos_density_ennreal`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L868-L1025)（L868） | E11 |
| E13 | [`LeanCompletion.jsp_001022_positive_enumeration_sums`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1029-L1073)（L1029） | — |
| E14 | [`LeanCompletion.jsp_001022_positive_subsequence_indices`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1077-L1132)（L1077） | — |
| E15 | [`LeanCompletion.jsp_001022_original_enumeration_chain`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/blob/3992abb235729e5ebd0359d897470d6101acf908/LeanCompletion/JSP001022.lean#L1136-L1199)（L1136） | E07, E08, E09, E10, E12, E13, E14 |

主要上游连接：E04 使用离散主项估计；E07 还使用取整的双对数误差界；E11、E12 用主项估计控制最终上界；E08 直接使用 Prim 的最终链定理。E15 的最终下界仍为完整加权上密度。

## 密度部分使用的 Prim 结果

- [`mangoldt_log_reciprocal_main_term_bound`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11114-L11191)（L11114）：离散对数增量和与 `log log N` 相差有界。
- [`mangoldt_log_reciprocal_floor_loglog_bound`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11545-L11593)（L11545）：实数取整的双对数误差界。

## 随机链部分的阅读顺序

先看主干的三个入口：

1. [`probabilistic_dense_ambient_chain`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14423-L14434)（L14423）：用权重比较和路径选取获得环境链。
2. [`mangoldt_adjoint_chain_density_selection`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14397-L14403)（L14397）：组合随机模型存在性与路径提取。
3. [`mangoldt_adjoint_random_model_exists`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14328-L14337)（L14328）：回到构造数据、二阶矩及反向 Fatou 的具体证明。

再按数学问题展开：

| 数学问题 | 对应已有代码 |
| --- | --- |
| 不变权重递推 | [`mangoldt_weight_von_mangoldt_invariant_recurrence`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9423-L9432)（L9423） |
| 伴随向上核存在性 | [`mangoldt_adjoint_kernel_package_exists`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9677-L9800)（L9677） |
| 路径测度构造 | [`mangoldt_adjoint_kernel_path_data_exists`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9900-L10158)（L9900） |
| 访问概率恒等式 | [`mangoldt_adjoint_visit_identity_from_kernel_path_data`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10232-L10508)（L10232） |
| 权重差的绝对可求和性 | [`mangoldt_weight_erdos_summable_error`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7727-L7735)（L7727） |
| 两种权重的密度比较 | [`mangoldt_weight_aggregate_comparison`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7962-L7970)（L7962） |
| 双点访问估计 | [`mangoldt_adjoint_two_point_divisor_bound_from_constructed_path_data`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10913-L10970)（L10913） |
| 质因子数加权和上界 | [`mangoldt_adjoint_card_factors_weighted_terminal_sum_bound`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12817-L12849)（L12817） |
| 二阶矩界的合成 | [`mangoldt_adjoint_second_moment_bound_from_two_point_divisor_bound`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12870-L12893)（L12870） |
| 归一化计数的一阶、二阶矩接口 | [`mangoldt_adjoint_hit_count_moment_bridge_from_first_second`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L13677-L13782)（L13677） |
| 截断反向 Fatou | [`mangoldt_adjoint_reverse_fatou_bridge_from_uniform_integrability`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L13831-L14128)（L13831） |
| 选出固定确定性路径 | [`mangoldt_adjoint_reverse_fatou_path_extraction`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14366-L14377)（L14366） |
| 提取集合内子链 | [`dense_hits_subchain_in_set`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14464-L14568)（L14464） |
| 上游最终定理 | [`erdos_sarkozy_szemeredi_1217`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14584-L14592)（L14584） |

数学原文：[arXiv:2605.00301v1](https://arxiv.org/pdf/2605.00301v1)，第 2 节给出不变权重与伴随链，第 9 节（第 27–29 页）处理访问计数、二阶矩和路径选取。下一轮先完成权重与随机链构造，之后再安排矩估计和反向 Fatou。

## 对照已有 plby 形式化

- [`lowerLogDensity_le_weightedRate`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217/Density.lean#L533-L536)（L533）：比扩展正性接口更强的密度比较。
- [`exists_divisibility_chain_of_weightedRate_pos`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217/Resolution.lean#L451-L499)（L451）：已有集合形式链定理。
- [Erdos1217 模块目录](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217)：AnalyticWeight、MarkovChain、Moments、OmegaBound、ReverseFatou、Reindex 等。
- [仓库既有比较说明](COMPARISON_WITH_PLBY.md)：离散归纳与积分 Abel 的实现差别，不应解读为新的数学解答或优先权。

## 可以直接复用的审计材料

- [Audit.lean](../LeanCompletion/Audit.lean)：第 23 行定义 `Expr.getUsedConstants` 读取器，第 40 行起导出十五个声明的类型/证明体依赖，并检查公理与模块路径。
- [targets.json](../verification/targets.json)：既有核查目标。
- [VERIFICATION.md](VERIFICATION.md)：既有复现步骤；本轮未执行。
- [2026-09-28/RESULT.md](../verification/2026-09-28/RESULT.md)：所选证明提交的历史摘要，当前树已移除原始执行日志。
- [STATEMENT_CORRESPONDENCE.md](STATEMENT_CORRESPONDENCE.md)：截断、索引和极限值域的既有对应说明。

当前文字核读不能替代编译后依赖或传递公理审计。本轮没有新的 Lean 构建结果。
