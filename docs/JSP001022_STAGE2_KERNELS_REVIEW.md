# 第三章第二阶段：不变权重与向上随机整除链

本轮只补第三章 3.1–3.2。3.3–3.5 分别保留访问恒等式、矩估计和反向 Fatou 的待办位置；3.6 的子链提取引理及证明保持原文。第一、二、四、五章与主文件不改，故主文件摘要中的阶段描述仍是第一阶段文字，待后续统一更新。

[修改后的第三章](../papers/jsp001022_exposition/sections/03-chain.tex)。原论文依据为 [Alexeev 等人 arXiv:2605.00301v1](https://arxiv.org/pdf/2605.00301v1) 第 2 节 Example 2.4、Definition 2.7、Example 2.8、Definition 2.9、Example 2.11，以及第 9 节的链构造。未以二手转述代替原文。

## 1. 新增公式与证明

状态空间是正整数，时间从 0 开始。准确权重为

\[
\nu_\Lambda(1)=1,\qquad
\nu_\Lambda(n)=\int_1^\infty\frac{\log n}{\zeta(s)n^s}\,ds\quad(n\ge2).
\]

因为被积函数严格为正且不超过 \(\log n\,n^{-s}\)，得到 \(0<\nu_\Lambda(n)\le1/n\)（\(n\ge2\)）。此上界是正文辅助推导，不宣称是指定接口导出的精确 Lean 类型。Erdős 权重 \(\nu_0(n)=1/(n\log n)\) 仅对 \(n\ge2\) 使用，可补 \(\nu_0(1)=0\)。两种权重的端点不同。

写 \(h=1/\zeta\)。正文由级数与积分比较证明 \(h(1+)=0\)、\(h(\infty)=1\)，由 Euler 乘积的对数导数得到

\[
h'(s)=h(s)\sum_{q\ge2}\Lambda(q)q^{-s},\qquad
\int_1^\infty h'(s)\,ds=1.
\]

非负性允许 Tonelli 换序，于是

\[
\sum_{q\ge2}\nu_\Lambda(nq)\frac{\Lambda(q)}{\log(nq)}
=\int_1^\infty n^{-s}h'(s)\,ds=\nu_\Lambda(n).
\]

最后一个等号在 \(n=1\) 时来自端点差；在 \(n\ge2\) 时来自分部积分。正文写明边界项为零及两侧的可积控制。交换时不预设级数有限；最终积分不超过 \(\int h'=1\)，同时证明可和性。

下降核在 \(n\ge2\)、\(m\mid n\)、\(m<n\) 时为 \(\Lambda(n/m)/\log n\)，其余为零，另设 \(P_\downarrow(1,1)=1\)。素因子分解给出 \(\sum_{d\mid n}\Lambda(d)=\log n\)，因而每行非负且和为 1。

向上核为

\[
U(m,mq)=\frac{\nu_\Lambda(mq)}{\nu_\Lambda(m)}
\frac{\Lambda(q)}{\log(mq)}\quad(q\ge2),
\]

其他转移为零。严格入流恒等式除以正数 \(\nu_\Lambda(m)\) 证明每行和为 1。非零转移仅支持严格整除，商实际为素数幂。伴随关系仅对不同状态成立：

\[
\nu_\Lambda(m)U(m,n)=\nu_\Lambda(n)P_\downarrow(n,m)\quad(m\ne n).
\]

以初始分布 \(\delta_1\) 和转移核 \(U\) 应用 Ionescu–Tulcea 定理，得到同一个无限乘积空间上的过程，柱集质量为

\[
\mathbb P(X_0=n_0,\ldots,X_r=n_r)
=\mathbf1_{n_0=1}\prod_{i<r}U(n_i,n_{i+1}).
\]

行归一化保证有限维分布相容。相邻二坐标概率公式使每个零转移事件为零测集；对可数时间取交，得到一个满测度的可测路径集合。限制到该集合后，每条路径都从 1 开始且严格递增、相邻整除。于是 \(X_k\ge2^k\)。这只完成随机链构造，不是对给定集合 \(A\) 的密度路径提取。

## 2. Prim 对应与实际调用

所有 Prim 链接固定于提交 `a303f6bd23bb8f29a833d1d70327528359180995` 的 `LeanMarathon/Main.lean`。以下是源码中可见的声明和显式调用职责，不是重新 elaboration 得到的完整传递依赖图。

| 数学结论 | 固定源码入口 | 实际调用及作用 |
| --- | --- | --- |
| 因子和等于对数 | [`von_mangoldt_divisor_sum`, L153](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L153) | 直接使用 mathlib 的 `ArithmeticFunction.vonMangoldt_sum`；下降行归一化的有限和依据。 |
| ζ 的对数导数级数 | [`mangoldt_dirichlet_series_eq_zeta_log_derivative`, L1286](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L1286) | 使用 `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`，并转换复数表达式与实数级数。 |
| 权重准确公式 | [`mangoldt_weight`, L6813](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L6813) | `n = 1` 时取 1；否则在 `Set.Ioi 1` 积分，分母为 `riemannZeta` 的实部乘 `Real.rpow n s`。数学状态空间排除 0。 |
| 积分存在与严格正性 | [`mangoldt_weight_positive`, L9468](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9468) | 调用 `mangoldt_weight_integral_change_of_variables_mangoldt_laplace`（L7189）和 `mangoldt_weight_integral_change_of_variables_zeta_kernel_integrable`（L7317）；平移为正半轴 Laplace 积分，在正测度区间上使用严格正性。 |
| 求和与积分桥接 | [`mangoldt_weight_incoming_integral_bridge`, L8610](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L8610) | 直接组合同前缀的 `lhs_laplace`（L8440）与 `rhs_laplace`（L8129）。前者使用 `term_laplace`、`weighted_summable`、`inner_tsum`，并以 `MeasureTheory.integral_tsum_of_summable_integral_norm` 换序；其加权可和性借助已有尾项估计。因此源码走绝对可积桥接，正文走 Tonelli，不能混称逐行翻译。 |
| 倒数 ζ 的两个端点 | [`reciprocal_zeta_tendsto_one_right`, L8639](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L8639)、[`reciprocal_zeta_tendsto_at_top`, L8722](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L8722) | 前者使用 `reciprocal_zeta_second_order_bound`；后者用可求和控制下的级数极限。正文用初等积分比较给出这两个极限，避免展开与本轮无关的定量误差分析。 |
| 入流积分的端点评估 | [`mangoldt_weight_reciprocal_zeta_endpoint_evaluation`, L9395](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9395) | 按 `n=1` 分情况，分别调用 `reciprocal_zeta_derivative_integral_one`（L9237）和 `mangoldt_weight_reciprocal_zeta_integration_by_parts`（L9302）。两者使用 `reciprocal_zeta_ibp_regularity`（L8852）提供可积性及导数条件，以 `MeasureTheory.integral_Ioi_deriv_mul_eq_sub` 完成无穷区间端点计算。 |
| 严格入流恒等式 | [`mangoldt_weight_von_mangoldt_invariant_recurrence`, L9423](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9423) | 直接重写 `mangoldt_weight_incoming_integral_bridge` 与 `mangoldt_weight_reciprocal_zeta_endpoint_evaluation`。求和明确只保留 `1 < q`。 |
| 下降核存在及全部条件 | [`mangoldt_von_mangoldt_downward_kernel_invariant_exists`, L9521](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9521) | 分段定义下降核，用 `Finset.sum_bij'` 对整数因子重新编号，调用因子和公式及上述入流递推；正整数行和为 1，状态 1 单独吸收。 |
| 向上核存在及全部条件 | [`mangoldt_adjoint_kernel_package_exists`, L9677](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9677) | 调用下降核存在定理和 `mangoldt_weight_positive`，用 `Function.Injective.tsum_eq` 按乘数重新编号，再由入流递推除以正权重。其接口 `mangoldt_adjoint_kernel_package`（L9446）同时包含非负性、正整数行和、零对角线、非对角伴随式与严格整除支撑。 |
| 无限路径及逐路径条件 | [`mangoldt_adjoint_kernel_path_data_exists`, L9900](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9900) | 由核包构造 `rowPMF`，用 `Kernel.ofFunOfCountable` 得到可测核，再经 `Kernel.comap` 读取有限历史的最后状态。`Kernel.trajMeasure (Measure.dirac 1) step` 给出无限路径测度。相邻柱集公式使用 `Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure` 与 `Measure.compProd_apply_prod`；通过可数零测事件、`MeasureTheory.ae_all_iff` 构造满测度的局部 `good` 集合，最后以 `μFull.comap Subtype.val` 限制并用 `measurePreserving_subtype_coe` 传递结论。 |

路径接口 [`mangoldt_adjoint_kernel_path_data`, L9845](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L9845) 要求总质量 1、逐样本从 1 出发、逐样本严格整除链、坐标可测、逐步非零转移，以及相邻二坐标概率公式。`mangoldt_adjoint_kernel_markov_law`（L9810）只封装最后这条公式；它本身不是完整的条件 Markov 性公理。源码实际构造的路径测度比这个导出接口提供更多结构。局部 `good` 子类型也不能与附近单独定义的 `mangoldt_adjoint_supported_path_space` 混为同一个定义。

底层概率论输入可以在固定 mathlib 提交 `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 的 [`IonescuTulcea/Traj.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean#L510) 查到：`traj` 是 Ionescu–Tulcea 构造；L762 的 `trajMeasure` 将初始分布与该构造组合；L770 的实例保证初始分布为概率测度时结果仍是概率测度；L776 的有限维投影恒等式用于上面的相邻柱集计算。这里只阅读固定源码，没有安装 mathlib。

## 3. 边界条件与可能误读

- **1 的权重不能套用积分公式。** 若将公式直接用于 1，`log 1 = 0` 会给出零；正确值必须单独定义为 1，入流等式在此由端点差得到。
- **不变性是严格入流。** 若把下降核的吸收自环算入，其流入 1 的质量还会多一个 1。这里不是包含该自环的平稳概率分布。
- **伴随式不能覆盖对角线。** \(U(1,1)=0\)，\(P_\downarrow(1,1)=1\)。去掉非对角条件即为错误公式。
- **自然数底层类型含 0，但数学过程不含 0。** 原始向上核第 0 行为零；`rowPMF` 在该行使用 `PMF.pure 1` 补全可测 Markov 核。从 1 出发不会访问 0，所以此技术处理不改变正整数链。
- **附加状态无穷不产生缺失质量。** 原论文的一般次不变权重框架允许流向无穷；本例严格入流等式使所有有限行和恰为 1，故无需该状态。
- **已有无限过程不等于已有高密度路径。** 本轮没有从期望直接挑选同时满足所有尺度要求的路径，也没有证明统一可积性或反向 Fatou。

在本轮核对范围内，未发现准确公式与上述构造之间的数学矛盾；未对后续访问恒等式、矩估计或整个 Prim 文件作完整数学审计。

## 4. 保留给下一轮的证明义务

1. 证明总访问概率等于 \(\nu_\Lambda(n)\)，包括初始状态和递推解的识别。不能把入流方程本身直接当作访问恒等式。
2. 证明与 Erdős 权重的差在集合截断求和中一致有界；本轮的 \(1/n\) 上界远远不够。
3. 建立一阶矩、利用 \(\Omega\) 控制路径访问次数的二阶矩估计，再建立归一化变量的统一可积性及反向 Fatou 所需条件。
4. 解释如何由极限论证在同一个无限样本空间中取得达到 \(\Delta(A)\) 的确定性路径，并正确处理可能的无穷值。
5. 本轮将 Euler 乘积的对数导数公式、Tonelli 定理和 Ionescu–Tulcea 定理作为明确列出的标准输入，未重新证明这些一般定理。已给出各自适用条件和在此处的作用。

## 5. 交付与检查边界

本轮只提交第三章、本文交接说明和论文目录 README。未修改任何 Lean 证明、工具链、依赖锁定文件或审计文件；未下载 Lean 环境。第二章的常数比较标注建议保留给以后，不在本轮跨章修改。

已对改动范围、LaTeX 环境与标签引用、文档相对链接和空白差异作静态检查，并核对原子链提取引理及证明未改。没有运行 Lean 或 LaTeX；源码阅读不是新的 Lean 验证，也没有生成新 PDF。下载的依赖源码、工具输出和本地研究缓存均不提交。
