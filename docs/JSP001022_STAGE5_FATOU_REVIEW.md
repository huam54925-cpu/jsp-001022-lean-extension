# Stage 5：统一可积性、反向 Fatou 与确定性路径

基于提交 `132fc5316536e674057834c44572220c3fbc4d2e`，继续 `codex/jsp001022-exposition-stage1`。本轮交付 [第三章修改稿](../papers/jsp001022_exposition/sections/03-chain.tex) 和本说明。主要替换 3.5；按审查意见补明 3.4 的 ψ 素数幂表达及中心二项式系数中对应估值项，并更新章内过渡语和末尾完成状态。3.1–3.3 及 3.6 子链提取引理、证明不改；其他章节、Lean 证明、依赖与审计文件不改。

## 1. 数学推导

固定集合 A，设 \(d=\Delta(A)>0\)。已证 Erdős 截断和的上界保证 \(0<d\le1\)。在同一个既有概率空间上，令

\[
Y_x=Z_A(x)/\log\log x\quad(x\ge e^e),\qquad g(x)=\mathbb E Y_x.
\]

Stage 3–4 给出 \(\limsup_{x\to\infty}g(x)=d\) 及 \(\sup_{x\ge e^e}\mathbb E Y_x^2\le C_*\)。由有限实数上极限的最终上界与任意远处的近似下界，递归选取 \(x_j\ge e^e\)、\(x_{j+1}>x_j+1\)，使 \(|g(x_j)-d|\le1/(j+1)\)。因此 \(x_j\to\infty\)、\(\mathbb E Y_{x_j}\to d\)，且全部项都满足二阶矩界。没有假设期望函数连续。

对全部 \(x\ge e^e\)，

\[
\mathbb E[Y_x\mathbf1_{Y_x>M}]\le\mathbb E Y_x^2/M\le C_*/M\quad(M>0).
\]

这是统一可积性所需的一致积分尾界，特别适用于 \(Y_j=Y_{x_j}\)。它不意味着存在一个逐点支配全体变量的可积函数。

令 \(F=\limsup_jY_j\in[0,\infty]\)。F 是可数上确界、下确界的组合，故可测。对固定有限高度 M，设 \(Y_j^{(M)}=\min(Y_j,M)\)，对非负变量 \(M-Y_j^{(M)}\) 应用通常 Fatou 引理：

\[
\mathbb E\limsup_jY_j^{(M)}\ge\limsup_j\mathbb E Y_j^{(M)}.
\]

由于 \(0\le\mathbb E Y_j-\mathbb E Y_j^{(M)}\le C_*/M\)，以及

\[
\limsup_j\min(Y_j,M)=\min(F,M),
\]

得到 \(\mathbb E\min(F,M)\ge d-C_*/M\)。正文解释了截断如何与尾部上确界及其下降极限交换，也单独说明 F=∞ 时两侧都为 M。再沿整数高度 M↑∞ 用单调收敛，得到

\[
\boxed{\mathbb E F\ge d}.
\]

此处期望是扩展非负积分，不要求 F 可积或几乎处处有限。所有减法只发生在有限高度截断或假定 F<d 的反证分支中，没有 ∞−∞。

为取得达到 d 本身的样本，反设所有 ω 均满足 F(ω)<d。则 D(ω)=d−F(ω)>0，集合 \(\{D\ge1/r\}\) 的可数并覆盖全空间，总质量为 1，故至少一个集合有正概率。这迫使 \(\mathbb E D>0\)，从而 \(\mathbb E F=d-\mathbb E D<d\)，矛盾。故存在固定 ω₀ 满足 F(ω₀)≥d。该反证也处理了 \(\mathbb E F=\infty\)：反设会强迫该期望有限。

设 \(m_i=X_i(\omega_0)\)。它从一开始就是同一个无限路径空间中一个样本的全部坐标，故保持无限、严格递增与相邻整除。由 \(x_j\to\infty\)，任意全尺度尾部包含该序列的一个尾部，得到

\[
\boxed{\limsup_{x\to\infty}
\frac{\#\{i:m_i\in A,\ m_i\le x\}}{\log\log x}
\ge\limsup_jY_{x_j}(\omega_0)\ge\Delta(A)}.
\]

量词为“每个符合条件的 A，存在一个样本 ω₀，对所有后续尺度使用同一条路径”；没有声称同一条路径同时适用于所有集合 A。只对可数序列的上极限积分；全体实数尺度的比较在固定 ω₀ 后完成，因此无须断言不可数上确界作为随机变量可测。

结合原有 3.6 的无限子链提取引理，本章数学证明主线闭合。主文件摘要、第一章阶段说明及第五章网络尚未更新；它们属于后续工作，不能把本章完成等同于整篇已定稿。

## 2. Prim 实际采用的分析步骤

固定源码：Prim `a303f6bd23bb8f29a833d1d70327528359180995`，`LeanMarathon/Main.lean`。以下是显式调用阅读，不是新的 elaboration 依赖图或机器验证。

`mangoldt_adjoint_hit_count_moment_bridge_from_first_second` 先把一、二点概率级数接到真实归一化计数变量的积分。用 \(y\le y^2+1\) 证明期望最终有界、非负性证明相应下界条件，再调用 `exists_seq_tendsto_limsup`；丢弃有限前缀，使所有尺度分母为正且二阶矩受控。**其证明体确实构造期望收敛的尺度序列，但导出接口只记录期望的上极限等于密度**；正文没有把更强性质误标为接口字段。

`mangoldt_adjoint_reverse_fatou_bridge_from_uniform_integrability` 的证明体没有构造命名为 UniformIntegrable 的独立结论。它逐点证明

\[
y\le\min(y,R)+y^2/R\quad(y\ge0,R>0),
\]

并在 `ENNReal` 中积分，以二阶矩把尾项控制为 C/R。截断高度取 R=N+1。接口只有 `AEMeasurable`，因此它对每个截断取 `AEMeasurable.mk` 可测代表，再用 `ae_all_iff` 把可数多个几乎处处相等的条件放到同一个满测度集合上。

随后调用 mathlib 的 [`MeasureTheory.limsup_lintegral_le`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean#L27)。已阅读锁定版本：条件是各函数可测、被同一个函数几乎处处支配、支配函数的非负积分有限；此处支配函数就是常数 R，概率质量为 1 保证积分为 R<∞。该库定理的证明使用尾部上确界和有限积分条件下的下降极限，并非正文所写的“对 M−截断变量应用通常 Fatou”这一逐行实现。

Prim 把截断上极限的积分直接估计为不超过 \(\int F\)，再用 C/(N+1)→0 与 `ENNReal.le_of_forall_pos_le_add` 消去误差。**它不需要显式调用正文的 min 与 limsup 交换等式或单调收敛步骤**。两者结论及作用相同，不能据此宣称逐行对应。

为了从实数的一阶矩接口回到 ENNReal，源码另证明各一阶积分有统一有限上界，调用 `ENNReal.ofReal_limsup_toReal`。随后分 \(\int F=\infty\) 与有限两种情况：无限分支用点态上界反证；有限分支调用 `MeasureTheory.exists_lintegral_le` 选样本。最后以 `Tendsto.limsup_comp_le_limsup` 从尺度子序列转回实数尺度。这些有限性与值域转换条件不能因省略 `toReal` 记号而被忽略。

## 3. 声明与依赖关系

| 固定源码入口 | 实际调用与数学职责 |
| --- | --- |
| [`mangoldt_adjoint_hit_count_moment_bridge_from_first_second`，L13677](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L13677) | 读取概率质量、逐路径链、坐标可测、一阶矩接口、二阶矩接口；调用一阶积分桥接（L13367）、二阶积分桥接（L13466）、归一化计数可测性（L13341）、访问指标有限性及 `exists_seq_tendsto_limsup`，输出可用的尺度序列和统一二阶积分界。 |
| [`mangoldt_adjoint_reverse_fatou_bridge_from_uniform_integrability`，L13831](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L13831) | 本轮实质性的截断、尾项控制、反向 Fatou、扩展上极限积分与样本选择证明所在；具体细节见上一节，而不是仅靠名称宣称统一可积性。 |
| [`mangoldt_adjoint_second_moment_bound_from_constructed_path_data`，L14149](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14149) | 组合 `mangoldt_adjoint_two_point_divisor_bound_from_constructed_path_data`（L10913）与 `mangoldt_adjoint_second_moment_bound_from_two_point_divisor_bound`（L12870），把 Stage 4 的结果提供给矩桥接。 |
| [`mangoldt_adjoint_reverse_fatou_extraction_principle_from_constructed_path_data`，L14182](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14182) | 调用 `mangoldt_adjoint_normalized_hit_expectation_limsup_from_visit_identity`（L12941）取得一阶矩；再调用矩桥接与反向 Fatou 桥接。第二矩是明确传入的假设，并非随机模型定义自动产生。 |
| [`mangoldt_adjoint_constructed_path_data_from_kernel_path_data`，L14217](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14217) | 保留概率质量、逐样本链、坐标可测，并调用访问恒等式（L10232）；把 Stage 2–3 的核路径数据转为构造阶段数据。 |
| [`mangoldt_adjoint_constructed_path_data_exists`，L14246](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14246) | 调用 `mangoldt_adjoint_kernel_path_data_exists`（L9900）和上一转换，提供同一个概率空间及整个无限过程。 |
| [`mangoldt_adjoint_random_model_from_constructed_path_data`，L14276](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14276) | 纯合取包装：将构造数据、已证明的第二矩和已证明的提取原则组成随机模型；本身不再证明 Fatou 或矩界。 |
| [`mangoldt_adjoint_reverse_fatou_extraction_principle_from_model`，L14302](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14302) | 只投影模型的最后一个字段 `hmodel.2.2.2.2.2`，不应将它误认作分析证明的来源。 |
| [`mangoldt_adjoint_random_model_exists`，L14328](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14328) | 先取构造数据，再调用第二矩定理及从构造数据出发的 Fatou 提取原则，最后包装成模型。由此可见模型中提取字段的来源，避免从包装接口循环解释路径存在性。 |
| [`mangoldt_adjoint_reverse_fatou_path_extraction`，L14366](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14366) | 投影提取原则取得样本 ω；取 `path ω`，同时使用模型对同一个 ω 给出的链性质。输出的确定性链不随尺度改变。 |
| [`mangoldt_adjoint_chain_density_selection`，L14397](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14397) | 调用模型存在定理并应用前一提取定理，得到正 Mangoldt 加权密度集合的环境链。 |
| [`probabilistic_dense_ambient_chain`，L14423](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L14423) | 调用 `mangoldt_weight_aggregate_comparison`（L7962）把 Mangoldt 密度换回 Erdős 双对数密度，再调用链选择定理，得到本章环境链不等式。 |

相关类型边界：`mangoldt_adjoint_hit_count_moment_bridge`（L13131）对正 Mangoldt 密度集合提供尺度、几乎处处有限的访问指标、AEMeasurable 归一化变量、实数化积分的上极限及统一二阶非负积分界；`mangoldt_adjoint_reverse_fatou_extraction_principle`（L8036）已经是一个样本的存在命题；`upper_chain_hit_density`（L6889）使用 **ENNReal 上极限**，`chain_hits_density_at_least`（L6902）把目标实数密度用 `ofReal` 嵌入比较。不能把路径的扩展上极限改用无界时总化的实数上极限。

## 4. 适用条件、补充修订和待审查项

- 所有随机变量都基于同一个概率空间；本章更早已限制到逐样本满足链性质的满测度子空间，所以最终选出的样本自动具有无限链性质。源码对可测代表的可数例外集合另作统一处理，不能在每个 j 上各自选择样本。
- 统一可积性使用非负性、可积性及统一二阶矩；有界截断反向 Fatou 使用有限高度和有限总质量；去截断使用单调收敛，允许结果无穷。不存在未经控制的期望与上极限直接交换。
- 存在达到精确下界的样本靠概率质量为 1 与严格间隙的可数覆盖证明，不能仅由逐尺度存在样本或趋近 d 的样本序列代替。
- 全尺度路径密度允许 +∞；有限的是目标密度 d，而不是已证明的每条路径上极限。
- Stage 4 小修订明确 ψ(t)=∑_{p^r≤t}log p；m<p^r≤2m 时，中心二项式系数估值的对应项为 1−2·0=1，满足审查所要求的自洽说明。未重写其他算术估计。
- Stage 5 所要求的数学链条已完成。本轮未进行 Stage 6 的全章量词、边界与 Chebyshev/Mertens 替代推导专项复审，也未进行 Stage 7 的第五章完整依赖网络整理。主文件摘要和其他章节的旧阶段文字仍待后续统一更新。

本轮的检查限于数学推导核对、固定源码阅读及静态文本检查。没有运行或安装 Lean、没有重跑审计、没有编译 LaTeX 或生成 PDF；阅读源码与新增中文证明均不构成新的机器验证。发布文件仅为第三章源文件及本交接说明，不含下载的库文件或原始工具输出。
