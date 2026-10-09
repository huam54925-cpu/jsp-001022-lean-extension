# Stage 4：二阶矩与质因子数加权估计

基于 `5b461f08e7e9d3b762ad9e5ec7af80347fea88e7`，继续 `codex/jsp001022-exposition-stage1`。只替换 [第三章](../papers/jsp001022_exposition/sections/03-chain.tex) 的“二阶矩：待展开”小节，并新增本说明。3.1–3.3、反向 Fatou 待办、子链提取及其他章节均保留。

## 已完成的证明

令 \(E_j(x)=\{X_j\in A,X_j\le x\}\)。对 \(x\ge1\)，只有 \(j<\lfloor x\rfloor\) 的事件可能非空，且坐标可测使所有事件及交事件可测。因此平方展开与积分交换只是有限和运算。将有序对分为两个三角区域、重复计入对角线，得到

\[
\mathbb E[Z_A(x)^2]
=\sum_{i,j}\mathbb P(E_i(x)\cap E_j(x))
\le2\sum_j(j+1)\mathbb P(E_j(x)).
\]

这里使用交事件包含关系，不使用独立性。原始双点概率级数与真实随机变量的二阶矩之间的积分桥接也已在源码对应中单列，避免凭声明名称混同两者。

对正整数，`ArithmeticFunction.cardFactors n` 就是带重数的 \(\Omega(n)\)，其定义为 `n.primeFactorsList.length`；`cardFactors_one` 给出 \(\Omega(1)=0\)，`cardFactors_eq_sum_factorization` 给出素因子估值之和。已阅读锁定 mathlib 提交 `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 的 [ArithmeticFunction/Misc.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean)，没有安装库。不能用 `cardDistinctFactors`（不同素因子数）替代这里的函数。

严格整除 \(b=ac>a\ge1\) 给出 \(c\ge2\)，所以 \(\Omega(b)=\Omega(a)+\Omega(c)\ge\Omega(a)+1\)。沿链归纳有 \(j\le\Omega(X_j)\)。按终点状态拆分事件、应用 Stage 3 的访问恒等式，即得

\[
\boxed{\mathbb E[Z_A(x)^2]\le
2\sum_{n\in A,\,1\le n\le x}(\Omega(n)+1)\nu_\Lambda(n)}.
\]

端点 \(n=1\) 只可能在 \(j=0\) 被访问，系数 \(\Omega(1)+1=1\)；状态 0 被正整数截断排除。

## 算术估计的完整路线

Stage 3 的逐点误差给出

\[
\nu_\Lambda(n)\le M\nu_0(n)\quad(n\ge2),\qquad
M=1+C/\log2.
\]

这是**逐点乘法支配**，可以乘上非负的 \(\Omega(n)+1\)。我们没有从无权误差绝对可和推断加权误差仍可和。正权重使源码中的 `max (mangoldt_weight n) 0` 在所有正状态上等于权重本身。

记 \(H(N)=\sum_{2\le n\le N}1/(n\log n)\)、\(P(N)=\sum_{p\le N}1/p\)，以及 \(T(N)=\sum_{2\le n\le N}(\Omega(n)+1)/(n\log n)\)。由

\[
\Omega(n)=\sum_{p,r\ge1}\mathbf1_{p^r\mid n},\qquad
\Omega(n)+1\le2\Omega(n)\quad(n\ge2),
\]

展开素数幂因子，并对倍数 \(n=qm\) 使用

\[
\sum_{2\le n\le N,\ q\mid n}\nu_0(n)
\le\frac1q\left(\frac1{\log2}+H(N)\right).
\]

这里商 \(m=1\) 必须单独估计，不能用 \(\nu_0(1)=0\) 控制它。再由 \(\sum_{r\ge1}p^{-r}=1/(p-1)\le2/p\)，得到

\[
\boxed{T(N)\le4\left(\frac1{\log2}+H(N)\right)P(N)}.
\]

正文解释了两个因子的增长来源：

1. 递减函数积分比较给出 \(H(N)\le B+\log\log N\)，可取 \(B=1/(2\log2)+|\log\log2|\)。Prim 则通过对数增量和已有双对数主项界取得它。
2. 素数倒数估计沿 Prim 的数学路线展开：先由 \(\log(N!)=\sum_{q\le N}\Lambda(q)\lfloor N/q\rfloor\)、Chebyshev 界及阶乘对数界取得 \(Q(t):=\sum_{q\le t}\Lambda(q)/q=\log t+O(1)\)；对 \(Q\) 作分部求和得到 \(S(t):=\sum_{2\le q\le t}\Lambda(q)/(q\log q)=\log\log t+O(1)\)；最后
   \[
   0\le S(t)-P(t)=\sum_{p^r\le t,\ r\ge2}\frac1{r p^r}\le1
   \]
   给出 \(|P(t)-\log\log t|\le B_p\)。正文进一步以二项式系数和二进制尺度证明所需的粗 Chebyshev 界，以积分比较证明阶乘对数界，并解释分部求和下端 \(Q(2^-)=0\) 和可积误差。没有把素数倒数估计只写成一个未说明的最终渐近式。

令 \(x\ge e^e\)、\(L=\log\log x\ge1\)、\(N=\lfloor x\rfloor\)，并取

\[
B_0=1/\log2+B,\qquad
K_E=4(B_0+1)(B_p+1),\qquad C_*=2(1+MK_E).
\]

则 \(T(N)\le K_E L^2\)，而任意集合的 Mangoldt 加权终点和不超过 \(1+MT(N)\)。最终

\[
\boxed{\mathbb E[Z_A(x)^2]\le C_*(\log\log x)^2\quad(x\ge e^e)},
\qquad
\boxed{\sup_{x\ge e^e}\mathbb E[(Z_A(x)/\log\log x)^2]\le C_*}.
\]

本过程的 \(C_*\) 与阈值均可独立于 \(A\)。Prim 的终点和接口按 \(A\) 给出存在常数，但实际选取的算术常数在引入 \(A\) 之前确定；本过程的双点常数统一为 2。因此正文的统一选择不意味着修改了 Lean 的导出类型。

## Prim 声明及实际依赖

以下全部固定于 `a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean`。这是源码阅读所得的显式调用与数学职责，不是新的 Lean 编译或完整 elaborated 依赖图。

| 固定源码入口 | 数学职责与实际调用 |
| --- | --- |
| [`mangoldt_adjoint_pair_measure_tsum_le_index`，L10661](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10661) | 以 `MeasureTheory.measure_mono` 控制两个三角区域，使用 `ENNReal.tsum_comm`、`ENNReal.tsum_add` 和 `mangoldt_adjoint_ennreal_tsum_ite_le`（L10631）数出每列的 k+1 项。一般声明甚至不要求事件可测；本文为真实积分另由坐标可测性提供该条件。 |
| [`mangoldt_adjoint_card_factors_strict_of_dvd_lt`，L10544](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10544) | 把 b 写成 ac，调用 `ArithmeticFunction.cardFactors_mul`（两个因子非零）和 `cardFactors_pos_iff_one_lt`，证明严格整除使 Ω 严格增加。 |
| [`mangoldt_adjoint_index_le_card_factors_of_strict_chain`，L10573](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10573) | 对时间归纳，调用上一条并排除零状态，得到时间指标不超过 Ω。 |
| [`mangoldt_adjoint_weighted_hit_tsum_le_divisor_sum`，L10718](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10718) | 使用 `mangoldt_adjoint_positive_of_strict_chain`、坐标可测性拆分状态纤维；以指标界控制加权系数，交换非负级数，并用访问恒等式替换每个状态的总访问质量。 |

| [`mangoldt_adjoint_two_point_divisor_bound_from_constructed_path_data`，L10913](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10913) | 组合事件双和界与终点权重和界，明确选择常数 2。接口附带最终 log log x>0，故源码在 x>e 上导出；事件不等式本身不依赖此归一化条件。 |
| [`mangoldt_adjoint_mangoldt_positive_part_le_erdos_local`，L12629](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12629) | 直接调用 `mangoldt_weight_erdos_pointwise_error_bound`，用 log n≥log 2 选择 M=1+C/log 2；没有调用无权误差可和性来处理 Ω。 |
| [`mangoldt_adjoint_terminal_sum_le_one_add_erdos_local`，L12685](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12685) | 去掉 A 的限制；n≥2 使用逐点支配，n=1 单独计入一个单位质量。截断支撑有限，故可在实数 tsum 中比较。 |
| [`mangoldt_adjoint_card_factors_le_prime_power_divisor_count_local`，L11950](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11950) | 调用 `ArithmeticFunction.cardFactors_eq_sum_factorization`、`Nat.Prime.pow_dvd_iff_le_factorization`；扩大到 p≤N、1≤r≤N 的有限计数作为上界，正文用非零项有限的准确计数式。 |
| [`mangoldt_adjoint_erdos_weight_mul_le_local`，L12024](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12024) | 分别处理商 m=1 和 m≥2；后者以 log(qm)≥log m 比较正分母。 |
| [`mangoldt_adjoint_erdos_weight_multiples_sum_le_local`，L12085](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12085) | 用 `Finset.sum_bij'` 按 n=qm 重编号，调用上一条，再把商的范围扩大到 1≤m≤N。 |
| [`mangoldt_adjoint_prime_power_reciprocal_sum_le_prime_sum_local`，L12221](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12221) | 调用 `geom_sum_Ico_le_of_lt_one`，公比 1/p∈[0,1)，再用 1/(p−1)≤2/p。 |
| [`mangoldt_adjoint_card_factors_erdos_natural_product_bound_local`，L12317](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12317) | 以 `cardFactors_pos_iff_one_lt` 得 Ω+1≤2Ω，组合素数幂计数、倍数求和、几何级数界，取得系数 4 的乘积估计。 |
| [`mangoldt_adjoint_erdos_weight_natural_terminal_sum_bound_local`，L11913](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11913) | 调用 `mangoldt_adjoint_erdos_weight_le_log_increment_local`（L11870）与 `mangoldt_log_reciprocal_main_term_bound`（L11114），取得 H 的双对数上界；正文用积分比较承担同一职责。 |
| [`mertens_von_mangoldt_reciprocal`，L181](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L181) | 通过 `ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum`、`vonMangoldt_mul_zeta` 得阶乘因子和恒等式，再使用 `Chebyshev.psi_le_const_mul_self`、`Stirling.le_log_factorial_stirling` 和取整界。正文给出粗二项式系数界及阶乘积分界，没有声称逐行重现上述库证明。 |
| [`mangoldt_log_reciprocal_partial_summation_nat`，L11446](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11446) | 调用前一 Mertens 界、`mangoldt_log_reciprocal_main_term_bound`、`mangoldt_log_reciprocal_mertens_error_bound`（L11205）及自然截断恒等式（L11397）；误差界使用 `mangoldt_mertens_error_partial_bound`（L1537）和递减权重的分部求和。 |
| [`mangoldt_log_reciprocal_partial_summation`，L11611](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11611) | 以自然截断结论、`mangoldt_log_reciprocal_partial_sum_floor`（L11498）和 `mangoldt_log_reciprocal_floor_loglog_bound`（L11545）转成实数截断。正文用阶梯函数积分表达该计算。 |
| [`prime_reciprocal_mangoldt_log_bridge`，L11666](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11666) | 用 `ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`（模 1）取得非素数部分可和，以 1/log n≤1/log 2 支配，再调用 `summable_error_limsup_transfer_truncated_error_bound`。正文的高次素数幂几何级数直接给出所需有限常数。 |
| [`mertens_prime_reciprocal`，L11826](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11826) | 将对数加权 Mangoldt 和估计与前一桥接界相加，取得素数倒数和相对 log log t 的有界误差。 |
| [`mangoldt_adjoint_card_factors_erdos_real_terminal_sum_bound_local`，L12489](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12489) | 取 N=自然数下取整 x，调用乘积界、H 的上界与 `mertens_prime_reciprocal`；利用 log log N≤log log x，在 log log x≥1 时吸收常数。 |
| [`mangoldt_adjoint_card_factors_weighted_terminal_sum_bound`，L12817](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12817) | 依次调用 Mangoldt 正部逐点支配、`mangoldt_adjoint_terminal_sum_le_one_add_erdos_local` 及前一实数终点界；取常数 1+M K，吸收 n=1 的贡献。 |
| [`mangoldt_adjoint_second_moment_bound_from_two_point_divisor_bound`，L12870](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12870) | 将双点界常数与算术终点界常数相乘，保留归一化分母最终为正的条件。接口控制的是 `mangoldt_adjoint_hit_second_moment` 定义的 ENNReal 双点概率级数。 |
| [`mangoldt_adjoint_normalized_hit_second_integral_bound_from_chain`，L13466](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L13466) | 连接概率双和与归一化随机变量平方的非负积分：调用有限计数表示（L13269）、`mangoldt_adjoint_of_real_normalized_finset_count`、`mangoldt_adjoint_finset_indicator_sum_square`（L13213）、`lintegral_indicator_const`、有限和积分以及 `mangoldt_adjoint_log_normalization_second_moment_cancel`（L13236）。条件为逐路径链、坐标可测、常数非负和 log log x>0。 |

## 适用条件与尚未解决的问题

- 原过程从 1 出发，严格递增且整除，因此固定截断的时间支撑统一有限，平方可积。本文的普通实数期望与源码的有限 ENNReal 概率双和没有无穷值转换问题。
- Ω 的乘法可加性用于非零整数；素数幂指数从 1 开始。n=1 的单位贡献没有被误删，商为 1 的倍数项也没有被错误地写成零。
- 平方主界只在充分大的尺度陈述；正文给出可用阈值 x≥e^e，从而双对数至少为 1。没有在 x=1、e 等归一化奇异点使用除法估计。
- 算术层面的非负性使去掉 A 的限制合法。Cauchy–Schwarz、独立性假设及加权误差绝对可和性均不是本轮证明的输入。
- 本轮仅证明 L² 一致有界。统一可积性、反向 Fatou、极限随机变量与确定性路径选择仍留在 Stage 5；正文 3.5 原样保留。不能从当前二阶矩或一阶矩等式直接宣称已经找到所需路径。

没有发现本轮公式需要额外的集合密度假设：二阶矩上界对任意 A 成立。Chebyshev/Mertens 的正文证明与源码在若干技术步骤采用不同的标准估计，已逐项标明；没有新增或修改 Lean 证明来形式化这些替代写法。

本轮检查为数学推导核对、固定源码阅读和静态文本检查，包括修改范围、标签引用、LaTeX 环境、文档链接及原有小节不变性。未运行或安装 Lean，未编译 LaTeX，未生成 PDF；也没有重跑历史审计。下载的 mathlib 单文件源码及原始工具输出不进入提交。
