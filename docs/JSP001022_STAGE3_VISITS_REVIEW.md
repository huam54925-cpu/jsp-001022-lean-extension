# Stage 3：访问概率恒等式、权重比较与一阶矩

沿用 `codex/jsp001022-exposition-stage1`，基于 Stage 2 提交 `37fd4834d7e64b79da5e24611fed3f9054da62c9`。本轮修改的论文源文件只有 [03-chain.tex](../papers/jsp001022_exposition/sections/03-chain.tex)，另新增本交接说明。其余章节、主文件、README、Lean 证明、依赖和审计文件均不改。旧摘要及 README 的阶段描述暂未同步，以遵守本轮范围。

## 完成的数学推导

### 访问质量

定义 \(v(n)=\sum_{k\ge0}\mathbb P(X_k=n)\)。由逐路径的严格递增和 \(X_0=1\)，有 \(X_k\ge k+1\)，故访问 \(n\) 只可能在 \(k<n\) 时发生。正文分别处理：

- \(n=0\)：不属于状态空间，访问事件为空；与源码的补充值 \(\nu_\Lambda(0)=0\) 一致。
- \(n=1\)：仅初始时刻被访问，所以 \(v(1)=1=\nu_\Lambda(1)\)。
- \(n\ge2\)：按前一状态分解成有限个不交事件，由相邻二坐标概率公式得到
  \[
  v(n)=\sum_{m=1}^{n-1}v(m)U(m,n).
  \]

对所有较小状态作强归纳，非对角伴随式消去权重分母，下降核的行归一化给出

\[
v(n)=\nu_\Lambda(n)\sum_{m=1}^{n-1}P_\downarrow(n,m)=\nu_\Lambda(n).
\]

这一证明只需要 Stage 2 导出的相邻二坐标恒等式，不需要从其接口名称推断更强的条件 Markov 性。换序在统一有限时间范围中完成。严格入流方程本身并不足以识别这个过程的实际访问质量。

### 逐点误差的来源

令 \(h(s)=1/\zeta(s)\)，写 \(\zeta(1+u)=u^{-1}+R(u)\)。Prim 的 `reciprocal_zeta_second_order_bound` 从右侧极点余项极限 \(R(u)\to\gamma\) 取得 \(|R(u)|\le B\)，再缩小邻域使 \(Bu\le1/2\)。于是

\[
\zeta(1+u)\ge(2u)^{-1},\qquad
|h(1+u)-u|=\frac{u|R(u)|}{\zeta(1+u)}\le2Bu^2.
\]

正文另明确指出，这里所需的“余项有界”本身可由已使用的级数积分比较直接证明：\(u^{-1}\le\zeta(1+u)\le1+u^{-1}\)，故 \(0\le R(u)\le1\)。因此正文不把 Laurent 展开作为未解释的黑箱，也不声称这种初等替代路径就是 Prim 的逐行实现。

局部控制还不足以直接估计整个积分。对 \(u>\delta\)，由 \(0<h(1+u)\le1\) 得

\[
|h(1+u)-u|\le1+u\le(\delta^{-2}+\delta^{-1})u^2.
\]

选 \(K=\max(2B,\delta^{-2}+\delta^{-1})\)，即可对全部 \(u>0\) 使用同一个二次控制。令 \(L=\log n>0\)，平移积分并减去 Erdős 权重的指数矩表示：

\[
\nu_\Lambda(n)-\nu_0(n)
=\frac Ln\int_0^\infty e^{-Lu}[h(1+u)-u]\,du.
\]

两个被减积分都绝对可积；用全局控制和 \(\int_0^\infty u^2e^{-Lu}du=2/L^3\)，得到

\[
|\nu_\Lambda(n)-\nu_0(n)|\le\frac{2K}{n(\log n)^2}\qquad(n\ge2).
\]

正文写出指数矩的换元、分部积分依据及可积性，不把积分相减或取绝对值的步骤略去。

### 误差可求和、密度与一阶矩

积分判别法给出 \(\sum_{n\ge2}1/[n(\log n)^2]<\infty\)。Prim 使用 Cauchy 凝聚判别法，凝聚后是 \(1/[k^2(\log2)^2]\) 的级数。计入 \(n=1\) 的误差 1，得到绝对常数

\[
D=\sum_{n\ge1}|\nu_\Lambda(n)-\nu_0(n)|<\infty.
\]

任意集合、任意实数截断都满足

\[
\left|\sum_{n\in A,n\le x}\nu_\Lambda(n)-W_A^{\le}(x)\right|\le D.
\]

除以 \(\log\log x\) 的操作只在 \(x>e\) 使用。差趋于零，故两种上密度一致。为与 Lean 的实数上极限对应，正文另以 \(W_A^{\le}(x)\le\log\log x+O(1)\) 核对最终有界性；没有将一般无界情形中的实数总化上极限当作扩展实数上极限。

对于 \(x\ge1\)，\(Z_A(x)\) 是至多 \(\lfloor x\rfloor\) 个可测指示函数之和，因而可积；\(x<1\) 时恒为零。有限和交换与访问恒等式给出

\[
\boxed{\mathbb E Z_A(x)=\sum_{n\in A,n\le x}\nu_\Lambda(n)
=W_A^{\le}(x)+O(1)},\qquad
\boxed{\limsup_{x\to\infty}\frac{\mathbb E Z_A(x)}{\log\log x}=\Delta(A)}.
\]

## 准确的源码对应与调用关系

以下链接均固定于 Prim `a303f6bd23bb8f29a833d1d70327528359180995`；对应的是源码声明、证明体及显式调用，未重新运行 Lean 或计算 elaboration 后的依赖闭包。

| 数学步骤 | 声明与调用职责 |
| --- | --- |
| 访问概率恒等式 | [`mangoldt_adjoint_visit_identity_from_kernel_path_data`，L10232](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L10232)：解包核与路径接口；`StrictMono.add_le_nat` 给出时间界，`Nat.strong_induction_on` 分状态归纳；`MeasureTheory.measure_biUnion_finset` 计算有限不交事件并的质量；`tsum_eq_sum` 和 `Finset.sum_comm` 化为有限和后换序；使用核包中的非对角公式、下降支撑及行和，并调用 `mangoldt_weight_positive` 消去分母。接口值域是 `ENNReal`，右侧是 `ENNReal.ofReal (mangoldt_weight n)`；正文的访问有限性保证可作普通实数概率之和解释。 |
| 局部倒数二阶误差 | [`reciprocal_zeta_second_order_bound`，L6984](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L6984)：直接使用 `ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right`，平移至 \(u\downarrow0\)，取实部；取 \(B=|\gamma|+1\)，再把邻域缩到 \(Bu\le1/2\)，完成上述代数估计。正文用积分比较替代取得有界余项这一步，其余倒数估计相同。 |
| 准确的误差积分 | [`mangoldt_weight_integral_change_of_variables`，L7447](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7447)：调用同前缀的 `mangoldt_laplace`、`erdos_laplace` 两个表示式，以及 `zeta_kernel_integrable`、`erdos_kernel_integrable` 两个可积性结论，再使用 `MeasureTheory.integral_sub`。 |
| 全局二次控制及积分误差 | [`mangoldt_weight_laplace_error_bound`，L7524](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7524)：调用局部二阶估计，以 `max C₀ (δ⁻¹ ^ 2 + δ⁻¹)` 延伸到整个正半轴；`mangoldt_weight_integral_change_of_variables_one_le_zeta_re` 控制尾区间；以 `ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul` 证明多项式乘指数可积，`Real.integral_rpow_mul_exp_neg_mul_Ioi` 和 `Real.Gamma_ofNat_eq_factorial` 计算二次指数矩，`MeasureTheory.norm_integral_le_of_norm_le` 控制误差积分。正文用两次分部积分计算同一指数矩。 |
| 逐点误差 | [`mangoldt_weight_erdos_pointwise_error_bound`，L7703](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7703)：由前两条声明重写并直接应用积分界，得到对所有 \(n\ge2\) 一致的存在常数。 |
| 控制级数与绝对可和 | [`log_square_tail_summable`，L6918](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L6918)：使用 `summable_condensed_iff_of_eventually_nonneg` 与 `Real.summable_one_div_nat_rpow`；[`mangoldt_weight_erdos_summable_error`，L7727](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7727) 再用逐点界及 `Summable.of_norm_bounded_eventually_nat` 比较，允许 0、1 这两个有限例外。 |
| 截断误差与密度转移 | [`summable_error_limsup_transfer_truncated_error_bound`，L7830](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7830) 以全体绝对误差和控制截断差；[`summable_error_limsup_transfer`，L7895](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7895) 除以发散的双对数，并调用 `summable_error_limsup_transfer_vanishing_perturbation`（L7752）；[`mangoldt_weight_aggregate_comparison`，L7962](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L7962) 将两个权重代入此一般转移结论。 |
| 时间访问质量等于状态权重和 | [`mangoldt_adjoint_normalized_hit_expectation_limsup_from_visit_identity`，L12941](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L12941)：假设 `mangoldt_adjoint_constructed_path_data`，从中读取概率测度、链、可测性与访问恒等式；按有限状态分解事件，使用 `ENNReal.tsum_comm` 换序，调用访问恒等式和权重正性，将有限扩展非负实数和转为实数截断和。证明体先取得逐点恒等式，声明最终导出归一化上极限等于 `mangoldt_weight_upper_density`；再与 L7962 组合得到 Erdős 密度。 |
| 真实积分与访问概率之和的桥接 | [`mangoldt_adjoint_normalized_hit_first_integral_from_chain`，L13367](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L13367)：要求逐样本链性质、各坐标可测及 \(\log\log x>0\)；使用 `mangoldt_adjoint_hit_index_count_finite_sum_from_chain`（L13269）与 `mangoldt_adjoint_of_real_normalized_finset_count`，继而以 `MeasureTheory.lintegral_indicator_const`、`MeasureTheory.lintegral_finset_sum'` 积分。源码范围取到自然数下取整再加一，正文使用从 1 出发得到的更紧有限范围；两者对本过程给出同一结果。该定理只涉及一阶矩，没有在本轮调用二阶矩结论。 |

注意：L12941 的名称含“expectation”，但其导出接口写的是一点评价概率级数的 `toReal`。上表特意补入 L13367，避免把一个命名当作已经提供真实随机变量积分等式的证据。在本概率空间中，截断访问次数有统一有限上界，故该级数与真实期望的等同没有无穷值转实数的问题。

## 标准定理的条件与审查边界

- 事件拆分与期望线性：坐标可测、离散状态空间中的集合可测；涉及状态与有效时间均有限。全过程不交换有正有负且未证可和的级数。
- Laplace 代换、积分相减及积分绝对值界：\(n\ge2\) 保证 \(L=\log n>0\)，有可积指数函数与多项式乘指数函数作控制。
- 级数积分判别法：控制函数在 \([2,\infty)\) 上非负递减，其反常积分有限。源码相应的凝聚法条件也是最终非负、递减。
- 上极限稳定性：归一化差的绝对值趋于零；正文另验证两者最终有界。\(x\le e\) 的分母行为不影响无穷远极限。
- 源码所用的 ζ 余项极限作为已定位的上游定理输入；本轮没有重新验证其 Lean 证明。正文的初等有界余项论证足以承担本节所需结论。

落实 Stage 2 两处修订：严格入流恒等式后再次明确“不变”不指包含吸收自环的平稳概率分布；限制到满测度集合时明确写出 \(\mathbb P(G)=1\) 和任意可测 \(B\) 的 \(\mathbb P(B\cap G)=\mathbb P(B)\)。随机核构造未重写。3.4 只更新待办措辞，避免把已证一阶矩继续标作未完成；没有增加二阶矩证明。

## 尚未解决的问题

本轮范围内的访问恒等式、逐点及聚合误差、一阶矩联系均已给出数学证明。尚未证明的是二阶矩控制、归一化访问变量的统一可积性、反向 Fatou，以及达到目标密度的同一条确定性路径。期望上极限的等式本身仍不足以得到这种路径。第五章的完整依赖网络与主文件的阶段描述留待后续统一更新。

本轮只进行了源码阅读和静态文本检查；未安装、运行 Lean，未编译 LaTeX，未生成 PDF。发布内容不含下载的依赖源码、原始工具输出或审计记录；本说明不能用作重新完成 Lean 验证的证据。
