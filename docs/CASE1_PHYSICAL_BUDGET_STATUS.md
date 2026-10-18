# Case1 距离取整与工作时间预算

后续进展：具体证书数值及至多三机排除已在 [Case1 内核闭合记录](CASE1_KERNEL_CLOSURE_STATUS.md) 中补齐。下文保留本阶段当时的结果与未完成项，不代表最新总体状态。

日期：2026-10-18。本轮源码为 [Case1Distance.lean](../LeanCompletion/UAV/Case1Distance.lean)、[Case1Budget.lean](../LeanCompletion/UAV/Case1Budget.lean)，独立成本核对脚本为 `LeanCompletion/UAV/certificates/verify_case1_costs.py`（本地辅助脚本，未随证明源码发布）。

本轮连接具体有理数路线成本、真实坐标的欧氏距离及工作时间预算。没有重新计算对偶证书求和，没有运行优化器，也没有验证四机见证。具体证书数值仍是最终条件性定理的显式前提。

## 距离与单位

对任意自然数 `s`，`scaled_nat_sqrt_le_real` 比较整数平方根与实数平方根：

```text
(Nat.sqrt (s * 10^10) : ℝ) ≤ 100000 * Real.sqrt s.
```

证明使用整数平方根的平方不超过被开方数、实数平方根的平方等式，以及非负数的平方比较，不枚举 Case1 弧。

`coordinateDistanceSq` 直接由 Case1 整数坐标转换到实数后作差并平方求和；`squaredDistance_cast` 证明原自然数平方距离与此实数表达式相等。该步骤证明整数转自然数不会因负坐标差而丢失距离：作差后先平方、求和，结果非负，再转换。

`distanceKm` 定义为坐标距离的平方根除以 10。`costUnits_km_le_distance` 对所有节点对（包括对角项）给出：

```text
(costUnits(i,j) : ℝ) / 1000000 ≤ distanceKm(i,j).
```

`routeDistanceKm` 按每条有向边的实际经过次数累加欧氏距离；重复经过的边仍按次数计费。`routeCost_km_le_fleetDistance` 把逐弧比较提升到任意有限机队。`three_routes_certificate_le_distance` 再调用已有的固定三机弱对偶，得到尚未求值的证书表达式除以百万不超过实际机队距离。

## 工作时间与预算

`routeTimeHours r = routeDistanceKm r / 55 + r.visits.length / 12`，分别表示以 55 公里/小时飞行及每次巡检五分钟的工作时间。基地不计巡检服务时间。该模型未引入电池、风场或额外服务规则；若实际模型还有非负等待或额外航行时间，工作时间不超过九小时仍须满足这里的必要条件。

`fleet_inspection_count` 从路线列表和精确需求覆盖推出总巡检次数为 72，没有把总服务时长当作额外假设。因此总服务时间为六小时。`fleet_distance_budget` 从每条参与路线不超过九小时推出：

```text
fleetDistanceKm ≤ 55 * (9 * activeFleetSize - 6).
```

`at_most_three_distance_budget` 在参与路线数不超过三条时推出 `fleetDistanceKm ≤ 1155`；`three_routes_distance_budget` 是恰好三条非空合法路线的版本。这里“至多三条”的结论只涉及预算上界，不会自动把三机对偶证书应用到更小机队。

`case1_distance_budget_contradiction` 是独立的有理数算术引理：若 `2316798209 / 2 ≤ D` 且 `D ≤ 1155 * 1000000`，则矛盾，单位为百万分之一公里。

`three_routes_infeasible_of_certificate` 汇总路线覆盖、逐机工作时间约束、物理距离比较、弱对偶及数值矛盾。它仍显式要求：

```text
(2316798209 : ℚ) / 2 ≤ Case1Data.certificateBoundUnits.
```

该前提没有在本轮证明，没有声明为公理，也没有用 Python PASS 自动替代。其余距离上界和边流可行性由路线与工作时间条件推导，未直接假设。

## 全部 2756 条弧的独立成本核对

新脚本不导入绑定生成器、现有证书验证器或求解器。它固定并核对 `Case1Data.lean` 的 LF 标准化 SHA256 `cce161c618a2ae82df1b72850a27bf7f4cb7ba927a02c3ed7a87c094f2293f3d`，直接解析该已审计源码的坐标字面量；原 JSON 则按既有 Case1 指纹核对。

两条独立计算路径分别为：

1. 根据 Lean 坐标和已检查的定义公式，用整数二分搜索求 `floor(sqrt(s * 10^10))`。
2. 根据原 JSON 坐标和 `unit_km`，用 Python `Fraction` 与 `math.isqrt` 重现既有验证器的缩放公式。

全部非自环有向弧逐条比较，并检查 `c² ≤ scaledSquaredDistance < (c+1)²`、对称性和节点编号。另有零、精确平方及平方两侧的整数边界检查。

实际结果：`Independent Case1 arc-cost audit PASS`，退出码 0；2756 条弧全部通过，成本范围为 `1500000..175716390` 个百万分之一公里单位。脚本同时核对模型输入中的 55 公里/小时、五分钟服务、72 次巡检和九小时时限。

这是针对固定 Lean 公式和原 JSON 的独立离线核对，不是 Lean 运行时批量导出，也不是 Lean 内核中的 JSON 解析或 2756 个数值等式证明。此前批量运行时导出的中止记录不因此改标为 PASS；本轮新增的是独立 Python 检查。

## 验证与复现

使用原工程固定 Lean/Mathlib 版本及已有编译缓存，未修改先前七个 UAV 模块、原证明工程配置或依赖。编译和公理审计输出保存在本地忽略目录 `verification/runs/physical-budget-20261018/`。

| 检查 | 实际结果 |
| --- | --- |
| `Case1Distance.lean` 最终编译及导入产物生成 | 退出码 0，无警告，`distance-02.log`。 |
| `Case1Budget.lean` 编译及导入产物生成 | 退出码 0，无警告，`budget-01.log`。 |
| 全部 13 个新定理的公理审计 | 退出码 0，`axiom-audit.log`；六个距离定理、七个预算定理均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。 |
| 全部 2756 条弧的独立 Python 成本核对 | 退出码 0，`arc-cost-audit.log`。 |

没有 `sorry`、`admit`、`native_decide` 或自定义公理。实数定义按 Lean 的实数接口标记为 `noncomputable`，定理仍由内核检查。初次距离编译中的实数定义标记和代数化简递归限制已修复，早期失败日志不作为最终验收结果。本轮使用既有缓存，未进行全新环境或 GitHub CI 重放，也未提交或上传。

在已有 `Case1Data.olean` 及前序依赖的工程根目录执行：

```powershell
py -3 LeanCompletion/UAV/certificates/verify_case1_costs.py
if ($LASTEXITCODE -ne 0) { throw 'Case1 arc-cost audit failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Case1Distance.olean LeanCompletion/UAV/Case1Distance.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Distance compilation failed' }
lake env lean LeanCompletion/UAV/Case1Budget.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Budget compilation failed' }
```

脚本默认读取相邻的既有 `instances.json`；也可用 `--instances` 指定原始输入路径。原始 JSON、日志及生成物不进入提交。

## 仍未完成

- 具体证书数值下界在 Lean 内核中的证明，或一份明确标注外部精确计算依赖的最终混合证明报告。
- 把数值排除结论扩展到少于三条非空路线；本轮已覆盖这些机队的预算上界，但未提供对应的数值下界。
- 四机路线的独立可行性验证，以及最终最少四机的完整结论。
- 本轮未将通用路线合法性和精确访问覆盖替换成对原题所有其他运行规则的完整形式化。
