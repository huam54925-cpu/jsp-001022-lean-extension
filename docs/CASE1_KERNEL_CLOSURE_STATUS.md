# Case1：证书数值闭合与至多三机排除

日期：2026-10-18。本轮在既有固定实例、合法路线、弱对偶、距离比较和时间预算证明上，补齐具体证书的 Lean 数值证明，并将排除结论扩展到任意至多三条非空合法路线。

发布范围：本次提交包含完整的 UAV Lean 证明依赖及四份阶段说明。原始 JSON、Python 辅助脚本、运行日志、审计输出及编译缓存仍保留在本地；以下历史检查记录不表示上传阶段重新运行了验证。Lean 证明使用源码中的固定字面量，不需要本地 JSON 或 Python 脚本。

## 形式化结论

- [Case1Numerics.lean](../LeanCompletion/UAV/Case1Numerics.lean) 中的 `UAVProof.Case1Certificate.certificate_value` 证明 `certificateBoundUnits = (2316798209 : ℚ) / 2`。单位为百万分之一公里，对应 1158.3991045 公里。
- [Case1Infeasible.lean](../LeanCompletion/UAV/Case1Infeasible.lean) 中的 `UAVProof.Case1Infeasible.at_most_three_infeasible` 排除 0、1、2、3 条非空合法路线。
- 同一模块的 `feasible_fleet_card_ge_four` 证明满足精确巡检覆盖和逐机九小时时限的有限参与机队必有至少四架。还提供 `one_vehicle_infeasible`、`two_vehicles_infeasible`、`three_vehicles_infeasible` 三个直接入口。

最终入口只要求路线合法性、非基地节点的精确巡检覆盖，以及参与路线的 `routeTimeHours ≤ 9`。具体证书的数值不再是未证明的前提；度约束、容量约束和连通性割也没有作为新的前提加入。

## 证书数值如何进入内核

[Case1Certificate.lean](../LeanCompletion/UAV/Case1Certificate.lean) 先证明原 `LPBridge.certifiedBound` 与按起点分行的计算表达式相等，没有改变证书公式或对角弧排除规则。随后数值模块逐行检查全部 53 个起点的修正项：

| 项目 | 精确值（百万分之一公里） |
| --- | --- |
| 度约束项 | `2164145799 / 2` |
| 割乘子之和（公式中减去此项） | `-111948712` |
| 53 行容量乘剩余成本修正项之和 | `-35622507` |
| 完整证书 | `2316798209 / 2` |

各行仍使用既有 `costUnits` 的 `Nat.sqrt` 定义、既有坐标、需求、割集合及有理数乘子。见证数值由本地脚本准备，Lean 使用 `decide +kernel` 检查每个等式，再通过已证明的分解定理汇总。外部脚本不是证明的信任前提；没有使用 `native_decide`、`sorry`、`admit` 或自定义公理。

## 为什么也能排除一机、两机

[Case1Fleet.lean](../LeanCompletion/UAV/Case1Fleet.lean) 保留同一组对偶乘子，把基地度改为实际参与路线数 `n`。当 `n ≤ 3` 时，各弧容量不会增加，而剩余成本修正项非正，因此容量修正部分只会改善下界。基地两项对偶乘子之和经内核检查为 `43200918`。

因此同一证书给出下界（公里）：

```text
1158.3991045 + (n - 3) * 43.200918
```

既有时间预算则给出上界 `55 * (9 * n - 6)` 公里。两者比较如下；较小机队的下界是由三机证书推导的保守下界，不声称是重新优化的最强界。

| 参与路线数 | 距离下界（公里） | 距离预算上界（公里） |
| --- | --- | --- |
| 1 | 1071.9972685 | 165 |
| 2 | 1115.1981865 | 660 |
| 3 | 1158.3991045 | 1155 |

Lean 用统一的线性不等式证明矛盾，并覆盖零架情况；没有用空路线填充三架，也没有直接把三机基地度套在更小机队上。

## 本轮检查及复现

使用原工程固定的 Lean `4.30.0-rc2`、依赖版本及既有前序模块缓存。四个新增模块已分别编译生成导入产物，最终成功命令的退出码均为 0、无警告。原始日志和审计源码保留在忽略目录 `verification/runs/case1-kernel-20261018/`。

| 检查 | 本轮实际结果 |
| --- | --- |
| 求和分解模块 | `certificate-01.log`，退出码 0 |
| 完整数值模块 | `numerics-01.log`，退出码 0 |
| 任意较小机队的下界推导 | `fleet-03.log`，退出码 0 |
| 不带数值前提的最终排除入口 | `infeasible-01.log`，退出码 0 |
| 10 个关键定理及其传递依赖的公理审计 | `axiom-audit.log`，退出码 0；仅有 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或额外计算公理 |

从仓库源码构建完整 Case1 证明链可在工程根目录执行 `lake build LeanCompletion.UAV.Case1Infeasible`，由 Lake 构建导入依赖；这里给出复现命令，不声称本轮做过全新环境重放。默认的 `lake build` 入口仍是原 JSP-001022 工程。

本轮实际采用已有前序模块产物，在工程根目录执行：

```powershell
$modules = @('Case1Certificate', 'Case1Numerics', 'Case1Fleet', 'Case1Infeasible')
foreach ($module in $modules) {
    lake env lean -o ".lake/build/lib/lean/LeanCompletion/UAV/$module.olean" "LeanCompletion/UAV/$module.lean"
    if ($LASTEXITCODE -ne 0) { throw "$module compilation failed" }
}
```

数值模块的内核归约比结构性定理耗时和占用内存更多。本次实际成功的是完整逐行数值模块；随后启动的单行性能探针已停止，不作为额外验证结果。开发时的类型转换和化简错误日志也不计为成功检查。

上述证明开发阶段没有重新运行今天已通过的 Python 下界、成本或四机可行性验证，没有运行求解器，没有进行全新环境或 GitHub CI 重放，当时也没有提交或上传。其后的源码发布按用户单独的上传指令进行。

## 结论边界

Lean 现已证明固定源码实例、当前合法路线和物理时间模型下的 `N_min ≥ 4`。用户于 2026-10-18 提供的独立 Python 四机见证验证输出为 PASS、`FeasibleExitCode=0`，给出同一指定模型下的 `N_min ≤ 4`；本轮沿用该结果，未把它重新标为新运行。

两者结合支持指定模型下最少四架的混合验证结论。四机可行见证本身尚未形式化为 Lean 定理，因此不声称已有完整的 Lean 内核 `N_min = 4` 证明。JSON 与固定源码字面量的对应仍依赖此前的外部绑定检查；本轮没有修改 `Case1Data.lean`、原证书、工具链、依赖配置或冻结目标。
