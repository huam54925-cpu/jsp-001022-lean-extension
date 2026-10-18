# Case1 固定实例绑定：证明覆盖与验收

后续进展：具体证书数值及至多三机排除已在 [Case1 内核闭合记录](CASE1_KERNEL_CLOSURE_STATUS.md) 中补齐。下文保留本阶段当时的结果与未完成项，不代表最新总体状态。

日期：2026-10-18。源码：[Case1Data.lean](../LeanCompletion/UAV/Case1Data.lean)。

本轮将既有 Case1 输入绑定到 `UAVProof.LPBridge`，并完成固定三机参数下的弱对偶调用。入口是 `UAVProof.Case1Data.three_routes_weak_duality`。结果仍是含具体系数的有理数表达式不等式，没有在本轮求出该表达式的数值，也没有证明最终三机不可行或四机可行。

## 输入身份与索引

输入为本地既有 `LeanCompletion/UAV/certificates/instances.json` 与 `bound_Case1.json`；本轮未重新运行求解器或精确下界验证器。

- Case1 规范化实例 SHA256：`8edfbad732afb3501d0e2616946475be39d5f5540d335d215e829a66dd8b1ac8`，与证书的 `instance_sha256` 一致。
- `instances.json` 文件 SHA256：`f9b2286f61c3878629ae3f2ba1f3764133c5b8051e884a97fecb22110c7904c7`。
- `bound_Case1.json` 文件 SHA256：`d2edb19ba8e1f741c4af05a4636798520a25b219580c0102621946d2d3dd849a`。
- 对照的 `verify_bound_certificate.py` SHA256：`1b6fba7b2efff776ea6ec3bc7544fcad9411285df8c2acf19ed8b538659f11ef`。

`Node = Fin 53`，基地为 0，巡检点为 1–52；JSON 点顺序与 `id` 逐项核对。基地坐标按原验证器取 `(0,0)`，其余 52 个坐标均为整数。`required 0 = 0` 仅表示没有基地巡检任务；基地的 LP 度由三机机队覆盖为 3，其余点使用实际需求，巡检需求合计 72。

`rowEquiv : Node ⊕ Node ≃ Fin 106` 为双射。`Sum.inl i` 对应 JSON `eq_dual[i]`，`Sum.inr i` 对应 `eq_dual[53+i]`。这是原验证器剩余成本 `cost - y[i] - y[n+j]` 的出度／入度顺序。

`CutIndex = Fin 32`，保留所有割的原编号，包括乘子为零的割；每个割内的成员集合与 JSON 一致。`Vehicle = Fin 3`，参与机队为 `Finset.univ`，每条路线仍要求任务非空。

## 固定成本与证明边界

Lean 将原整数坐标差的平方和定义为 `squaredDistance`。由于 `unit_km = 1/10`，百万分之一公里单位下的整数成本定义为：

```text
costUnits(i,j) = (Nat.sqrt (squaredDistance(i,j) * 10000000000) : ℚ).
```

先在整数中作差、平方、求和，再转自然数，避免负坐标差在平方前被截成零。该公式与原验证器的 `isqrt(floor(squared_scaled_distance))` 在本实例整数坐标下对应；有理数系数保持证书的整数或分数形式，不转为浮点数。`costUnits`、`eqDual`、`cutDual` 和 `certificateBoundUnits` 均使用百万分之一公里单位，不能直接把表达式当成公里值。

非自环弧与 Python 的双重循环使用相同的 `i ≠ j` 条件，Lean 证明其数量为 2756。成本核对定义公式并执行 `(0,1)`、`(1,0)` 两条方向相反的样例，均为 `80613274` 单位。附加运行时批量导出耗时较长，已中止，不计为本轮 PASS；全量成本运行时一致性及取整成本小于真实欧氏距离的形式化比较留待下一阶段。本轮不重新计算对偶证书求和。

## 17 个定理

以下名称均位于 `UAVProof.Case1Data`。

| 定理 | 结论 |
| --- | --- |
| `node_count`、`equality_row_count`、`cut_count` | 节点、等式行、割数量分别为 53、106、32。 |
| `row_out_index`、`row_in_index` | 等式行映射的数值索引分别为 `i` 和 `53+i`。 |
| `degreeDual_out`、`degreeDual_in` | LP 行乘子确实从对应的证书数组项读取。 |
| `arc_count` | `LPBridge.arcSet` 恰有 2756 条非自环弧，使用有限集计数定理证明。 |
| `inspection_count` | 非基地巡检需求总和为 72，基地巡检需求为零。 |
| `required_positive` | 全部非基地节点的需求为正。 |
| `cuts_exclude_depot` | 32 个割逐个不含基地。 |
| `cut_witness_mem`、`cut_witness_positive` | 每个割都有一个属于该割且需求为正的具体节点。 |
| `cuts_valid` | 每个具体割满足 `LPBridge.ValidCut`。 |
| `cutDual_nonpos` | 全部割乘子非正。 |
| `prescribedDegree_depot` | 本实例基地规定度为 3。 |
| `three_routes_weak_duality` | 三条合法路线精确覆盖规定需求时，`certificateBoundUnits ≤ routeCost ... costUnits`。 |

入口定理只要求三条合法路线及非基地节点的精确巡检覆盖。割合法性和乘子符号在模块中证明后传入 `legalFleet_weak_duality`；度、容量和割流量约束仍由前序模块推导，没有重新假设。

## 验证与复现

使用原工程的 Lean `4.30.0-rc2` 和既有 Mathlib 缓存，六个前序证明模块、工具链及依赖配置保持不变。数据导入脚本是 `LeanCompletion/UAV/certificates/bind_case1_data.py`（本地辅助脚本，未随证明源码发布），只生成或核对有标记的字面量区，不修改证明区，也不调用优化器或计算完整证书下界。

Lean 内核检查的是模块中固定的字面量及其定理。JSON 到这些字面量的对应由 Python 精确解析及生成区逐字核对完成；该外部对应不是 Lean 内核中的 JSON 解析证明。小规模 `#eval` 仅用于成本样例检查，不提供定理证明。批量求值导出没有完成，也没有纳入验收依据。

在原工程根目录、已有前序导入产物时执行：

```powershell
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/LPBridge.olean LeanCompletion/UAV/LPBridge.lean
if ($LASTEXITCODE -ne 0) { throw 'LPBridge import compilation failed' }
py -3 LeanCompletion/UAV/certificates/bind_case1_data.py --check
if ($LASTEXITCODE -ne 0) { throw 'Case1 literal binding failed' }
lake env lean LeanCompletion/UAV/Case1Data.lean
if ($LASTEXITCODE -ne 0) { throw 'Case1Data compilation failed' }
```

最终公理审计导入本轮由最终源码编译生成的 `Case1Data.olean`，对上述 17 个定理执行 `#print axioms`。原始日志、审计源码及数据导出只保存在本地忽略目录 `verification/runs/case1-data-20261018/`。这不是全新环境或 GitHub CI 重放。

| 检查 | 实际结果 |
| --- | --- |
| 最终源码编译 | `compile-02.log`：退出码 0，无警告。 |
| 同一源码生成导入产物 | `compile-03.log`：退出码 0，无警告。 |
| 17 个定理公理审计 | `axiom-audit-final.log`：退出码 0，仅依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，无 `sorryAx` 或自定义公理。 |
| 字面量与原 JSON 核对 | `literal-binding-final.log`：退出码 0；逐项覆盖坐标、需求、106 个精确系数、32 个割与乘子及割见证。 |
| 两条方向相反的成本样例 | `cost-probe.log` 与 `cost-sample-check.log`：退出码 0，Lean 与 Python 均得到 `80613274`。 |

没有使用 `sorry`、`admit`、`native_decide` 或额外 `axiom`。初次开发检查中的弧枚举递归限制、有理数符号化简问题已修复；附加导出尝试的失败或中止不应混同于上述最终编译与公理审计结果。

## 尚未完成

1. 尚未将 `certificateBoundUnits` 的具体有限求和证明为证书声明的 `2316798209/2`；既有 Python `Fraction` PASS 不自动成为 Lean 数值定理。
2. 尚未证明取整成本与真实欧氏距离的大小关系，或从百万分之一公里转到物理距离的完整比较链。
3. 尚未接入速度、服务时间、工作时限与 1155 公里预算。
4. 当前入口为恰好三条非空路线，不能直接排除至多三架的所有情况；少于三条非空路线及原模型是否要求精确访问仍须处理。
5. 尚未在本轮独立验证四机可行见证。

本轮停止于固定 Case1 三机参数的通用弱对偶实例化，等待审查。
