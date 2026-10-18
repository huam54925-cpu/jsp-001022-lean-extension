# LPBridge：合法机队到有理数弱对偶的衔接

后续进展参见 [Case1 内核闭合记录](CASE1_KERNEL_CLOSURE_STATUS.md)。下文保留本阶段当时的结果与未完成项。

日期：2026-10-18。源码：[LPBridge.lean](../LeanCompletion/UAV/LPBridge.lean)。

本模块将合法有限机队生成的自然数边流转换为有理数 LP 变量，并实际调用已有的 `UAVProof.finite_weak_duality`。入口定理是 `UAVProof.LPBridge.legalFleet_weak_duality`。本轮不代入 Case1 的数值证书，不核验四机见证，不提交或上传。

## 定义与索引约定

所有新定义位于 `UAVProof.LPBridge` 命名空间。

| 定义 | 含义 |
| --- | --- |
| `arcSet` | 在有限顶点对类型 `V × V` 中筛选 `i ≠ j`；传给弱对偶的变量集合就是这个非自环集合。 |
| `flow x e` | 将自然数边流 `x(e.1,e.2)` 精确嵌入有理数。 |
| `capacity b e` | 两端节点度的最小值，以有理数表示。 |
| `eqMatrix` | 行类型为 `V ⊕ V`；`Sum.inl i` 选择起点为 `i` 的弧，`Sum.inr i` 选择终点为 `i` 的弧。矩阵值为 0 或 1。 |
| `rhs b` | 出度行和入度行均使用同一个节点度 `b(i)` 的有理数值。 |
| `cutMatrix S` | 选择起点在 `S`、终点不在 `S` 的弧，方向与 `outCutFlow` 相同。 |
| `ValidCut depot required S` | 基地不在 `S` 中，且 `S` 内至少有一个规定访问次数为正的节点；这一见证同时保证集合非空。 |
| `routeCost` | 对每架选中的无人机、每条有向边，按边在实际路线中的出现次数乘以有理数边成本，再求和。 |
| `certifiedBound` | 由规定度、等式对偶系数、割对偶系数以及变量上界的负剩余成本修正构成的精确有理数表达式。 |

无人机编号仍由 `ks : Finset ι` 索引，因此相同路线不会去重。割由 `cs : Finset κ` 和 `cuts : κ → Finset V` 索引，相同顶点集合若使用不同割编号，也会按其编号分别计入。

变量的承载类型采用 `V × V`，但只对 `arcSet` 中的变量求和。这是 `finite_weak_duality` 的有限变量集合接口，不会把自环当成 LP 变量。

## 已覆盖的九个证明

| 定理 | 证明作用 |
| --- | --- |
| `sum_arcSet_eq_univ` | 对角贡献为零时，删去自环不改变有限求和。 |
| `eqMatrix_out_sum` | 出度矩阵行的有理数和等于原自然数总出流的转换值。 |
| `eqMatrix_in_sum` | 入度矩阵行的有理数和等于原自然数总入流的转换值。 |
| `cutMatrix_sum` | 出割矩阵行的有理数和等于 `outCutFlow` 的转换值。自环不可能跨割，此等式不额外要求无自环。 |
| `legalFleet_variable_bounds` | 从已证明的自然数边流容量定理推出 `0 ≤ flow(e) ≤ capacity(e)`。 |
| `legalFleet_degree_rows` | 从实际巡检覆盖、总度和无自环定理推出全部出度、入度矩阵等式。 |
| `legalFleet_cut_row` | 从合法割内的正需求见证、实际覆盖以及 `Connectivity.lean` 的连通性割定理，推出有理数割下界 1。 |
| `objective_eq_routeCost` | 非自环 LP 目标函数等于各条实际路线按边出现次数计费的成本之和。 |
| `legalFleet_weak_duality` | 将以上证明分别作为 `hx`、`hxu`、`heq`、`hcut` 传入 `finite_weak_duality`，再把目标值改写成 `routeCost`。 |

## 入口定理的前提与结论

入口要求：有限顶点类型；有限编号集合中的合法路线；每个非基地节点的实际总巡检次数恰好等于规定需求；每个选中割满足 `ValidCut`；每个选中割的对偶乘子 `z(k) ≤ 0`。边成本和等式对偶乘子都是任意有理数。

它不假设边流度等式、边流容量或割不等式。上述约束全部由路线合法性和实际覆盖条件导出。割合法性与乘子符号是输入数据必须满足的条件，不是预先假设 LP 可行性。

记 `b(i)` 为基地处的 `ks.card`，或非基地处的规定需求。则：

```text
q(e) = cost(e) - Σ_h y(h) A(h,e) + Σ_k z(k) C(k,e)

certifiedBound = Σ_h y(h)b(h) - Σ_k z(k)
                 + Σ_e capacity(e) min(0, q(e))

certifiedBound ≤ routeCost.
```

求和中的弧属于 `arcSet`，行属于 `V ⊕ V`，割编号属于 `cs`。结论适用于任意有限机队，包括用 `Fin m` 表示的机队。

## 验证方式

本轮最终结果：

| 检查 | 实际结果 |
| --- | --- |
| `Connectivity.lean`、`WeakDuality.lean` 导入产物生成 | 均为退出码 0，无警告。 |
| 最终 `LPBridge.lean` 编译 | 退出码 0，无警告；日志为 `lp-bridge-compile-02.log`。 |
| 完整审计文件编译 | 退出码 0，无警告；日志为 `lp-bridge-audit-03.log`。 |
| 九个定理的公理依赖 | 均仅为 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或额外自定义公理。 |
| 15 个检查例子及覆盖条件证明 | 均通过；包含非对称矩阵方向、非自环变量集、负剩余成本修正、基地需求参数被忽略和无效割反例。 |

两节点例子的对偶下界表达式值为 9，实际路线成本为 10；已通过 `legalFleet_weak_duality` 推出下界，再以精确计算改写得到 `9 ≤ routeCost`，并非只计算数值不等式。此前开发日志中的类型转换、测试类型标注和缩进错误均已修正，不能将早期失败日志当作最终结果。

使用原工程的 Lean `4.30.0-rc2` 和既有 Mathlib 缓存，未修改工具链或依赖。五个已验证模块按文件哈希核对保持不变。本轮为导入新模块重新生成了 `Connectivity.olean` 和 `WeakDuality.olean`，没有重新编译 Mathlib。

在已准备好前序模块导入产物的工程根目录执行：

```powershell
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/Connectivity.olean LeanCompletion/UAV/Connectivity.lean
if ($LASTEXITCODE -ne 0) { throw 'Connectivity import build failed' }
lake env lean -o .lake/build/lib/lean/LeanCompletion/UAV/WeakDuality.olean LeanCompletion/UAV/WeakDuality.lean
if ($LASTEXITCODE -ne 0) { throw 'WeakDuality import build failed' }
lake env lean LeanCompletion/UAV/LPBridge.lean
if ($LASTEXITCODE -ne 0) { throw 'LPBridge compilation failed' }
```

实际编译日志、审计源码、边界例子和退出码记录保存在本地忽略目录 `verification/runs/lp-bridge-20261018-141656/`。日志和生成产物不进入提交。审计源码在完整最终模块后追加上述九个定理的 `#print axioms`，并包含一个两节点、两架相同路线的测试：出入度方向分开，非对称成本为 2 和 3，对角成本为 99，等式乘子非零，割乘子为 -1，两个弧的剩余成本均为负。

## 剩余问题与边界

1. **Case1 数据索引**：尚未将 53 个节点、106 个等式系数、2756 条非自环弧与此处的抽象顶点、`Sum.inl`/`Sum.inr` 行及弧集合逐项对应。
2. **32 个具体割**：本模块处理任意有效割族；尚未导入并逐个核对证书割的成员、非空性、基地排除和正需求见证。
3. **成本和单位**：`cost` 是抽象有理数，尚未证明与 Python 验证器的坐标、缩放单位、距离取整下界完全一致；不能将当前 `routeCost` 自动解释为真实欧氏飞行距离。
4. **数值表达式**：本轮未复跑既有 Python 证书，也未在 Lean 中证明具体系数计算出 `1158.3991045 km`。`certifiedBound` 是已定义且有通用正确性证明的表达式，不是已实例化的 Case1 数值常量。
5. **预算矛盾**：尚未把速度、服务时间、工作时限和三机的 1155 公里预算连接到当前成本不等式。
6. **机队模型**：每条参与路线仍要求非空，实际访问次数要求恰好满足需求；要排除至多三架实际工作的情况，仍需处理少于三条非空路线及原模型的准确覆盖约定。
7. **可行性见证**：四机路线的独立复核不属于本轮，尚未在本轮执行。

本轮完成的是合法机队到有理数 LP 弱对偶的通用结构性衔接，不能表述为 Case1 的最终数值不可行性定理已经在 Lean 内核中闭合。
