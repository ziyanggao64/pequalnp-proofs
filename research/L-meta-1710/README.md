# L-meta-1710：已验证的辅助结果

这组文件记录对公开任务 L-meta-1710 的研究进展。原任务要求一个与图、顶点数和度数均无关的常数，使围长至少为 5、每个非孤立顶点度数至少为 3 的图满足 `|E| ≤ c * (C.size + 1)`。

**原任务尚未证明。本分支保存辅助定理，不是对原任务完成或上游采纳的声明。**

## 1. 输入支持集与固定最大度数

`SupportBound.lean` 仅导入 `PEqualNP.Defs`，在命名空间 `PEqualNP.Outside.L_meta_1710.BoundedDegree` 中证明：

- `dependent_inputs_card_le`：任意扇入至多二的电路，其必要输入集合大小至多为门数加一。
- `nonisolated_card_le`：计算图边函数的电路，门数加一至少为图的非孤立顶点数。
- `monotone_bounded_degree_edges`：若所有顶点的度数至多为 `D`，则 `2 * G.edgeFinset.card ≤ D * (C.size + 1)`。

支持集结论实际上不要求门操作单调；最后一条将它专门应用于任务的 `Monotone2` 类。证明处理了不存在的线路读假、重复输入、零输入门等根模型细节。

这里的 `D` 是最大度数上界。原任务给的是非零度数的下界，不能用它替代 `D`，也不能从这条结果推出原任务要求的统一常数。

## 2. 剩余边与唯一载体

`CarrierBridge.lean` 仅导入 `PEqualNP.Defs`，在命名空间 `PEqualNP.Outside.L_meta_1710.CarrierBridge` 中证明：

- 正确的单调电路在每条图边的双点输入上都存在唯一的最早活跃 AND 载体。
- 在 `IsAO2` 模型中，如果该载体满足 `BelowF`，对应边必属于 `starEdges`。
- 因而，`Ustar` 中每条剩余边的唯一载体必属于 `junk`。
- `residual_card_le_sum_carried` 给出 `Ustar.card ≤ ∑ j ∈ junk, (carried j).card`。
- 不同载体的 `carried` 集合互不相交；对任意有限门集合，其承载边数之和不超过图的边数。

剩余边的归属桥只要求 `IsAO2` 和电路正确性，不需要围长、最小度、电路最小性或 `TopForm`。不重复计数的上界甚至不要求电路正确，因为 `Carries` 的定义已包含图邻接，而载体由最早索引唯一确定。

原任务仍缺少下面这类统一的总成本估计：

```text
∑ j ∈ junk, (carried j).card ≤ b * (C.size + 1)
```

证明某条边有唯一载体，没有限制一个载体可以承载多少条边。因此，以上结构和计数结果不能被当作该总成本估计。

## 3. 验证与复现

两份源码均已使用项目固定的 Lean 4.36.0 工具链普通编译通过；关键定理的公理审计只出现 `propext`、`Classical.choice`、`Quot.sound`。`validation/` 保存了实际审计输出和源码校验值。

没有对这些辅助文件运行项目原版完整检查器，也没有将其作为 L-meta-1710 的完成证明提交上游。

从该仓库根目录进入 `lean` 后，可复现普通编译：

```sh
lake env lean ../research/L-meta-1710/SupportBound.lean
lake env lean ../research/L-meta-1710/CarrierBridge.lean
```

环境沿用固定的 `lean-toolchain` 和 `lake-manifest.json`；不要更新 Mathlib 版本。Mathlib 固定提交为 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。

## 4. 来源

支持集计数改编自本项目 `MetaComplexity/Helpers/Support.lean`、`PermInputs.lean`。握手计数的短证明改编自固定 Mathlib 的 `Combinatorics/SimpleGraph/DegreeSum.lean`，保留了源码中的作者与 Apache 2.0 许可说明。

载体基础部分抽取并扩展了本项目 `Outside/L_meta_1603.lean`，补充了从干净载体到星形边、剩余边到复杂载体的论证和有限集计数。图、电路、`TopForm` 与载体均使用项目现有定义。
