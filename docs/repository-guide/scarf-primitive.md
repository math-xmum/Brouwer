# ScarfPath 与 Primitive：从入口到调用

这两个接口沿用 formech 的组织方式：用命名空间表达对象上下文，内部使用短名；操作和性质放到对应对象下面，能推断的参数留给 Lean 推断。这里采用 Lean 常见的 `IsPrimitive`、`ReplacementStep` 等类型/谓词命名，不复制 formech 中所有历史拼写。

## 选择入口

```lean
import Gametheory.ScarfPath  -- 固定颜色的 room-door 图
-- 或者：
import Gametheory.Primitive -- primitive 集合、替换和轨迹，也导入图接口
```

| 要做什么 | 使用什么 |
| --- | --- |
| 构造固定颜色图 | `ScarfPath.graph c i`，顶点类型是 `ScarfPath.Cell T I` |
| 判断相关顶点、边或端点 | `ScarfPath.IsVertex`、`ScarfPath.Edge`、`ScarfPath.IsEndpoint` |
| 使用度数上界或端点分类 | `ScarfPath.degree_le_two`、`ScarfPath.isEndpoint_iff` |
| 使用分量的打包结论 | `ScarfPath.component_structure` |
| 在 `T ⊕ I` 中表示 goods 与 slack indices | `Primitive.ExtendedGoods T I`，分别用 `Sum.inl t` 和 `Sum.inr i` |
| 编码或还原一个 cell | `Primitive.toPrimitiveSet`、`Primitive.cell`、`Primitive.goods`、`Primitive.missingColors` |
| 判断 primitive 或 almost primitive | `Primitive.IsPrimitive`、`Primitive.IsAlmostPrimitive` |
| 表达替换、取得相应图上的 walk | `Primitive.ReplacementStep`、`Primitive.SplitStep`、`h.walk` |
| 取得从边界到 fully colored 集合的轨迹 | `Primitive.Trace.nonempty c i` |
| 只需要 fully colored 集合存在性 | `Primitive.exists_fullyColored c` |
| 使用可选的坐标模型 | `Primitive.Coordinate.exists_model`、`Primitive.Coordinate.IsPrimitive.erase_replacement` |

完整可编译用法在 [`Gametheory/Examples/ScarfPrimitive.lean`](../../Gametheory/Examples/ScarfPrimitive.lean)。默认 `lake build` 会检查它，包括不开启整个命名空间时的参数推断、proof dot notation，以及编码的 `simp` 化简。

## 最短的轨迹调用

以下示例的 `c` 和 `i` 显式给出；集合、索引类型从它们推断。`IST` 是与 `Scarf.lean` 共用的 indexed-order 实例，在存在多个候选实例时可用 `(IST := ...)` 指定。

```lean
import Gametheory.Primitive

variable {T I : Type*} [Fintype T] [Fintype I]
variable [DecidableEq T] [DecidableEq I] [Inhabited T]
variable [IST : IndexedLOrder I T]

example (c : T → I) (i : I) :
    ∃ X : Finset (Primitive.ExtendedGoods T I),
      Primitive.IsFullyColored (IST := IST) c X ∧
      (ScarfPath.graph (IST := IST) c i).Reachable
        (Primitive.cell (Primitive.slackBoundary i)) (Primitive.cell X) := by
  obtain ⟨trace⟩ := Primitive.Trace.nonempty (IST := IST) c i
  exact ⟨trace.terminal, trace.terminal_fullyColored, ⟨trace.walk⟩⟩
```

给定 `i : I` 后，`Trace.nonempty` 不再要求调用者额外提供 `[Inhabited I]`。不指定颜色的 `exists_fullyColored` 仍使用这个实例选择起始颜色。轨迹存在性返回 `Nonempty`；在证明中用 `obtain` 取得见证，再访问 `trace.terminal`、`trace.walk` 或 `trace.terminal_colorful_room`。

## 操作跟着对象走

- 对 `h : ScarfPath.Edge c i v w`，使用 `h.symm`、`h.left_vertex`、`h.right_vertex`。
- 对 `h : Primitive.IsPrimitive X`，使用 `h.isRoom` 取得对应 room。
- 对 `h : Primitive.IsAlmostPrimitive Y`，使用 `h.isDoor`。
- 对 `h : Primitive.ReplacementStep X X'`，使用 `h.symm`、`h.common_door`、`h.exists_face`。
- 对 `h : Primitive.SplitStep c i X Y X'`，使用 `h.replacementStep`、`h.edges`、`h.walk`。
- `simp` 可以直接证明 `Primitive.cell (Primitive.toPrimitiveSet σ C) = (σ, C)`，不需要 inhabited 类型或 indexed-order 实例。

上面的简写省略了可推断的隐式参数。需要对象的完整类型时，可在编辑器中使用 `#check Primitive.SplitStep.walk` 等命令。

## 定义的数学含义

来源是 Ivanov 的 *Beyond Sperner's Lemma*，特别是 §3 的 primitive/slack-vector 与路径构造；room/door 基础定义留在 `IndexedLOrder` 中。

`toPrimitiveSet σ C` 只是集合编码，不携带“这是 primitive”的证明。要从 room 得到该证明，使用 `isPrimitive_of_room` 或 `isPrimitive_toPrimitiveSet_iff_room`。`IsPrimitive` 是基于 dominance 的定义；`isRoomPrimitive_iff_isPrimitive` 连接 room 表述与 native 表述。`IsAlmostPrimitive` 通过 door 定义，`isAlmostPrimitive_iff_native` 连接它与“包含在 primitive 集合中的余维一面”的表述。

`ScarfPath.graph` 的环境顶点类型是所有 finset 对；不满足 `IsVertex` 的对是孤立点。通用图论接口位于 [`Gametheory/PathComponents.lean`](../../Gametheory/PathComponents.lean) 的 `PathComponents` 命名空间。`ComponentHasSpanningPath` 表示路径经过分量中的全部顶点，不断言它用尽该分量的所有边；`ComponentHasSpanningCycle` 同理。

`Trace` 包含从 slack boundary 到 terminal 的 graph walk。它没有额外记录每一步的 `SplitStep` 证书，也没有可执行的选点策略、无重复路径保证或复杂度界。`SplitStep.walk` 是从一个 split replacement 到长度为二的 walk 的方向性接口。

## 迁移旧代码

所有原先由这两个模块导出的声明都从 `IndexedLOrder` 移到新命名空间；没有新增旧名兼容层。完整映射见 [scarf-primitive-renames.md](scarf-primitive-renames.md)。普通 room/door 定义与 `IndexedLOrder.Scarf` 不变。

常见调用从 `IndexedLOrder.GiGraph` 改为 `ScarfPath.graph`，从 `IndexedLOrder.scarfAlgorithmTrace_exists` 改为 `Primitive.Trace.nonempty`。一般不必 `open` 两个命名空间；保留 `Primitive.` / `ScarfPath.` 前缀可以明确对象所属层。

`paper/cpp2027/main.tex` 和 `ARTIFACT.md` 使用当前接口名称。带日期的审计/修订报告保留当时的声明名称与行号，阅读旧报告时请结合迁移表，不要把历史构建记录当成本次验证。
