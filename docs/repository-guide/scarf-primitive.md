# ScarfPath and Primitive: Entry Points and Usage

Namespaces express object context, names inside them remain short, operations and properties live under the corresponding objects, and Lean infers parameters where possible. Types and predicates use conventional Lean names such as `IsPrimitive` and `ReplacementStep`.

## Choose an entry point

```lean
import Gametheory.ScarfPath  -- The fixed-color room-door graph.
-- Or:
import Gametheory.Primitive -- Primitive sets, replacements, and traces; also imports the graph interface.
```

| Task | Interface |
| --- | --- |
| Construct a fixed-color graph | `ScarfPath.graph c i`, with vertex type `ScarfPath.Cell T I` |
| Identify relevant vertices, edges, or endpoints | `ScarfPath.IsVertex`, `ScarfPath.Edge`, `ScarfPath.IsEndpoint` |
| Use a degree bound or endpoint classification | `ScarfPath.degree_le_two`, `ScarfPath.isEndpoint_iff` |
| Use the packaged component result | `ScarfPath.component_structure` |
| Represent goods and slack indices in `T ⊕ I` | `Primitive.ExtendedGoods T I`, using `Sum.inl t` and `Sum.inr i`, respectively |
| Encode or recover a cell | `Primitive.toPrimitiveSet`, `Primitive.cell`, `Primitive.goods`, `Primitive.missingColors` |
| Express primitive or almost-primitive status | `Primitive.IsPrimitive`, `Primitive.IsAlmostPrimitive` |
| Express a replacement or obtain the corresponding graph walk | `Primitive.ReplacementStep`, `Primitive.SplitStep`, `h.walk` |
| Obtain a trace from the boundary to a fully colored set | `Primitive.Trace.nonempty c i` |
| Obtain only the existence of a fully colored set | `Primitive.exists_fullyColored c` |
| Use the optional coordinate model | `Primitive.Coordinate.exists_model`, `Primitive.Coordinate.IsPrimitive.erase_replacement` |

Complete compilable examples are in [`Gametheory/Examples/ScarfPrimitive.lean`](../../Gametheory/Examples/ScarfPrimitive.lean). The default `lake build` checks them, including parameter inference without opening entire namespaces, proof dot notation, and `simp` reductions of the encoding.

## A minimal trace example

The example below supplies `c` and `i` explicitly; the goods and index types are inferred from them. `IST` is the indexed-order instance shared with `Scarf.lean`. Use `(IST := ...)` to select it when multiple instances are available.

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

Given `i : I`, `Trace.nonempty` does not require an additional `[Inhabited I]` instance. The color-independent `exists_fullyColored` still uses that instance to select a starting color. Trace existence returns `Nonempty`: use `obtain` in a proof to extract a witness, then access `trace.terminal`, `trace.walk`, or `trace.terminal_colorful_room`.

## Operations follow their objects

- For `h : ScarfPath.Edge c i v w`, use `h.symm`, `h.left_vertex`, and `h.right_vertex`.
- For `h : Primitive.IsPrimitive X`, use `h.isRoom` to obtain the corresponding room.
- For `h : Primitive.IsAlmostPrimitive Y`, use `h.isDoor`.
- For `h : Primitive.ReplacementStep X X'`, use `h.symm`, `h.common_door`, and `h.exists_face`.
- For `h : Primitive.SplitStep c i X Y X'`, use `h.replacementStep`, `h.edges`, and `h.walk`.
- `simp` proves `Primitive.cell (Primitive.toPrimitiveSet σ C) = (σ, C)` directly, without inhabited types or an indexed-order instance.

These abbreviated types omit inferable implicit parameters. To inspect a full type, use a command such as `#check Primitive.SplitStep.walk` in the editor.

## Mathematical meaning of the definitions

The source is Ivanov's *Beyond Sperner's Lemma*, especially the primitive/slack-vector and path constructions in §3. The basic room/door definitions remain in `IndexedLOrder`.

`toPrimitiveSet σ C` is only a set encoding; it carries no proof of being primitive. To obtain that proof from a room, use `isPrimitive_of_room` or `isPrimitive_toPrimitiveSet_iff_room`. `IsPrimitive` is defined through dominance; `isRoomPrimitive_iff_isPrimitive` connects the room and native formulations. `IsAlmostPrimitive` is defined through doors; `isAlmostPrimitive_iff_native` connects it with the formulation as a codimension-one face contained in a primitive set.

The ambient vertex type of `ScarfPath.graph` consists of all finset pairs; pairs that do not satisfy `IsVertex` are isolated. The general graph interface is in the `PathComponents` namespace in [`Gametheory/PathComponents.lean`](../../Gametheory/PathComponents.lean). `ComponentHasSpanningPath` means that the path visits every vertex of the component; it does not assert that the path uses every edge. The analogous distinction applies to `ComponentHasSpanningCycle`.

`Trace` contains a graph walk from the slack boundary to the terminal set. It does not additionally record a `SplitStep` certificate for each step, an executable selection strategy, a guarantee of no repeated vertices, or a complexity bound. `SplitStep.walk` is a directional interface from a split replacement to a walk of length two.

## Migrating existing code

All declarations previously exported by these two modules have moved from `IndexedLOrder` to the new namespaces; no compatibility layer for old names was added. See [scarf-primitive-renames.md](scarf-primitive-renames.md) for the complete mapping. Ordinary room/door definitions and `IndexedLOrder.Scarf` are unchanged.

Typical calls change from `IndexedLOrder.GiGraph` to `ScarfPath.graph`, and from `IndexedLOrder.scarfAlgorithmTrace_exists` to `Primitive.Trace.nonempty`. It is generally unnecessary to `open` either namespace; retaining the `Primitive.` / `ScarfPath.` prefixes makes the relevant layer explicit.
