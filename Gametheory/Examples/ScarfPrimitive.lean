import Gametheory.Primitive

/-!
# Using the Scarf path and primitive APIs

Client examples for namespace discovery, inferred parameters, proof dot
notation, and the boundary-to-terminal interface. `lake build` checks this
module. Import `Gametheory.Primitive` to use both APIs in your own file.
-/

namespace Examples.ScarfPrimitive

variable {T I : Type*} [Fintype T] [Fintype I]
variable [DecidableEq T] [DecidableEq I] [IST : IndexedLOrder I T]

-- Edge proofs carry the operations and vertex information a caller needs.
example {c : T → I} {i : I} {v w : ScarfPath.Cell T I}
    (h : ScarfPath.Edge (IST := IST) c i v w) :
    ScarfPath.Edge (IST := IST) c i w v ∧ ScarfPath.IsVertex (IST := IST) c i v :=
  ⟨h.symm, h.left_vertex⟩

-- The encoding simplifier works without inhabited types or indexed-order data.
example (σ : Finset T) (C : Finset I) :
    Primitive.cell (Primitive.toPrimitiveSet σ C) = (σ, C) := by
  simp

variable [Inhabited T]

-- Direct graph interfaces avoid unpacking a bundled statement with `.1`/`.2`.
example (c : T → I) (i : I) (v : ScarfPath.Cell T I) :
    ScarfPath.degree (IST := IST) c i v ≤ 2 :=
  ScarfPath.degree_le_two c i v

example (c : T → I) (i : I) (v : ScarfPath.Cell T I) :
    ScarfPath.IsEndpoint (IST := IST) c i v ↔
      (ScarfPath.IsDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
        IST.isColorful c v.1 v.2 :=
  ScarfPath.isEndpoint_iff c i v

-- Recover the associated room directly from a primitive proof.
example {X : Finset (Primitive.ExtendedGoods T I)}
    (h : Primitive.IsPrimitive (IST := IST) X) :
    IST.isRoom (Primitive.goods X) (Primitive.missingColors X) :=
  h.isRoom

example {X : Finset (Primitive.ExtendedGoods T I)}
    (h : Primitive.IsPrimitive (IST := IST) X)
    {x : Primitive.ExtendedGoods T I} (hx : x ∈ X) :
    ¬ (Primitive.goods (X.erase x)).Nonempty ∨
      ∃! y, y ∉ X ∧ Primitive.IsPrimitive (IST := IST) (insert y (X.erase x)) :=
  h.erase_replacement hx

example {c : T → I} {i : I} {X Y X' : Finset (Primitive.ExtendedGoods T I)}
    (h : Primitive.SplitStep (IST := IST) c i X Y X') :
    Primitive.ReplacementStep (IST := IST) X X' :=
  h.replacementStep

noncomputable example {c : T → I} {i : I}
    {X Y X' : Finset (Primitive.ExtendedGoods T I)}
    (h : Primitive.SplitStep (IST := IST) c i X Y X') :
    (ScarfPath.graph (IST := IST) c i).Walk (Primitive.cell X) (Primitive.cell X') :=
  h.walk

-- Consume the classical witness inside a proof, then use its terminal and walk.
example (c : T → I) (i : I) :
    ∃ X : Finset (Primitive.ExtendedGoods T I),
      Primitive.IsFullyColored (IST := IST) c X ∧
      (ScarfPath.graph (IST := IST) c i).Reachable
        (Primitive.cell (Primitive.slackBoundary i)) (Primitive.cell X) := by
  obtain ⟨trace⟩ := Primitive.Trace.nonempty (IST := IST) c i
  exact ⟨trace.terminal, trace.terminal_fullyColored, ⟨trace.walk⟩⟩

example {c : T → I} {i : I} (trace : Primitive.Trace (IST := IST) c i) :
    IST.isColorful c (Primitive.goods trace.terminal)
      (Primitive.missingColors trace.terminal) :=
  trace.terminal_colorful_room

-- Coordinate realizations are an optional, separately named interface.
example [Inhabited I] :
    ∃ (u : I → T → ℝ) (M : I → ℝ),
      Primitive.Coordinate.PositiveRealization (IST := IST) u ∧
      Primitive.Coordinate.SlackBounds u M ∧
      Primitive.Coordinate.SlackHeightsPairwiseDistinct M ∧
      Primitive.Coordinate.DefinesLinearOrders u M :=
  Primitive.Coordinate.exists_model

example {u : I → T → ℝ} {M : I → ℝ}
    {hCoord : Primitive.Coordinate.DefinesLinearOrders u M}
    (hu : Primitive.Coordinate.PositiveRealization (IST := IST) u)
    (hM : Primitive.Coordinate.SlackBounds u M)
    {X : Finset (Primitive.ExtendedGoods T I)}
    (h : Primitive.Coordinate.IsPrimitive u M hCoord X)
    {x : Primitive.ExtendedGoods T I} (hx : x ∈ X) :
    ¬ (Primitive.goods (X.erase x)).Nonempty ∨
      ∃! y, y ∉ X ∧ Primitive.Coordinate.IsPrimitive u M hCoord (insert y (X.erase x)) :=
  h.erase_replacement hu hM hx

end Examples.ScarfPrimitive
