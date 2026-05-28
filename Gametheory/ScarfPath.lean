import Gametheory.Scarf

open Classical
open Finset

noncomputable section

namespace IndexedLOrder

variable {T I : Type*} [Inhabited T] [Fintype T] [Fintype I]
variable [DecidableEq T] [DecidableEq I] [IST : IndexedLOrder I T]

/-- A room/door cell, represented as the pair `(σ, C)`. -/
abbrev GiCell (T I : Type*) := Finset T × Finset I

/-- The room-type vertices of the graph `G_i`: colorful rooms and typed nearly-colorful rooms. -/
def GiRoomVertex (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  IST.isColorful c v.1 v.2 ∨
    (IST.isRoom v.1 v.2 ∧ IST.isTypedNC c i v.1 v.2)

/-- The door-type vertices of the graph `G_i`: typed nearly-colorful doors. -/
def GiDoorVertex (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  IST.isDoor v.1 v.2 ∧ IST.isTypedNC c i v.1 v.2

/-- Vertices of `G_i`, as in Theorem 9. -/
def GiVertex (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  GiRoomVertex (IST := IST) c i v ∨ GiDoorVertex (IST := IST) c i v

/-- Edges of `G_i`: room-door incidence, made symmetric. -/
def GiEdge (c : T → I) (i : I) (v w : GiCell T I) : Prop :=
  (GiRoomVertex (IST := IST) c i v ∧
    GiDoorVertex (IST := IST) c i w ∧
      IST.isDoorof w.1 w.2 v.1 v.2) ∨
  (GiRoomVertex (IST := IST) c i w ∧
    GiDoorVertex (IST := IST) c i v ∧
      IST.isDoorof v.1 v.2 w.1 w.2)

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma GiEdge.symm {c : T → I} {i : I} {v w : GiCell T I}
    (h : GiEdge (IST := IST) c i v w) :
    GiEdge (IST := IST) c i w v := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The finite neighbor set of a vertex in `G_i`. -/
def GiNeighbors (c : T → I) (i : I) (v : GiCell T I) : Finset (GiCell T I) :=
  Finset.univ.filter (fun w => GiVertex (IST := IST) c i w ∧ GiEdge (IST := IST) c i v w)

/-- Degree in `G_i`. -/
def GiDegree (c : T → I) (i : I) (v : GiCell T I) : Nat :=
  (GiNeighbors (IST := IST) c i v).card

/-- Endpoint vertices of `G_i`. -/
def GiEndpoint (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  GiVertex (IST := IST) c i v ∧ GiDegree (IST := IST) c i v = 1

/-- A vertex has at most two neighbors in an abstract undirected graph relation. -/
def graphDegreeAtMostTwo {α : Type*} (step : α → α → Prop) : Prop :=
  ∀ ⦃v a b c⦄,
    step v a → step v b → step v c →
      a ≠ b → a ≠ c → b ≠ c → False

/-- A vertex is an endpoint when it has exactly one neighbor. -/
def graphEndpoint {α : Type*} (step : α → α → Prop) (v : α) : Prop :=
  ∃! w, step v w

/-- At an endpoint there is only one possible first step. -/
theorem graphEndpoint_firstStep_unique {α : Type*} {step : α → α → Prop}
    {v a b : α} (hend : graphEndpoint step v)
    (ha : step v a) (hb : step v b) :
    a = b := by
  rcases hend with ⟨w, _hw, hUnique⟩
  exact (hUnique a ha).trans (hUnique b hb).symm

/--
In a graph of degree at most two, once a path enters `cur` from `prev`, there
is at most one way to continue without turning back.
-/
theorem graph_nextStep_unique_of_noBacktracking {α : Type*} {step : α → α → Prop}
    (hdeg : graphDegreeAtMostTwo step)
    {prev cur next₁ next₂ : α}
    (hprev : step cur prev) (hnext₁ : step cur next₁) (hnext₂ : step cur next₂)
    (hne₁ : next₁ ≠ prev) (hne₂ : next₂ ≠ prev) :
    next₁ = next₂ := by
  by_contra hne
  exact hdeg hprev hnext₁ hnext₂
    (fun h => hne₁ h.symm)
    (fun h => hne₂ h.symm)
    hne

/--
The degree statement underlying Theorem 9: every `G_i` vertex has degree one
or two, and the degree-one vertices are exactly the unique outside door of type
`i` and the colorful rooms.
-/
def GiTheorem9DegreeStatement (c : T → I) (i : I) : Prop :=
  (∀ v, GiVertex (IST := IST) c i v →
    GiDegree (IST := IST) c i v = 1 ∨ GiDegree (IST := IST) c i v = 2) ∧
  (∀ v, GiEndpoint (IST := IST) c i v ↔
    (GiDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
      IST.isColorful c v.1 v.2)

/--
Target statement for the graph part of Theorem 9.  The eventual proof should
combine `GiTheorem9DegreeStatement` with the elementary degree-one/two graph
path-following lemmas above.
-/
def GiTheorem9Target (c : T → I) (i : I) : Prop :=
  GiTheorem9DegreeStatement (IST := IST) c i ∧
    graphDegreeAtMostTwo (GiEdge (IST := IST) c i)

end IndexedLOrder

end
