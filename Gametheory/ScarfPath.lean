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

/-- Vertices of `G_i`: the relevant rooms and doors of fixed type `i`. -/
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

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma GiEdge.left_vertex {c : T → I} {i : I} {v w : GiCell T I}
    (h : GiEdge (IST := IST) c i v w) :
    GiVertex (IST := IST) c i v := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2.1

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma GiEdge.right_vertex {c : T → I} {i : I} {v w : GiCell T I}
    (h : GiEdge (IST := IST) c i v w) :
    GiVertex (IST := IST) c i w :=
  (GiEdge.symm h).left_vertex

/-- The finite neighbor set of a vertex in `G_i`. -/
def GiNeighbors (c : T → I) (i : I) (v : GiCell T I) : Finset (GiCell T I) :=
  Finset.univ.filter (fun w => GiVertex (IST := IST) c i w ∧ GiEdge (IST := IST) c i v w)

omit [Inhabited T] in
lemma mem_GiNeighbors {c : T → I} {i : I} {v w : GiCell T I} :
    w ∈ GiNeighbors (IST := IST) c i v ↔ GiEdge (IST := IST) c i v w := by
  constructor
  · intro hw
    exact (Finset.mem_filter.mp hw).2.2
  · intro hEdge
    rw [GiNeighbors, Finset.mem_filter]
    exact ⟨Finset.mem_univ w, GiEdge.right_vertex hEdge, hEdge⟩

/-- Degree in `G_i`. -/
def GiDegree (c : T → I) (i : I) (v : GiCell T I) : Nat :=
  (GiNeighbors (IST := IST) c i v).card

/-- Endpoint vertices of `G_i`. -/
def GiEndpoint (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  GiVertex (IST := IST) c i v ∧ GiDegree (IST := IST) c i v = 1

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma not_room_of_door {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ IST.isRoom τ D := by
  intro hRoom
  have hCardDoor := hDoor.2
  have hCardRoom := hRoom.2
  omega

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma not_colorful_of_door {c : T → I} {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ IST.isColorful c τ D := by
  intro hColorful
  exact not_room_of_door hDoor (IST.room_of_colorful hColorful)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma not_GiRoomVertex_of_door {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ GiRoomVertex (IST := IST) c i (τ, D) := by
  intro hRoomVertex
  rcases hRoomVertex with hColorful | hTypedRoom
  · exact not_colorful_of_door hDoor hColorful
  · exact not_room_of_door hDoor hTypedRoom.1

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma not_door_of_room {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) :
    ¬ IST.isDoor σ C := by
  intro hDoor
  exact not_room_of_door hDoor hRoom

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma not_GiDoorVertex_of_room {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) :
    ¬ GiDoorVertex (IST := IST) c i (σ, C) := by
  intro hDoorVertex
  exact not_door_of_room hRoom hDoorVertex.1

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma isDoor_of_Doorof {τ σ : Finset T} {D C : Finset I}
    (hDoorof : IST.isDoorof τ D σ C) :
    IST.isDoor τ D := by
  cases hDoorof with
  | idoor _ hDoor _ _ _ _ => exact hDoor
  | odoor _ hDoor _ _ _ _ => exact hDoor

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma GiRoomVertex_of_incident_typed_door {c : T → I} {i : I}
    {τ σ : Finset T} {D C : Finset I}
    (hTypedDoor : IST.isTypedNC c i τ D)
    (hDoorof : IST.isDoorof τ D σ C) :
    GiRoomVertex (IST := IST) c i (σ, C) := by
  obtain hTypedRoom | hColorful := IST.NC_or_C_of_door hTypedDoor hDoorof
  · exact Or.inr ⟨IST.isRoom_of_Door hDoorof, hTypedRoom⟩
  · exact Or.inl hColorful

omit [Inhabited T] in
theorem GiDegree_internalDoor {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hInternal : IST.isInternalDoor τ D) (hTyped : IST.isTypedNC c i τ D) :
    GiDegree (IST := IST) c i (τ, D) = 2 := by
  obtain ⟨σ₁, σ₂, C₁, C₂, hNe, hRoom₁, hRoom₂, hDoor₁, hDoor₂, hUnique⟩ :=
    IST.internal_door_two_rooms τ D hInternal
  have hNeighbors :
      GiNeighbors (IST := IST) c i (τ, D) = ({(σ₁, C₁), (σ₂, C₂)} : Finset (GiCell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : GiEdge (IST := IST) c i (τ, D) w := (mem_GiNeighbors).1 hw
      rcases hEdge with hBad | hGood
      · exact False.elim (not_GiRoomVertex_of_door hInternal.1 hBad.1)
      · obtain hCases := hUnique w.1 w.2 (IST.isRoom_of_Door hGood.2.2) hGood.2.2
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hCases with hLeft | hRight
        · left
          exact Prod.ext hLeft.1 hLeft.2
        · right
          exact Prod.ext hRight.1 hRight.2
    · intro hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      apply (mem_GiNeighbors).2
      rcases hw with hEq | hEq
      · rw [hEq]
        exact Or.inr ⟨GiRoomVertex_of_incident_typed_door hTyped hDoor₁,
          ⟨hInternal.1, hTyped⟩, hDoor₁⟩
      · rw [hEq]
        exact Or.inr ⟨GiRoomVertex_of_incident_typed_door hTyped hDoor₂,
          ⟨hInternal.1, hTyped⟩, hDoor₂⟩
  rw [GiDegree, hNeighbors]
  exact Finset.card_pair hNe

omit [Inhabited T] in
theorem GiDegree_typedNCRoom {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) (hTyped : IST.isTypedNC c i σ C) :
    GiDegree (IST := IST) c i (σ, C) = 2 := by
  obtain ⟨door₁, door₂, hNe, hDoors⟩ :=
    IST.doors_of_NCroom (c := c) hRoom (IST.NC_of_TNC hTyped)
  have hNeighbors :
      GiNeighbors (IST := IST) c i (σ, C) = ({door₁, door₂} : Finset (GiCell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : GiEdge (IST := IST) c i (σ, C) w := (mem_GiNeighbors).1 hw
      rcases hEdge with hGood | hBad
      · have hwDoor : w ∈ IST.NCdoors c σ C := by
          change IST.isNearlyColorful c w.1 w.2 ∧ IST.isDoorof w.1 w.2 σ C
          exact ⟨IST.NC_of_TNC hGood.2.1.2, hGood.2.2⟩
        rw [hDoors] at hwDoor
        simpa using hwDoor
      · exact False.elim (not_GiDoorVertex_of_room hRoom hBad.2.1)
    · intro hw
      have hwDoor : w ∈ IST.NCdoors c σ C := by
        rw [hDoors]
        simpa using hw
      change IST.isNearlyColorful c w.1 w.2 ∧ IST.isDoorof w.1 w.2 σ C at hwDoor
      let hTypedDoor := IST.isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC
        hwDoor.1 hwDoor.2 hTyped
      apply (mem_GiNeighbors).2
      exact Or.inl ⟨Or.inr ⟨hRoom, hTyped⟩,
        ⟨isDoor_of_Doorof hwDoor.2, hTypedDoor⟩,
        hwDoor.2⟩
  rw [GiDegree, hNeighbors]
  exact Finset.card_pair hNe

theorem GiDegree_outsideDoor {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hOutside : IST.isOutsideDoor τ D) (hTyped : IST.isTypedNC c i τ D) :
    GiDegree (IST := IST) c i (τ, D) = 1 := by
  have hτ : τ = Finset.empty := hOutside.2
  have hD : D = ({i} : Finset I) := by
    have h := hTyped.2
    rw [hτ] at h
    simpa using h
  let xMax : T := @Finset.max' T (IST i) Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨(default : T)⟩)
  let room : GiCell T I := ({xMax}, ({i} : Finset I))
  have hCellRoom : IST.isCell ({xMax} : Finset T) ({i} : Finset I) := by
    intro y
    refine ⟨i, by simp, ?_⟩
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
  have hDoorofRoom : IST.isDoorof τ D ({xMax} : Finset T) ({i} : Finset I) := by
    rw [hτ, hD]
    apply isDoorof.idoor hCellRoom (IST.outsidedoor_singleton i).1 xMax
    · exact Finset.notMem_empty xMax
    · rfl
    · rfl
  have hNeighbors :
      GiNeighbors (IST := IST) c i (τ, D) = ({room} : Finset (GiCell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : GiEdge (IST := IST) c i (τ, D) w := (mem_GiNeighbors).1 hw
      rcases hEdge with hBad | hGood
      · exact False.elim (not_GiRoomVertex_of_door hOutside.1 hBad.1)
      · have hDoorof : IST.isDoorof τ D w.1 w.2 := hGood.2.2
        have hRoomW : IST.isRoom w.1 w.2 := IST.isRoom_of_Door hDoorof
        rw [hτ, hD] at hDoorof
        cases hDoorof with
        | idoor hCell _ x _ hInsert hDEq =>
            rw [Finset.mem_singleton]
            apply Prod.ext
            · have hwσ : w.1 = ({x} : Finset T) := by
                simpa using hInsert.symm
              have hxMax : x = xMax := by
                have hAbove : ∀ y : T, (IST i).le y x := by
                  intro y
                  obtain ⟨j, hj, hle⟩ := hCell y
                  have hji : j = i := by
                    rw [← hDEq] at hj
                    exact Finset.mem_singleton.mp hj
                  subst hji
                  apply hle
                  rw [hwσ]
                  simp
                have hx_le_max : (IST i).le x xMax :=
                  @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
                have hmax_le_x : (IST i).le xMax x := hAbove xMax
                exact @le_antisymm T (IST i).toPartialOrder x xMax hx_le_max hmax_le_x
              rw [hwσ, hxMax]
            · exact hDEq.symm
        | odoor _ _ _ _ hτEq _ =>
            exfalso
            have hσEmpty : w.1 = Finset.empty := by
              simpa using hτEq.symm
            have hNonempty := IST.sigma_nonempty_of_room hRoomW
            rw [hσEmpty] at hNonempty
            exact Finset.not_nonempty_empty hNonempty
    · intro hw
      rw [Finset.mem_singleton] at hw
      rw [hw]
      apply (mem_GiNeighbors).2
      exact Or.inr ⟨GiRoomVertex_of_incident_typed_door hTyped hDoorofRoom,
        ⟨hOutside.1, hTyped⟩, hDoorofRoom⟩
  rw [GiDegree, hNeighbors]
  simp

/-- A vertex has at most two neighbors in an abstract undirected graph relation. -/
def graphDegreeAtMostTwo {α : Type*} (step : α → α → Prop) : Prop :=
  ∀ ⦃v a b c⦄,
    step v a → step v b → step v c →
      a ≠ b → a ≠ c → b ≠ c → False

/-- A vertex is an endpoint when it has exactly one neighbor. -/
def graphEndpoint {α : Type*} (step : α → α → Prop) (v : α) : Prop :=
  ∃! w, step v w

/-- Consecutive vertices of a list are connected by the graph relation. -/
def graphWalk {α : Type*} (step : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => step x y ∧ graphWalk step (y :: rest)

/-- A simple path is a walk with no repeated vertices. -/
def graphSimplePath {α : Type*} [DecidableEq α] (step : α → α → Prop) (p : List α) : Prop :=
  graphWalk step p ∧ p.Nodup

/-- A cycle is a nontrivial closed walk whose interior vertices do not repeat. -/
def graphCycle {α : Type*} [DecidableEq α] (step : α → α → Prop) (p : List α) : Prop :=
  ∃ start rest,
    p = start :: rest ++ [start] ∧
      rest ≠ [] ∧
      (start :: rest).Nodup ∧
      graphWalk step p

/-- Two vertices lie in the same connected component if a walk connects them. -/
def graphConnected {α : Type*} (step : α → α → Prop) (a b : α) : Prop :=
  ∃ p, p ≠ [] ∧ p.head? = some a ∧ p.getLast? = some b ∧ graphWalk step p

/-- The finite connected component of a vertex inside a chosen finite vertex set. -/
def graphComponent {α : Type*} [Fintype α] (vertex : α → Prop) (step : α → α → Prop)
    (v : α) : Finset α :=
  Finset.univ.filter (fun w => vertex w ∧ graphConnected step v w)

/-- A component is represented by a simple path whose vertex set is exactly the component. -/
def graphPathComponent {α : Type*} [Fintype α] [DecidableEq α]
    (step : α → α → Prop) (component : Finset α) : Prop :=
  ∃ p : List α,
    graphSimplePath step p ∧
      p.toFinset = component

/-- A component is represented by a cycle whose vertex set is exactly the component. -/
def graphCycleComponent {α : Type*} [Fintype α] [DecidableEq α]
    (step : α → α → Prop) (component : Finset α) : Prop :=
  ∃ p : List α,
    graphCycle step p ∧
      p.toFinset = component

/-- The literal "disjoint paths and cycles" component statement for a finite graph. -/
def graphComponentsArePathsOrCycles {α : Type*} [Fintype α] [DecidableEq α]
    (vertex : α → Prop) (step : α → α → Prop) : Prop :=
  ∀ v, vertex v →
    graphPathComponent step (graphComponent vertex step v) ∨
      graphCycleComponent step (graphComponent vertex step v)

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
The degree characterization of `G_i`: every vertex has degree one or two, and
the degree-one vertices are exactly the unique outside door of type `i` and
the colorful rooms.
-/
def GiDegreeCharacterization (c : T → I) (i : I) : Prop :=
  (∀ v, GiVertex (IST := IST) c i v →
    GiDegree (IST := IST) c i v = 1 ∨ GiDegree (IST := IST) c i v = 2) ∧
  (∀ v, GiEndpoint (IST := IST) c i v ↔
    (GiDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
      IST.isColorful c v.1 v.2)

/--
The path-structure target for `G_i`: degree characterization plus the local
degree-at-most-two property used by path-following.
-/
def GiPathStructure (c : T → I) (i : I) : Prop :=
  GiDegreeCharacterization (IST := IST) c i ∧
    graphDegreeAtMostTwo (GiEdge (IST := IST) c i)

/--
The faithful component-level target for `G_i`: its connected components are
paths or cycles, and the endpoints of path components are exactly colorful
rooms except for the unique outside door of type `i`.
-/
def GiComponentStructure (c : T → I) (i : I) : Prop :=
  graphComponentsArePathsOrCycles (GiVertex (IST := IST) c i) (GiEdge (IST := IST) c i) ∧
    (∀ v, GiEndpoint (IST := IST) c i v ↔
      (GiDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
        IST.isColorful c v.1 v.2)

omit [Inhabited T] in
theorem GiPathStructure_of_degreeCharacterization {c : T → I} {i : I}
    (hdegStmt : GiDegreeCharacterization (IST := IST) c i) :
    GiPathStructure (IST := IST) c i := by
  refine ⟨hdegStmt, ?_⟩
  intro v a b d hva hvb hvd hab had hbd
  have hv : GiVertex (IST := IST) c i v := GiEdge.left_vertex hva
  have hDegree := (hdegStmt.1 v hv)
  have haMem : a ∈ GiNeighbors (IST := IST) c i v := (mem_GiNeighbors).2 hva
  have hbMem : b ∈ GiNeighbors (IST := IST) c i v := (mem_GiNeighbors).2 hvb
  have hdMem : d ∈ GiNeighbors (IST := IST) c i v := (mem_GiNeighbors).2 hvd
  have hTripleSubset : ({a, b, d} : Finset (GiCell T I)) ⊆ GiNeighbors (IST := IST) c i v := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haMem
    · exact hbMem
    · exact hdMem
  have hTripleCard : ({a, b, d} : Finset (GiCell T I)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, b, d, hab, had, hbd, rfl⟩
  have hCardLe : 3 ≤ GiDegree (IST := IST) c i v := by
    rw [GiDegree, ← hTripleCard]
    exact Finset.card_le_card hTripleSubset
  rcases hDegree with hOne | hTwo
  · omega
  · omega

omit [Inhabited T] in
theorem GiComponentStructure_of_components_are_paths_or_cycles {c : T → I} {i : I}
    (hdegStmt : GiDegreeCharacterization (IST := IST) c i)
    (hcomponents :
      graphComponentsArePathsOrCycles (GiVertex (IST := IST) c i) (GiEdge (IST := IST) c i)) :
    GiComponentStructure (IST := IST) c i := by
  exact ⟨hcomponents, hdegStmt.2⟩

end IndexedLOrder

end
