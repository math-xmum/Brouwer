import Gametheory.Scarf
import Gametheory.PathComponents



open Classical
open Finset

noncomputable section

namespace ScarfPath

open IndexedLOrder

variable {T I : Type*} [Inhabited T] [Fintype T] [Fintype I]
variable [DecidableEq T] [DecidableEq I] [IST : IndexedLOrder I T]

/-- A room/door cell, represented as the pair $(\sigma, C)$. -/
abbrev Cell (T I : Type*) := Finset T × Finset I

/-- The room-type vertices of the graph $G_i$: colorful rooms and typed nearly-colorful rooms. -/
def IsRoomVertex (c : T → I) (i : I) (v : Cell T I) : Prop :=
  IST.isColorful c v.1 v.2 ∨
    (IST.isRoom v.1 v.2 ∧ IST.isTypedNC c i v.1 v.2)

/-- The door-type vertices of the graph $G_i$: typed nearly-colorful doors. -/
def IsDoorVertex (c : T → I) (i : I) (v : Cell T I) : Prop :=
  IST.isDoor v.1 v.2 ∧ IST.isTypedNC c i v.1 v.2

/-- Vertices of $G_i$: the relevant rooms and doors of fixed type $i$. -/
def IsVertex (c : T → I) (i : I) (v : Cell T I) : Prop :=
  IsRoomVertex (IST := IST) c i v ∨ IsDoorVertex (IST := IST) c i v

/-- Edges of $G_i$: room-door incidence, made symmetric. -/
def Edge (c : T → I) (i : I) (v w : Cell T I) : Prop :=
  (IsRoomVertex (IST := IST) c i v ∧
    IsDoorVertex (IST := IST) c i w ∧
      IST.isDoorof w.1 w.2 v.1 v.2) ∨
  (IsRoomVertex (IST := IST) c i w ∧
    IsDoorVertex (IST := IST) c i v ∧
      IST.isDoorof v.1 v.2 w.1 w.2)

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma Edge.symm {c : T → I} {i : I} {v w : Cell T I}
    (h : Edge (IST := IST) c i v w) :
    Edge (IST := IST) c i w v := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma Edge.left_vertex {c : T → I} {i : I} {v w : Cell T I}
    (h : Edge (IST := IST) c i v w) :
    IsVertex (IST := IST) c i v := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2.1

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma Edge.right_vertex {c : T → I} {i : I} {v w : Cell T I}
    (h : Edge (IST := IST) c i v w) :
    IsVertex (IST := IST) c i w :=
  (Edge.symm h).left_vertex

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma IsRoomVertex.room {c : T → I} {i : I} {v : Cell T I}
    (h : IsRoomVertex (IST := IST) c i v) :
    IST.isRoom v.1 v.2 := by
  rcases h with hColorful | hTyped
  · exact IST.room_of_colorful hColorful
  · exact hTyped.1

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma IsDoorVertex.door {c : T → I} {i : I} {v : Cell T I}
    (h : IsDoorVertex (IST := IST) c i v) :
    IST.isDoor v.1 v.2 := h.1

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma Edge.irrefl {c : T → I} {i : I} (v : Cell T I) :
    ¬ Edge (IST := IST) c i v v := by
  intro h
  rcases h with h | h
  · have hRoom := h.1.room
    have hDoor := h.2.1.door
    have hRoomCard := hRoom.2
    have hDoorCard := hDoor.2
    omega
  · have hRoom := h.1.room
    have hDoor := h.2.1.door
    have hRoomCard := hRoom.2
    have hDoorCard := hDoor.2
    omega

/-- The Mathlib `SimpleGraph` whose vertices and edges are the graph $G_i$. -/
def graph (c : T → I) (i : I) : SimpleGraph (Cell T I) where
  Adj := Edge (IST := IST) c i
  symm := ⟨fun _ _ h => Edge.symm h⟩
  loopless := ⟨fun v => Edge.irrefl (IST := IST) (c := c) (i := i) v⟩

/-- The finite neighbor set of a vertex in $G_i$. -/
def neighbors (c : T → I) (i : I) (v : Cell T I) : Finset (Cell T I) :=
  (graph (IST := IST) c i).neighborFinset v

omit [Inhabited T] in
lemma mem_neighbors {c : T → I} {i : I} {v w : Cell T I} :
    w ∈ neighbors (IST := IST) c i v ↔ Edge (IST := IST) c i v w := by
  exact SimpleGraph.mem_neighborFinset (graph (IST := IST) c i) v w

/-- Degree in $G_i$. -/
def degree (c : T → I) (i : I) (v : Cell T I) : Nat :=
  (neighbors (IST := IST) c i v).card

/-- Endpoint vertices of $G_i$. -/
def IsEndpoint (c : T → I) (i : I) (v : Cell T I) : Prop :=
  IsVertex (IST := IST) c i v ∧ degree (IST := IST) c i v = 1

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
lemma not_IsRoomVertex_of_door {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ IsRoomVertex (IST := IST) c i (τ, D) := by
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
lemma not_IsDoorVertex_of_room {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) :
    ¬ IsDoorVertex (IST := IST) c i (σ, C) := by
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
lemma isRoomVertex_of_incident_typed_door {c : T → I} {i : I}
    {τ σ : Finset T} {D C : Finset I}
    (hTypedDoor : IST.isTypedNC c i τ D)
    (hDoorof : IST.isDoorof τ D σ C) :
    IsRoomVertex (IST := IST) c i (σ, C) := by
  obtain hTypedRoom | hColorful := IST.NC_or_C_of_door hTypedDoor hDoorof
  · exact Or.inr ⟨IST.isRoom_of_Door hDoorof, hTypedRoom⟩
  · exact Or.inl hColorful

omit [Inhabited T] in
theorem degree_of_internalDoor {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hInternal : IST.isInternalDoor τ D) (hTyped : IST.isTypedNC c i τ D) :
    degree (IST := IST) c i (τ, D) = 2 := by
  obtain ⟨σ₁, σ₂, C₁, C₂, hNe, hRoom₁, hRoom₂, hDoor₁, hDoor₂, hUnique⟩ :=
    IST.internal_door_two_rooms τ D hInternal
  have hNeighbors :
      neighbors (IST := IST) c i (τ, D) = ({(σ₁, C₁), (σ₂, C₂)} : Finset (Cell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : Edge (IST := IST) c i (τ, D) w := (mem_neighbors).1 hw
      rcases hEdge with hBad | hGood
      · exact False.elim (not_IsRoomVertex_of_door hInternal.1 hBad.1)
      · obtain hCases := hUnique w.1 w.2 (IST.isRoom_of_Door hGood.2.2) hGood.2.2
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hCases with hLeft | hRight
        · left
          exact Prod.ext hLeft.1 hLeft.2
        · right
          exact Prod.ext hRight.1 hRight.2
    · intro hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      apply (mem_neighbors).2
      rcases hw with hEq | hEq
      · rw [hEq]
        exact Or.inr ⟨isRoomVertex_of_incident_typed_door hTyped hDoor₁,
          ⟨hInternal.1, hTyped⟩, hDoor₁⟩
      · rw [hEq]
        exact Or.inr ⟨isRoomVertex_of_incident_typed_door hTyped hDoor₂,
          ⟨hInternal.1, hTyped⟩, hDoor₂⟩
  rw [degree, hNeighbors]
  exact Finset.card_pair hNe

omit [Inhabited T] in
theorem degree_of_typedNCRoom {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) (hTyped : IST.isTypedNC c i σ C) :
    degree (IST := IST) c i (σ, C) = 2 := by
  obtain ⟨door₁, door₂, hNe, hDoors⟩ :=
    IST.doors_of_NCroom (c := c) hRoom (IST.NC_of_TNC hTyped)
  have hNeighbors :
      neighbors (IST := IST) c i (σ, C) = ({door₁, door₂} : Finset (Cell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : Edge (IST := IST) c i (σ, C) w := (mem_neighbors).1 hw
      rcases hEdge with hGood | hBad
      · have hwDoor : w ∈ IST.NCdoors c σ C := by
          change IST.isNearlyColorful c w.1 w.2 ∧ IST.isDoorof w.1 w.2 σ C
          exact ⟨IST.NC_of_TNC hGood.2.1.2, hGood.2.2⟩
        rw [hDoors] at hwDoor
        simpa using hwDoor
      · exact False.elim (not_IsDoorVertex_of_room hRoom hBad.2.1)
    · intro hw
      have hwDoor : w ∈ IST.NCdoors c σ C := by
        rw [hDoors]
        simpa using hw
      change IST.isNearlyColorful c w.1 w.2 ∧ IST.isDoorof w.1 w.2 σ C at hwDoor
      let hTypedDoor := IST.isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC
        hwDoor.1 hwDoor.2 hTyped
      apply (mem_neighbors).2
      exact Or.inl ⟨Or.inr ⟨hRoom, hTyped⟩,
        ⟨isDoor_of_Doorof hwDoor.2, hTypedDoor⟩,
        hwDoor.2⟩
  rw [degree, hNeighbors]
  exact Finset.card_pair hNe

theorem degree_of_outsideDoor {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hOutside : IST.isOutsideDoor τ D) (hTyped : IST.isTypedNC c i τ D) :
    degree (IST := IST) c i (τ, D) = 1 := by
  have hτ : τ = Finset.empty := hOutside.2
  have hD : D = ({i} : Finset I) := by
    have h := hTyped.2
    rw [hτ] at h
    have hImg : Finset.image c (Finset.empty : Finset T) = Finset.empty := Finset.image_empty c
    rw [hImg] at h
    have hsdiff : D \ (Finset.empty : Finset I) = D :=
      Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_empty_right D)
    rwa [hsdiff] at h
  let xMax : T := @Finset.max' T (IST i) Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨(default : T)⟩)
  let room : Cell T I := ({xMax}, ({i} : Finset I))
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
      neighbors (IST := IST) c i (τ, D) = ({room} : Finset (Cell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : Edge (IST := IST) c i (τ, D) w := (mem_neighbors).1 hw
      rcases hEdge with hBad | hGood
      · exact False.elim (not_IsRoomVertex_of_door hOutside.1 hBad.1)
      · have hDoorof : IST.isDoorof τ D w.1 w.2 := hGood.2.2
        have hRoomW : IST.isRoom w.1 w.2 := IST.isRoom_of_Door hDoorof
        rw [hτ, hD] at hDoorof
        cases hDoorof with
        | idoor hCell _ x _ hInsert hDEq =>
            rw [Finset.mem_singleton]
            apply Prod.ext
            · have hwσ : w.1 = ({x} : Finset T) := by
                calc
                  w.1 = insert x ∅ := hInsert.symm
                  _ = {x} := Finset.insert_empty
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
      apply (mem_neighbors).2
      exact Or.inr ⟨isRoomVertex_of_incident_typed_door hTyped hDoorofRoom,
        ⟨hOutside.1, hTyped⟩, hDoorofRoom⟩
  rw [degree, hNeighbors]
  simp

omit [Inhabited T] in
theorem degree_of_colorfulRoom {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hColorful : IST.isColorful c σ C) :
    degree (IST := IST) c i (σ, C) = 1 := by
  have hRoom : IST.isRoom σ C := IST.room_of_colorful hColorful
  have hInj : Set.InjOn c (↑σ : Set T) := by
    apply (Finset.card_image_iff).mp
    rw [hColorful.2, hRoom.2]
  by_cases hiC : i ∈ C
  · have hiImage : i ∈ σ.image c := by
      rwa [hColorful.2]
    obtain ⟨x, hxσ, hcx⟩ := Finset.mem_image.mp hiImage
    let door : Cell T I := (σ.erase x, C)
    have hxUnique : ∀ ⦃y⦄, y ∈ σ → c y = c x → y = x := by
      intro y hy hcy
      exact hInj hy hxσ hcy
    have hDoorof : IST.isDoorof (σ.erase x) C σ C :=
      IST.isDoorof_erase_of_isRoom σ C x hRoom hxσ
    have hTypedDoor : IST.isTypedNC c i (σ.erase x) C := by
      constructor
      · exact IST.Dominant_of_subset σ (σ.erase x) C (Finset.erase_subset x σ) hColorful.1
      · have hImgErase :
            (σ.erase x).image c = (σ.image c).erase (c x) :=
          image_erase_eq_erase_image_of_unique σ c hxσ hxUnique
        rw [hImgErase, ← hColorful.2, hcx]
        ext j
        constructor
        · intro hj
          rcases Finset.mem_sdiff.mp hj with ⟨hjC, hjNotErase⟩
          by_cases hji : j = i
          · simp [hji]
          · have hjErase : j ∈ (σ.image c).erase i := Finset.mem_erase.mpr ⟨hji, hjC⟩
            exact False.elim (hjNotErase hjErase)
        · intro hj
          have hji : j = i := Finset.mem_singleton.mp hj
          subst hji
          exact Finset.mem_sdiff.mpr ⟨hiImage, by simp⟩
    have hNeighbors :
        neighbors (IST := IST) c i (σ, C) = ({door} : Finset (Cell T I)) := by
      ext w
      constructor
      · intro hw
        have hEdge : Edge (IST := IST) c i (σ, C) w := (mem_neighbors).1 hw
        rcases hEdge with hGood | hBad
        · have hDoorofW : IST.isDoorof w.1 w.2 σ C := hGood.2.2
          have hTypedW : IST.isTypedNC c i w.1 w.2 := hGood.2.1.2
          cases hDoorofW with
          | idoor _ _ y hyNot hInsert hDEq =>
              have hyσ : y ∈ σ := by
                rw [← hInsert]
                exact Finset.mem_insert_self y w.1
              have hwσ : w.1 = σ.erase y := by
                rw [← Finset.erase_insert hyNot, hInsert]
              have hcyNotErase : c y ∉ (σ.erase y).image c := by
                intro hmem
                rcases Finset.mem_image.mp hmem with ⟨z, hzErase, hcz⟩
                have hzσ : z ∈ σ := Finset.erase_subset y σ hzErase
                have hzEq : z = y := hInj hzσ hyσ hcz
                exact (Finset.mem_erase.mp hzErase).1 hzEq
              have hcyDiff : c y ∈ w.2 \ w.1.image c := by
                rw [hDEq, hwσ]
                exact Finset.mem_sdiff.mpr
                  ⟨by rw [← hColorful.2]; exact Finset.mem_image_of_mem c hyσ, hcyNotErase⟩
              have hcyi : c y = i := by
                rw [hTypedW.2] at hcyDiff
                exact Finset.mem_singleton.mp hcyDiff
              have hyx : y = x := hInj hyσ hxσ (hcyi.trans hcx.symm)
              rw [Finset.mem_singleton]
              apply Prod.ext
              · rw [hwσ, hyx]
              · exact hDEq
          | odoor _ _ j _ hτEq _ =>
              exfalso
              have hiDiff : i ∈ w.2 \ w.1.image c := by
                rw [hTypedW.2]
                simp
              have hiNotImage : i ∉ w.1.image c := (Finset.mem_sdiff.mp hiDiff).2
              rw [hτEq] at hiNotImage
              exact hiNotImage hiImage
        · exact False.elim (not_IsDoorVertex_of_room hRoom hBad.2.1)
      · intro hw
        rw [Finset.mem_singleton] at hw
        rw [hw]
        apply (mem_neighbors).2
        exact Or.inl ⟨Or.inl hColorful, ⟨isDoor_of_Doorof hDoorof, hTypedDoor⟩, hDoorof⟩
    rw [degree, hNeighbors]
    simp
  · let door : Cell T I := (σ, insert i C)
    have hDoor : IST.isDoor σ (insert i C) := by
      constructor
      · exact IST.Dominant_of_supset σ C (insert i C) (Finset.subset_insert i C) hColorful.1
      · rw [Finset.card_insert_of_notMem hiC, hRoom.2]
    have hDoorof : IST.isDoorof σ (insert i C) σ C :=
      isDoorof.odoor hColorful.1 hDoor i hiC rfl rfl
    have hTypedDoor : IST.isTypedNC c i σ (insert i C) := by
      constructor
      · exact hDoor.1
      · rw [← hColorful.2]
        ext j
        constructor
        · intro hj
          rcases Finset.mem_sdiff.mp hj with ⟨hjInsert, hjNotImage⟩
          rcases Finset.mem_insert.mp hjInsert with hji | hjImage
          · simp [hji]
          · exact False.elim (hjNotImage hjImage)
        · intro hj
          have hji : j = i := Finset.mem_singleton.mp hj
          rw [hji]
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_insert_self i (σ.image c), by
              rwa [hColorful.2]⟩
    have hNeighbors :
        neighbors (IST := IST) c i (σ, C) = ({door} : Finset (Cell T I)) := by
      ext w
      constructor
      · intro hw
        have hEdge : Edge (IST := IST) c i (σ, C) w := (mem_neighbors).1 hw
        rcases hEdge with hGood | hBad
        · have hDoorofW : IST.isDoorof w.1 w.2 σ C := hGood.2.2
          have hTypedW : IST.isTypedNC c i w.1 w.2 := hGood.2.1.2
          cases hDoorofW with
          | idoor _ _ y _ _ hDEq =>
              exfalso
              have hiDiff : i ∈ w.2 \ w.1.image c := by
                rw [hTypedW.2]
                simp
              have hiC' : i ∈ C := by
                rw [hDEq] at hiDiff
                exact (Finset.mem_sdiff.mp hiDiff).1
              exact hiC hiC'
          | odoor _ _ j hjNotC hτEq hDEq =>
              have hjDiff : j ∈ w.2 \ w.1.image c := by
                rw [hDEq, hτEq]
                exact Finset.mem_sdiff.mpr
                  ⟨Finset.mem_insert_self j C, by
                    rw [hColorful.2]
                    exact hjNotC⟩
              have hji : j = i := by
                rw [hTypedW.2] at hjDiff
                exact Finset.mem_singleton.mp hjDiff
              rw [Finset.mem_singleton]
              apply Prod.ext
              · exact hτEq
              · rw [hDEq, hji]
        · exact False.elim (not_IsDoorVertex_of_room hRoom hBad.2.1)
      · intro hw
        rw [Finset.mem_singleton] at hw
        rw [hw]
        apply (mem_neighbors).2
        exact Or.inl ⟨Or.inl hColorful, ⟨hDoor, hTypedDoor⟩, hDoorof⟩
    rw [degree, hNeighbors]
    simp

/--
The degree characterization of $G_i$: every vertex has degree $1$ or $2$, and
the degree-$1$ vertices are exactly the unique outside door of type $i$ and
the colorful rooms.
-/
def DegreeCharacterization (c : T → I) (i : I) : Prop :=
  (∀ v, IsVertex (IST := IST) c i v →
    degree (IST := IST) c i v = 1 ∨ degree (IST := IST) c i v = 2) ∧
  (∀ v, IsEndpoint (IST := IST) c i v ↔
    (IsDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
      IST.isColorful c v.1 v.2)

theorem degree_characterization (c : T → I) (i : I) :
    DegreeCharacterization (IST := IST) c i := by
  constructor
  · intro v hv
    rcases hv with hRoomVertex | hDoorVertex
    · rcases hRoomVertex with hColorful | hTypedRoom
      · exact Or.inl (degree_of_colorfulRoom (IST := IST) (i := i) hColorful)
      · exact Or.inr (degree_of_typedNCRoom (IST := IST) hTypedRoom.1 hTypedRoom.2)
    · by_cases hNonempty : v.1.Nonempty
      · exact Or.inr (degree_of_internalDoor (IST := IST) ⟨hDoorVertex.1, hNonempty⟩ hDoorVertex.2)
      · have hOutside : IST.isOutsideDoor v.1 v.2 :=
          ⟨hDoorVertex.1, Finset.not_nonempty_iff_eq_empty.mp hNonempty⟩
        exact Or.inl (degree_of_outsideDoor (IST := IST) hOutside hDoorVertex.2)
  · intro v
    constructor
    · intro hend
      rcases hend with ⟨hv, hDegreeOne⟩
      rcases hv with hRoomVertex | hDoorVertex
      · rcases hRoomVertex with hColorful | hTypedRoom
        · exact Or.inr hColorful
        · have hDegreeTwo := degree_of_typedNCRoom (IST := IST) hTypedRoom.1 hTypedRoom.2
          exfalso
          rw [hDegreeOne] at hDegreeTwo
          norm_num at hDegreeTwo
      · by_cases hNonempty : v.1.Nonempty
        · have hDegreeTwo := degree_of_internalDoor (IST := IST) ⟨hDoorVertex.1, hNonempty⟩ hDoorVertex.2
          exfalso
          rw [hDegreeOne] at hDegreeTwo
          norm_num at hDegreeTwo
        · have hOutside : IST.isOutsideDoor v.1 v.2 :=
            ⟨hDoorVertex.1, Finset.not_nonempty_iff_eq_empty.mp hNonempty⟩
          exact Or.inl ⟨hDoorVertex, hOutside⟩
    · intro hEndpointKind
      rcases hEndpointKind with hOutsideDoor | hColorful
      · exact ⟨Or.inr hOutsideDoor.1,
          degree_of_outsideDoor (IST := IST) hOutsideDoor.2 hOutsideDoor.1.2⟩
      · exact ⟨Or.inl (Or.inl hColorful),
          degree_of_colorfulRoom (IST := IST) (i := i) hColorful⟩

/--
The path-structure target for $G_i$: degree characterization plus the local
degree-at-most-$2$ property used by path-following.
-/
def PathStructure (c : T → I) (i : I) : Prop :=
  DegreeCharacterization (IST := IST) c i ∧
    PathComponents.DegreeAtMostTwo (graph (IST := IST) c i)

/--
The component-level statement for $G_i$: every connected component has a
spanning path or cycle, and degree-one vertices are exactly colorful rooms
and the unique outside door of type $i$.
-/
def ComponentStructure (c : T → I) (i : I) : Prop :=
  PathComponents.ComponentsHaveSpanningPathsOrCycles (graph (IST := IST) c i) ∧
    (∀ v, IsEndpoint (IST := IST) c i v ↔
      (IsDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
        IST.isColorful c v.1 v.2)

omit [Inhabited T] in
theorem pathStructure_of_degreeCharacterization {c : T → I} {i : I}
    (hdegStmt : DegreeCharacterization (IST := IST) c i) :
    PathStructure (IST := IST) c i := by
  refine ⟨hdegStmt, ?_⟩
  intro v
  rw [SimpleGraph.degree]
  change degree (IST := IST) c i v ≤ 2
  by_cases hv : IsVertex (IST := IST) c i v
  · rcases hdegStmt.1 v hv with hOne | hTwo
    · omega
    · omega
  · have hNoNeighbors : neighbors (IST := IST) c i v = ∅ := by
      ext w
      constructor
      · intro hw
        exact False.elim (hv (Edge.left_vertex ((mem_neighbors).1 hw)))
      · intro hw
        simp at hw
    rw [degree, hNoNeighbors]
    simp

omit [Inhabited T] in
theorem componentStructure_of_components_have_spanning_paths_or_cycles {c : T → I} {i : I}
    (hdegStmt : DegreeCharacterization (IST := IST) c i)
    (hcomponents :
      PathComponents.ComponentsHaveSpanningPathsOrCycles (graph (IST := IST) c i)) :
    ComponentStructure (IST := IST) c i := by
  exact ⟨hcomponents, hdegStmt.2⟩

/--
Final graph structure statement for $G_i$: its components have spanning
paths or cycles, and its endpoints are exactly the outside door of type $i$
and the colorful rooms.
-/
theorem component_structure (c : T → I) (i : I) :
    ComponentStructure (IST := IST) c i := by
  exact componentStructure_of_components_have_spanning_paths_or_cycles
    (IST := IST)
    (degree_characterization (IST := IST) c i)
    (PathComponents.components_have_spanning_paths_or_cycles_of_degree_le_two
      (graph (IST := IST) c i)
      (pathStructure_of_degreeCharacterization
        (IST := IST) (degree_characterization (IST := IST) c i)).2)

/-- The degree bound as a direct interface, without unpacking `PathStructure`. -/
theorem degree_le_two (c : T → I) (i : I) (v : Cell T I) :
    degree (IST := IST) c i v ≤ 2 :=
  (pathStructure_of_degreeCharacterization
    (degree_characterization (IST := IST) c i)).2 v

/-- An endpoint is an outside typed door or a colorful room. -/
theorem isEndpoint_iff (c : T → I) (i : I) (v : Cell T I) :
    IsEndpoint (IST := IST) c i v ↔
      (IsDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
        IST.isColorful c v.1 v.2 :=
  (degree_characterization (IST := IST) c i).2 v

end ScarfPath
