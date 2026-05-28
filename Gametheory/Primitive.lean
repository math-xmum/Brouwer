import Gametheory.Brouwer

open Classical
open Finset


noncomputable section

namespace IndexedLOrder

variable {T I : Type*} [Inhabited T] [Fintype T] [Fintype I]
variable [DecidableEq T] [DecidableEq I] [IST : IndexedLOrder I T]

/-- The abstract enlargement `T ∪ I` used for Scarf's slack-vector language. -/
abbrev ExtendedGoods (T I : Type*) := Sum T I

/-- Turn a room `(σ, C)` into the corresponding primitive set `σ ∪ (I \ C)`. -/
def toPrimitiveSet (σ : Finset T) (C : Finset I) : Finset (ExtendedGoods T I) :=
  (σ.image Sum.inl) ∪ ((Finset.univ \ C).image Sum.inr)

/-- Turn a door `(τ, D)` into the corresponding almost primitive set `τ ∪ (I \ D)`. -/
def toAlmostPrimitive (τ : Finset T) (D : Finset I) : Finset (ExtendedGoods T I) :=
  toPrimitiveSet (I := I) τ D

/-- The goods part of a subset of `T ∪ I`. -/
def fromGoods (X : Finset (ExtendedGoods T I)) : Finset T :=
  Finset.univ.filter (fun t : T => Sum.inl t ∈ X)

/-- The indices whose slack vectors are missing from a subset of `T ∪ I`. -/
def fromMissing (X : Finset (ExtendedGoods T I)) : Finset I :=
  Finset.univ.filter (fun i : I => Sum.inr i ∉ X)

omit [Inhabited T] [Fintype T] IST in
@[simp] lemma mem_toPrimitiveSet_inl {σ : Finset T} {C : Finset I} {t : T} :
    Sum.inl t ∈ toPrimitiveSet (I := I) σ C ↔ t ∈ σ := by
  simp [toPrimitiveSet]

omit [Fintype T] IST in
@[simp] lemma mem_toPrimitiveSet_inr {σ : Finset T} {C : Finset I} {i : I} :
    Sum.inr i ∈ toPrimitiveSet (T := T) σ C ↔ i ∉ C := by
  simp [toPrimitiveSet]

omit [Inhabited T] [Fintype T] IST in
@[simp] lemma mem_toAlmostPrimitive_inl {τ : Finset T} {D : Finset I} {t : T} :
    Sum.inl t ∈ toAlmostPrimitive (I := I) τ D ↔ t ∈ τ := by
  simp [toAlmostPrimitive]

omit [Fintype T] IST in
@[simp] lemma mem_toAlmostPrimitive_inr {τ : Finset T} {D : Finset I} {i : I} :
    Sum.inr i ∈ toAlmostPrimitive (T := T) τ D ↔ i ∉ D := by
  simp [toAlmostPrimitive]

omit [Inhabited T] [Fintype I] IST in
@[simp] lemma mem_fromGoods {X : Finset (ExtendedGoods T I)} {t : T} :
    t ∈ fromGoods (T := T) (I := I) X ↔ Sum.inl t ∈ X := by
  simp [fromGoods]

omit [Inhabited T] [Fintype T] IST in
@[simp] lemma mem_fromMissing {X : Finset (ExtendedGoods T I)} {i : I} :
    i ∈ fromMissing (T := T) (I := I) X ↔ Sum.inr i ∉ X := by
  simp [fromMissing]

omit [Inhabited T] IST in
@[simp] lemma fromGoods_toPrimitiveSet (σ : Finset T) (C : Finset I) :
    fromGoods (T := T) (I := I) (toPrimitiveSet (I := I) σ C) = σ := by
  ext t
  simp

omit [Fintype T] IST in
@[simp] lemma fromMissing_toPrimitiveSet (σ : Finset T) (C : Finset I) :
    fromMissing (T := T) (I := I) (toPrimitiveSet (I := I) σ C) = C := by
  ext i
  simp

omit [Inhabited T] IST in
@[simp] lemma fromGoods_toAlmostPrimitive (τ : Finset T) (D : Finset I) :
    fromGoods (T := T) (I := I) (toAlmostPrimitive (I := I) τ D) = τ := by
  simp [toAlmostPrimitive]

omit [Fintype T] IST in
@[simp] lemma fromMissing_toAlmostPrimitive (τ : Finset T) (D : Finset I) :
    fromMissing (T := T) (I := I) (toAlmostPrimitive (I := I) τ D) = D := by
  simp [toAlmostPrimitive]

omit [Inhabited T] [Fintype T] IST in
lemma goods_slacks_disjoint (σ : Finset T) (C : Finset I) :
    Disjoint (σ.image Sum.inl) ((Finset.univ \ C).image Sum.inr) := by
  rw [Finset.disjoint_left]
  intro x hxGoods hxSlack
  rcases Finset.mem_image.mp hxGoods with ⟨t, _, rfl⟩
  rcases Finset.mem_image.mp hxSlack with ⟨i, _, h⟩
  cases h

omit [Inhabited T] [Fintype T] IST in
lemma card_toPrimitiveSet (σ : Finset T) (C : Finset I) :
    (toPrimitiveSet (I := I) σ C).card = σ.card + (Finset.univ \ C).card := by
  rw [toPrimitiveSet, Finset.card_union_of_disjoint (goods_slacks_disjoint σ C)]
  have hGoods : (σ.image (Sum.inl : T → ExtendedGoods T I)).card = σ.card := by
    apply Finset.card_image_of_injOn
    intro a _ b _ h
    exact Sum.inl.inj h
  have hSlacks :
      (((Finset.univ \ C).image (Sum.inr : I → ExtendedGoods T I)).card =
        (Finset.univ \ C).card) := by
    apply Finset.card_image_of_injOn
    intro a _ b _ h
    exact Sum.inr.inj h
  rw [hGoods, hSlacks]

/-- Scarf primitive sets, stated through the equivalent room language. -/
def isPrimitive (X : Finset (ExtendedGoods T I)) : Prop :=
  ∃ σ C, IST.isRoom σ C ∧ X = toPrimitiveSet (I := I) σ C

/-- Almost primitive sets, stated through the equivalent door language. -/
def isAlmostPrimitive (Y : Finset (ExtendedGoods T I)) : Prop :=
  ∃ τ D σ C,
    IST.isDoorof τ D σ C ∧
      Y = toAlmostPrimitive (I := I) τ D

omit [Inhabited T] [Fintype T] in
/-- A primitive set can be represented by the room from which it was built. -/
lemma room_to_primitive {σ : Finset T} {C : Finset I} (h : IST.isRoom σ C) :
    isPrimitive (IST := IST) (toPrimitiveSet (I := I) σ C) := by
  exact ⟨σ, C, h, rfl⟩

/-- Extract the room corresponding to a primitive set. -/
lemma primitive_to_room {X : Finset (ExtendedGoods T I)} (h : isPrimitive (IST := IST) X) :
    IST.isRoom (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  rcases h with ⟨σ, C, hRoom, rfl⟩
  simpa using hRoom

lemma primitive_eq_toPrimitive_from_parts {X : Finset (ExtendedGoods T I)}
    (h : isPrimitive (IST := IST) X) :
    X = toPrimitiveSet (I := I)
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  rcases h with ⟨σ, C, _hRoom, rfl⟩
  simp

/-- A room recovered from a primitive set is again primitive. -/
lemma primitive_from_parts {X : Finset (ExtendedGoods T I)}
    (h : isPrimitive (IST := IST) X) :
    isPrimitive (IST := IST)
      (toPrimitiveSet (I := I)
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X)) := by
  exact room_to_primitive (primitive_to_room h)

omit [Inhabited T] [Fintype T] in
/-- A door of a room gives an almost primitive set. -/
lemma door_to_almostPrimitive {τ σ : Finset T} {D C : Finset I}
    (h : IST.isDoorof τ D σ C) :
    isAlmostPrimitive (IST := IST) (toAlmostPrimitive (I := I) τ D) := by
  exact ⟨τ, D, σ, C, h, rfl⟩

/-- Recover the door represented by an almost primitive set. -/
lemma almostPrimitive_to_door {Y : Finset (ExtendedGoods T I)}
    (h : isAlmostPrimitive (IST := IST) Y) :
    IST.isDoor (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y) := by
  rcases h with ⟨τ, D, σ, C, hDoor, rfl⟩
  cases hDoor with
  | idoor _ hD _ _ _ _ => simpa using hD
  | odoor _ hD _ _ _ _ => simpa using hD

/-- Recover a room incident to an almost primitive set. -/
lemma almostPrimitive_incident_room {Y : Finset (ExtendedGoods T I)}
    (h : isAlmostPrimitive (IST := IST) Y) :
    ∃ σ C,
      IST.isDoorof (fromGoods (T := T) (I := I) Y)
        (fromMissing (T := T) (I := I) Y) σ C := by
  rcases h with ⟨τ, D, σ, C, hDoor, rfl⟩
  exact ⟨σ, C, by simpa using hDoor⟩

omit [Fintype T] in
/-- Incidence of doors and rooms becomes subset inclusion of the corresponding sets. -/
lemma doorof_toAlmost_subset_toPrimitive {τ σ : Finset T} {D C : Finset I}
    (h : IST.isDoorof τ D σ C) :
    toAlmostPrimitive (I := I) τ D ⊆ toPrimitiveSet (I := I) σ C := by
  intro z hz
  cases z with
  | inl t =>
      cases h with
      | idoor _ _ _ _ hInsert hD =>
          rw [mem_toAlmostPrimitive_inl] at hz
          rw [mem_toPrimitiveSet_inl]
          rw [← hInsert]
          exact Finset.mem_insert_of_mem hz
      | odoor _ _ _ hNot hτ hD =>
          rw [mem_toAlmostPrimitive_inl] at hz
          rw [mem_toPrimitiveSet_inl]
          rwa [← hτ]
  | inr i =>
      cases h with
      | idoor _ _ _ _ hInsert hD =>
          rw [mem_toAlmostPrimitive_inr] at hz
          rw [mem_toPrimitiveSet_inr]
          rwa [hD] at hz
      | odoor _ _ j hNot hτ hD =>
          rw [mem_toAlmostPrimitive_inr] at hz
          rw [mem_toPrimitiveSet_inr]
          rw [hD] at hz
          exact fun hiC => hz (Finset.mem_insert_of_mem hiC)

omit [Fintype T] in
/-- A useful packaged form of the door/primitive-set incidence correspondence. -/
lemma doorof_iff_subset_primitive {τ σ : Finset T} {D C : Finset I} :
    IST.isDoorof τ D σ C →
      IST.isRoom σ C ∧
        isAlmostPrimitive (IST := IST) (toAlmostPrimitive (I := I) τ D) ∧
          isPrimitive (IST := IST) (toPrimitiveSet (I := I) σ C) ∧
            toAlmostPrimitive (I := I) τ D ⊆ toPrimitiveSet (I := I) σ C := by
  intro h
  have hRoom : IST.isRoom σ C := IST.isRoom_of_Door h
  exact ⟨hRoom, door_to_almostPrimitive h, room_to_primitive hRoom,
    doorof_toAlmost_subset_toPrimitive h⟩

lemma almostPrimitive_eq_toAlmost_from_parts {Y : Finset (ExtendedGoods T I)}
    (h : isAlmostPrimitive (IST := IST) Y) :
    Y = toAlmostPrimitive (I := I)
      (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y) := by
  rcases h with ⟨τ, D, σ, C, _hDoor, rfl⟩
  simp

/--
Scarf's main lemma for internal almost primitive sets, in the room/door
language: an internal almost primitive face is contained in two distinct
primitive sets.
-/
theorem internal_almostPrimitive_two_incident_primitives {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hInternal : (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃ X₁ X₂ : Finset (ExtendedGoods T I),
      X₁ ≠ X₂ ∧
        isPrimitive (IST := IST) X₁ ∧
        isPrimitive (IST := IST) X₂ ∧
        Y ⊆ X₁ ∧
        Y ⊆ X₂ := by
  let τ := fromGoods (T := T) (I := I) Y
  let D := fromMissing (T := T) (I := I) Y
  have hDoor : IST.isDoor τ D := almostPrimitive_to_door hY
  obtain ⟨σ₁, σ₂, C₁, C₂, hNe, hRoom₁, hRoom₂, hDoor₁, hDoor₂, _hUnique⟩ :=
    IST.internal_door_two_rooms τ D ⟨hDoor, hInternal⟩
  let X₁ := toPrimitiveSet (I := I) σ₁ C₁
  let X₂ := toPrimitiveSet (I := I) σ₂ C₂
  refine ⟨X₁, X₂, ?_, room_to_primitive hRoom₁, room_to_primitive hRoom₂, ?_, ?_⟩
  · intro hEq
    have hσ : σ₁ = σ₂ := by
      have := congrArg (fromGoods (T := T) (I := I)) hEq
      simpa [X₁, X₂] using this
    have hC : C₁ = C₂ := by
      have := congrArg (fromMissing (T := T) (I := I)) hEq
      simpa [X₁, X₂] using this
    exact hNe (by simp [hσ, hC])
  · rw [almostPrimitive_eq_toAlmost_from_parts hY]
    exact doorof_toAlmost_subset_toPrimitive hDoor₁
  · rw [almostPrimitive_eq_toAlmost_from_parts hY]
    exact doorof_toAlmost_subset_toPrimitive hDoor₂

/-- The boundary almost primitive set made only of slacks, missing `i`. -/
def slackBoundary (i : I) : Finset (ExtendedGoods T I) :=
  toAlmostPrimitive (T := T) (Finset.empty : Finset T) ({i} : Finset I)

/-- Each slack boundary is an almost primitive set. -/
lemma slackBoundary_isAlmostPrimitive (i : I) :
    isAlmostPrimitive (IST := IST) (slackBoundary (T := T) (I := I) i) := by
  have hOutside : IST.isOutsideDoor (Finset.empty : Finset T) ({i} : Finset I) :=
    IST.outsidedoor_singleton i
  let xMax : T := @Finset.max' T (IST i) Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨(default : T)⟩)
  have hCell : IST.isCell ({xMax} : Finset T) ({i} : Finset I) := by
    intro y
    refine ⟨i, by simp, ?_⟩
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
  have hDoorof : IST.isDoorof (Finset.empty : Finset T) ({i} : Finset I)
      ({xMax} : Finset T) ({i} : Finset I) := by
    apply isDoorof.idoor hCell hOutside.1 xMax
    · exact Finset.notMem_empty xMax
    · rfl
    · rfl
  exact door_to_almostPrimitive hDoorof

/-- Extend a coloring of goods by coloring each slack vector by its own index. -/
def extendedColoring (c : T → I) : ExtendedGoods T I → I
  | Sum.inl t => c t
  | Sum.inr i => i

omit [Fintype T] IST in
lemma image_extendedColoring_toPrimitiveSet (c : T → I) (σ : Finset T) (C : Finset I) :
    (toPrimitiveSet (I := I) σ C).image (extendedColoring (T := T) (I := I) c) =
      (σ.image c) ∪ (Finset.univ \ C) := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨x, hx, rfl⟩
    cases x with
    | inl t =>
        rw [mem_toPrimitiveSet_inl] at hx
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem c hx)
    | inr j =>
        rw [mem_toPrimitiveSet_inr] at hx
        exact Finset.mem_union_right _ (by simpa [extendedColoring] using hx)
  · intro hi
    rcases Finset.mem_union.mp hi with hImage | hSlack
    · rcases Finset.mem_image.mp hImage with ⟨t, ht, rfl⟩
      exact Finset.mem_image_of_mem (extendedColoring (T := T) (I := I) c)
        (show Sum.inl t ∈ toPrimitiveSet (I := I) σ C by
          rw [mem_toPrimitiveSet_inl]
          exact ht)
    · exact Finset.mem_image_of_mem (extendedColoring (T := T) (I := I) c)
        (show Sum.inr i ∈ toPrimitiveSet (T := T) σ C by
          rw [mem_toPrimitiveSet_inr]
          exact (Finset.mem_sdiff.mp hSlack).2)

omit [Fintype T] in
/--
For a room, Scarf's statement that a primitive set has all colors is exactly
the Section 1 statement that the corresponding room is colorful.
-/
lemma full_color_primitive_iff_colorful_room (c : T → I) {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) :
    (toPrimitiveSet (I := I) σ C).image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ : Finset I) ↔
      IST.isColorful c σ C := by
  constructor
  · intro hFull
    have hUnion : (σ.image c) ∪ (Finset.univ \ C) = (Finset.univ : Finset I) := by
      simpa [image_extendedColoring_toPrimitiveSet] using hFull
    have hC_subset_image : C ⊆ σ.image c := by
      intro i hiC
      have hiUnion : i ∈ (σ.image c) ∪ (Finset.univ \ C) := by
        rw [hUnion]
        exact Finset.mem_univ i
      rcases Finset.mem_union.mp hiUnion with hiImage | hiCompl
      · exact hiImage
      · exact False.elim ((Finset.mem_sdiff.mp hiCompl).2 hiC)
    have hImage_card_le_C : (σ.image c).card ≤ C.card := by
      calc
        (σ.image c).card ≤ σ.card := Finset.card_image_le
        _ = C.card := hRoom.2.symm
    exact ⟨hRoom.1, (Finset.eq_of_subset_of_card_le hC_subset_image hImage_card_le_C).symm⟩
  · intro hColorful
    rw [image_extendedColoring_toPrimitiveSet, hColorful.2]
    exact Finset.union_sdiff_self_eq_union.symm.trans (by simp)

/--
Utility functions realize the abstract preference orders when they preserve
and reflect each indexed strict order.
-/
structure UtilityRealization (u : I → T → ℝ) : Prop where
  order_iff : ∀ i x y, (IST i).lt x y ↔ u i x < u i y

/-- Positive utility functions, matching the economic convention in §3. -/
structure PositiveUtilityRealization (u : I → T → ℝ) : Prop extends
    UtilityRealization (IST := IST) u where
  positive : ∀ i x, 0 < u i x

/--
The coordinate model of Scarf's slack vector for face `i`: the `i`th
coordinate is zero and all other coordinates are the chosen large value `M i`.
-/
def slackVector (M : I → ℝ) (i : I) : I → ℝ :=
  fun j => if j = i then 0 else M i

omit [Fintype I] in
@[simp] lemma slackVector_self (M : I → ℝ) (i : I) :
    slackVector (I := I) M i i = 0 := by
  simp [slackVector]

omit [Fintype I] in
@[simp] lemma slackVector_of_ne (M : I → ℝ) {i j : I} (h : j ≠ i) :
    slackVector (I := I) M i j = M i := by
  simp [slackVector, h]

end IndexedLOrder

end
