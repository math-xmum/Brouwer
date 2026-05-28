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

omit [Inhabited T] IST in
lemma eq_toPrimitive_from_parts (X : Finset (ExtendedGoods T I)) :
    X = toPrimitiveSet (I := I)
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  ext x
  cases x with
  | inl t => simp
  | inr i => simp [toPrimitiveSet, fromMissing]

omit [Inhabited T] IST in
lemma eq_toAlmost_from_parts (X : Finset (ExtendedGoods T I)) :
    X = toAlmostPrimitive (I := I)
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  simpa [toAlmostPrimitive] using
    (eq_toPrimitive_from_parts (T := T) (I := I) X)

omit [Inhabited T] [Fintype T] in
lemma card_toPrimitiveSet_of_room {σ : Finset T} {C : Finset I} (hRoom : IST.isRoom σ C) :
    (toPrimitiveSet (I := I) σ C).card = Fintype.card I := by
  rw [card_toPrimitiveSet, ← hRoom.2, Finset.card_sdiff_of_subset (Finset.subset_univ C),
    Finset.card_univ]
  have hCle : C.card ≤ Fintype.card I := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ C)
  omega

omit [Inhabited T] [Fintype T] in
lemma card_toAlmostPrimitive_of_door {τ : Finset T} {D : Finset I} (hDoor : IST.isDoor τ D) :
    (toAlmostPrimitive (I := I) τ D).card + 1 = Fintype.card I := by
  rw [toAlmostPrimitive, card_toPrimitiveSet,
    Finset.card_sdiff_of_subset (Finset.subset_univ D), Finset.card_univ]
  have hDle : D.card ≤ Fintype.card I := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ D)
  omega

omit [Inhabited T] [Fintype T] IST in
lemma exists_insert_eq_of_subset_card_eq_succ {α : Type*} [DecidableEq α]
    {s t : Finset α} (hsub : s ⊆ t) (hcard : t.card = s.card + 1) :
    ∃ x, x ∉ s ∧ insert x s = t := by
  have hdiff_card : (t \ s).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiff_card
  have hxmem : x ∈ t \ s := by
    rw [hx]
    simp
  refine ⟨x, (Finset.mem_sdiff.mp hxmem).2, ?_⟩
  calc
    insert x s = {x} ∪ s := rfl
    _ = (t \ s) ∪ s := by rw [hx]
    _ = t := Finset.sdiff_union_of_subset hsub

/-- Scarf primitive sets, stated through the equivalent room language. -/
def isPrimitive (X : Finset (ExtendedGoods T I)) : Prop :=
  ∃ σ C, IST.isRoom σ C ∧ X = toPrimitiveSet (I := I) σ C

/--
Primitive sets in the paper's native dominance form, using the characterization
`X` primitive iff `X ∩ T` is dominant with respect to the missing slack indices.
-/
def isPrimitiveNative (X : Finset (ExtendedGoods T I)) : Prop :=
  X.card = Fintype.card I ∧
    IST.isDominant (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X)

/-- Almost primitive sets, stated through the equivalent door language. -/
def isAlmostPrimitive (Y : Finset (ExtendedGoods T I)) : Prop :=
  ∃ τ D σ C,
    IST.isDoorof τ D σ C ∧
      Y = toAlmostPrimitive (I := I) τ D

/-- Almost primitive sets in the paper's native form: an `(n-1)`-face contained in a primitive set. -/
def isAlmostPrimitiveNative (Y : Finset (ExtendedGoods T I)) : Prop :=
  Y.card + 1 = Fintype.card I ∧ ∃ X, isPrimitive (IST := IST) X ∧ Y ⊆ X

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

omit [Inhabited T] in
lemma primitive_eq_toPrimitive_from_parts {X : Finset (ExtendedGoods T I)}
    (_h : isPrimitive (IST := IST) X) :
    X = toPrimitiveSet (I := I)
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  exact eq_toPrimitive_from_parts X

/-- A room recovered from a primitive set is again primitive. -/
lemma primitive_from_parts {X : Finset (ExtendedGoods T I)}
    (h : isPrimitive (IST := IST) X) :
    isPrimitive (IST := IST)
      (toPrimitiveSet (I := I)
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X)) := by
  exact room_to_primitive (primitive_to_room h)

lemma primitive_to_nativePrimitive {X : Finset (ExtendedGoods T I)}
    (h : isPrimitive (IST := IST) X) :
    isPrimitiveNative (IST := IST) X := by
  constructor
  · rcases h with ⟨σ, C, hRoom, rfl⟩
    exact card_toPrimitiveSet_of_room hRoom
  · exact (primitive_to_room h).1

omit [Inhabited T] in
lemma nativePrimitive_to_primitive {X : Finset (ExtendedGoods T I)}
    (h : isPrimitiveNative (IST := IST) X) :
    isPrimitive (IST := IST) X := by
  rcases h with ⟨hCard, hDom⟩
  let σ := fromGoods (T := T) (I := I) X
  let C := fromMissing (T := T) (I := I) X
  have hXcard : X.card = σ.card + (Finset.univ \ C).card := by
    rw [eq_toPrimitive_from_parts (T := T) (I := I) X, card_toPrimitiveSet]
  have hCcard : C.card = σ.card := by
    rw [hXcard, Finset.card_sdiff_of_subset (Finset.subset_univ C),
      Finset.card_univ] at hCard
    have hCle : C.card ≤ Fintype.card I := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ C)
    omega
  have hRoom : IST.isRoom σ C := ⟨hDom, hCcard⟩
  rw [eq_toPrimitive_from_parts (T := T) (I := I) X]
  exact room_to_primitive hRoom

theorem isPrimitive_iff_native {X : Finset (ExtendedGoods T I)} :
    isPrimitive (IST := IST) X ↔ isPrimitiveNative (IST := IST) X :=
  ⟨primitive_to_nativePrimitive, nativePrimitive_to_primitive⟩

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

omit [Inhabited T] in
lemma almostPrimitive_eq_toAlmost_from_parts {Y : Finset (ExtendedGoods T I)}
    (_h : isAlmostPrimitive (IST := IST) Y) :
    Y = toAlmostPrimitive (I := I)
      (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y) := by
  exact eq_toAlmost_from_parts Y

omit [Fintype T] in
lemma subset_toPrimitive_toAlmost_doorof {τ σ : Finset T} {D C : Finset I}
    (hDoor : IST.isDoor τ D) (hRoom : IST.isRoom σ C)
    (hsub : toAlmostPrimitive (I := I) τ D ⊆ toPrimitiveSet (I := I) σ C) :
    IST.isDoorof τ D σ C := by
  have hτsub : τ ⊆ σ := by
    intro t ht
    have hmem : Sum.inl t ∈ toPrimitiveSet (I := I) σ C :=
      hsub (by simpa using ht)
    simpa using hmem
  have hCsubD : C ⊆ D := by
    intro i hiC
    by_contra hiD
    have hmem : Sum.inr i ∈ toPrimitiveSet (T := T) σ C :=
      hsub (by simpa using hiD)
    have hiNotC : i ∉ C := by simpa using hmem
    exact hiNotC hiC
  have hτleσ : τ.card ≤ σ.card := Finset.card_le_card hτsub
  have hσleτsucc : σ.card ≤ τ.card + 1 := by
    calc
      σ.card = C.card := hRoom.2.symm
      _ ≤ D.card := Finset.card_le_card hCsubD
      _ = τ.card + 1 := hDoor.2
  have hCases : σ.card = τ.card ∨ σ.card = τ.card + 1 := by
    omega
  cases hCases with
  | inl hEq =>
      have hτσ : τ = σ := Finset.eq_of_subset_of_card_le hτsub (by omega)
      have hDcard : D.card = C.card + 1 := by
        omega
      obtain ⟨j, hjC, hjInsert⟩ := exists_insert_eq_of_subset_card_eq_succ hCsubD hDcard
      apply isDoorof.odoor hRoom.1 hDoor j hjC
      · exact hτσ
      · exact hjInsert.symm
  | inr hSucc =>
      have hCD : C = D := by
        apply Finset.eq_of_subset_of_card_le hCsubD
        omega
      obtain ⟨x, hxτ, hxInsert⟩ := exists_insert_eq_of_subset_card_eq_succ hτsub hSucc
      apply isDoorof.idoor hRoom.1 hDoor x hxτ
      · exact hxInsert
      · exact hCD.symm

lemma nativeAlmostPrimitive_to_almostPrimitive {Y : Finset (ExtendedGoods T I)}
    (h : isAlmostPrimitiveNative (IST := IST) Y) :
    isAlmostPrimitive (IST := IST) Y := by
  rcases h with ⟨hcard, X, hPrim, hsub⟩
  rcases hPrim with ⟨σ, C, hRoom, rfl⟩
  let τ := fromGoods (T := T) (I := I) Y
  let D := fromMissing (T := T) (I := I) Y
  have hYeq : Y = toAlmostPrimitive (I := I) τ D := eq_toAlmost_from_parts Y
  have hτsub : τ ⊆ σ := by
    intro t ht
    have hy : Sum.inl t ∈ Y := by simpa [τ] using ht
    have hx : Sum.inl t ∈ toPrimitiveSet (I := I) σ C := hsub hy
    simpa using hx
  have hCsubD : C ⊆ D := by
    intro i hiC
    rw [mem_fromMissing]
    intro hy
    have hx : Sum.inr i ∈ toPrimitiveSet (T := T) σ C := hsub hy
    have hiNotC : i ∉ C := by simpa using hx
    exact hiNotC hiC
  have hCell : IST.isCell τ D := by
    exact IST.Dominant_of_supset τ C D hCsubD
      (IST.Dominant_of_subset σ τ C hτsub hRoom.1)
  have hDoor : IST.isDoor τ D := by
    constructor
    · exact hCell
    · have hYcard :
          Y.card = τ.card + (Finset.univ \ D).card := by
        rw [hYeq, toAlmostPrimitive, card_toPrimitiveSet]
      rw [hYcard, Finset.card_sdiff_of_subset (Finset.subset_univ D),
        Finset.card_univ] at hcard
      have hDle : D.card ≤ Fintype.card I := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ D)
      omega
  have hsubParts : toAlmostPrimitive (I := I) τ D ⊆ toPrimitiveSet (I := I) σ C := by
    rw [← hYeq]
    exact hsub
  exact ⟨τ, D, σ, C, subset_toPrimitive_toAlmost_doorof hDoor hRoom hsubParts, hYeq⟩

omit [Fintype T] in
lemma almostPrimitive_to_nativeAlmostPrimitive {Y : Finset (ExtendedGoods T I)}
    (h : isAlmostPrimitive (IST := IST) Y) :
    isAlmostPrimitiveNative (IST := IST) Y := by
  rcases h with ⟨τ, D, σ, C, hDoorof, rfl⟩
  have hDoor : IST.isDoor τ D := by
    cases hDoorof with
    | idoor _ hD _ _ _ _ => exact hD
    | odoor _ hD _ _ _ _ => exact hD
  have hRoom : IST.isRoom σ C := IST.isRoom_of_Door hDoorof
  constructor
  · exact card_toAlmostPrimitive_of_door hDoor
  · exact ⟨toPrimitiveSet (I := I) σ C, room_to_primitive hRoom,
      doorof_toAlmost_subset_toPrimitive hDoorof⟩

theorem isAlmostPrimitive_iff_native {Y : Finset (ExtendedGoods T I)} :
    isAlmostPrimitive (IST := IST) Y ↔ isAlmostPrimitiveNative (IST := IST) Y :=
  ⟨almostPrimitive_to_nativeAlmostPrimitive, nativeAlmostPrimitive_to_almostPrimitive⟩

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

theorem internal_almostPrimitive_exactly_two_incident_primitives
    {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hInternal : (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃ X₁ X₂ : Finset (ExtendedGoods T I),
      X₁ ≠ X₂ ∧
        isPrimitive (IST := IST) X₁ ∧
        isPrimitive (IST := IST) X₂ ∧
        Y ⊆ X₁ ∧
        Y ⊆ X₂ ∧
        ∀ X, isPrimitive (IST := IST) X → Y ⊆ X → X = X₁ ∨ X = X₂ := by
  let τ := fromGoods (T := T) (I := I) Y
  let D := fromMissing (T := T) (I := I) Y
  have hDoor : IST.isDoor τ D := almostPrimitive_to_door hY
  obtain ⟨σ₁, σ₂, C₁, C₂, hNe, hRoom₁, hRoom₂, hDoor₁, hDoor₂, hUnique⟩ :=
    IST.internal_door_two_rooms τ D ⟨hDoor, hInternal⟩
  let X₁ := toPrimitiveSet (I := I) σ₁ C₁
  let X₂ := toPrimitiveSet (I := I) σ₂ C₂
  refine ⟨X₁, X₂, ?_, room_to_primitive hRoom₁, room_to_primitive hRoom₂, ?_, ?_, ?_⟩
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
  · intro X hX hSub
    have hDoorX :
        IST.isDoorof τ D (fromGoods (T := T) (I := I) X)
          (fromMissing (T := T) (I := I) X) := by
      have hRoomX : IST.isRoom (fromGoods (T := T) (I := I) X)
          (fromMissing (T := T) (I := I) X) := primitive_to_room hX
      apply subset_toPrimitive_toAlmost_doorof hDoor hRoomX
      rw [← almostPrimitive_eq_toAlmost_from_parts hY, ← primitive_eq_toPrimitive_from_parts hX]
      exact hSub
    have hRoomX : IST.isRoom (fromGoods (T := T) (I := I) X)
        (fromMissing (T := T) (I := I) X) := primitive_to_room hX
    obtain hLeft | hRight := hUnique
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) hRoomX hDoorX
    · left
      rw [primitive_eq_toPrimitive_from_parts hX, hLeft.1, hLeft.2]
    · right
      rw [primitive_eq_toPrimitive_from_parts hX, hRight.1, hRight.2]

theorem native_internal_almostPrimitive_exactly_two_incident_primitives
    {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitiveNative (IST := IST) Y)
    (hInternal : (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃ X₁ X₂ : Finset (ExtendedGoods T I),
      X₁ ≠ X₂ ∧
        isPrimitiveNative (IST := IST) X₁ ∧
        isPrimitiveNative (IST := IST) X₂ ∧
        Y ⊆ X₁ ∧
        Y ⊆ X₂ ∧
        ∀ X, isPrimitiveNative (IST := IST) X → Y ⊆ X → X = X₁ ∨ X = X₂ := by
  have hY' : isAlmostPrimitive (IST := IST) Y :=
    nativeAlmostPrimitive_to_almostPrimitive hY
  obtain ⟨X₁, X₂, hNe, hPrim₁, hPrim₂, hSub₁, hSub₂, hUnique⟩ :=
    internal_almostPrimitive_exactly_two_incident_primitives hY' hInternal
  exact ⟨X₁, X₂, hNe, primitive_to_nativePrimitive hPrim₁,
    primitive_to_nativePrimitive hPrim₂, hSub₁, hSub₂, fun X hX hSub =>
      hUnique X (nativePrimitive_to_primitive hX) hSub⟩

/--
Native Scarf main lemma in the "remove one point" form: after removing a
point from a primitive set, either the resulting face lies in the slack
boundary, or there is a unique other primitive set containing that face.
-/
theorem native_primitive_erase_mainLemma
    {X : Finset (ExtendedGoods T I)} (hX : isPrimitiveNative (IST := IST) X)
    {x : ExtendedGoods T I} (hx : x ∈ X) :
    ¬ (fromGoods (T := T) (I := I) (X.erase x)).Nonempty ∨
      ∃! X' : Finset (ExtendedGoods T I),
        isPrimitiveNative (IST := IST) X' ∧
          X.erase x ⊆ X' ∧ X' ≠ X := by
  let Y := X.erase x
  have hYnative : isAlmostPrimitiveNative (IST := IST) Y := by
    constructor
    · have hcardErase : Y.card + 1 = X.card := by
        change (X.erase x).card + 1 = X.card
        rw [Finset.card_erase_of_mem hx]
        have hpos : 0 < X.card := Finset.card_pos.mpr ⟨x, hx⟩
        omega
      exact hcardErase.trans hX.1
    · exact ⟨X, nativePrimitive_to_primitive hX, Finset.erase_subset x X⟩
  by_cases hInternal : (fromGoods (T := T) (I := I) Y).Nonempty
  · right
    obtain ⟨X₁, X₂, hNe, hPrim₁, hPrim₂, hSub₁, hSub₂, hUnique⟩ :=
      native_internal_almostPrimitive_exactly_two_incident_primitives hYnative hInternal
    have hXmem := hUnique X hX (Finset.erase_subset x X)
    rcases hXmem with hXX₁ | hXX₂
    · refine ⟨X₂, ⟨hPrim₂, hSub₂, ?_⟩, ?_⟩
      · intro hX₂
        exact hNe (hXX₁.symm.trans hX₂.symm)
      · intro Z hZ
        rcases hZ with ⟨hPrimZ, hSubZ, hZneX⟩
        rcases hUnique Z hPrimZ hSubZ with hZ₁ | hZ₂
        · exfalso
          exact hZneX (hZ₁.trans hXX₁.symm)
        · exact hZ₂
    · refine ⟨X₁, ⟨hPrim₁, hSub₁, ?_⟩, ?_⟩
      · intro hX₁
        exact hNe (hX₁.trans hXX₂)
      · intro Z hZ
        rcases hZ with ⟨hPrimZ, hSubZ, hZneX⟩
        rcases hUnique Z hPrimZ hSubZ with hZ₁ | hZ₂
        · exact hZ₁
        · exfalso
          exact hZneX (hZ₂.trans hXX₂.symm)
  · left
    exact hInternal

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

lemma slackBoundary_unique_incident_primitive (i : I) :
    ∃! X : Finset (ExtendedGoods T I),
      isPrimitive (IST := IST) X ∧ slackBoundary (T := T) (I := I) i ⊆ X := by
  let xMax : T := @Finset.max' T (IST i) Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨(default : T)⟩)
  let X₀ := toPrimitiveSet (I := I) ({xMax} : Finset T) ({i} : Finset I)
  have hOutside : IST.isOutsideDoor (Finset.empty : Finset T) ({i} : Finset I) :=
    IST.outsidedoor_singleton i
  have hCell : IST.isCell ({xMax} : Finset T) ({i} : Finset I) := by
    intro y
    refine ⟨i, by simp, ?_⟩
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
  have hDoorof₀ : IST.isDoorof (Finset.empty : Finset T) ({i} : Finset I)
      ({xMax} : Finset T) ({i} : Finset I) := by
    apply isDoorof.idoor hCell hOutside.1 xMax
    · exact Finset.notMem_empty xMax
    · rfl
    · rfl
  have hRoom₀ : IST.isRoom ({xMax} : Finset T) ({i} : Finset I) := IST.isRoom_of_Door hDoorof₀
  refine ⟨X₀, ⟨room_to_primitive hRoom₀, ?_⟩, ?_⟩
  · exact doorof_toAlmost_subset_toPrimitive hDoorof₀
  · intro X hX
    rcases hX with ⟨hPrim, hSub⟩
    rcases hPrim with ⟨σ, C, hRoom, rfl⟩
    have hDoorof : IST.isDoorof (Finset.empty : Finset T) ({i} : Finset I) σ C :=
      subset_toPrimitive_toAlmost_doorof hOutside.1 hRoom hSub
    cases hDoorof with
    | idoor hCellσC _ x _ hInsert hD_eq =>
        have hσ : σ = ({x} : Finset T) := by
          simpa using hInsert.symm
        have hC : C = ({i} : Finset I) := hD_eq.symm
        have hx_eq : x = xMax := by
          have hAbove : ∀ y : T, (IST i).le y x := by
            intro y
            obtain ⟨j, hj, hle⟩ := hCellσC y
            have hji : j = i := by
              rw [hC] at hj
              exact Finset.mem_singleton.mp hj
            subst hji
            apply hle
            rw [hσ]
            simp
          have hx_le_max : (IST i).le x xMax :=
            @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
          have hmax_le_x : (IST i).le xMax x := hAbove xMax
          exact @le_antisymm T (IST i).toPartialOrder x xMax hx_le_max hmax_le_x
        rw [hσ, hC, hx_eq]
    | odoor _ _ j _ hτ_eq _ =>
        exfalso
        have hσNonempty : σ.Nonempty := IST.sigma_nonempty_of_room hRoom
        rw [← hτ_eq] at hσNonempty
        exact Finset.not_nonempty_empty hσNonempty

/--
Incidence between an almost primitive face and a primitive set is exactly
the old room-door incidence after translating both sides back to `(goods, indices)`.
-/
lemma almostPrimitive_subset_primitive_iff_doorof
    {Y X : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y) (hX : isPrimitive (IST := IST) X) :
    Y ⊆ X ↔
      IST.isDoorof (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y)
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  constructor
  · intro hSub
    have hDoor : IST.isDoor (fromGoods (T := T) (I := I) Y)
        (fromMissing (T := T) (I := I) Y) := almostPrimitive_to_door hY
    have hRoom : IST.isRoom (fromGoods (T := T) (I := I) X)
        (fromMissing (T := T) (I := I) X) := primitive_to_room hX
    apply subset_toPrimitive_toAlmost_doorof hDoor hRoom
    rw [← almostPrimitive_eq_toAlmost_from_parts hY, ← primitive_eq_toPrimitive_from_parts hX]
    exact hSub
  · intro hDoorof
    rw [almostPrimitive_eq_toAlmost_from_parts hY, primitive_eq_toPrimitive_from_parts hX]
    exact doorof_toAlmost_subset_toPrimitive hDoorof

/--
A Scarf replacement step: two primitive sets are adjacent if they share an
almost primitive face. This is the primitive-set version of walking through a
door from one room to another.
-/
def primitiveReplacementStep (X X' : Finset (ExtendedGoods T I)) : Prop :=
  isPrimitive (IST := IST) X ∧
    isPrimitive (IST := IST) X' ∧
      X ≠ X' ∧
        ∃ Y, isAlmostPrimitive (IST := IST) Y ∧ Y ⊆ X ∧ Y ⊆ X'

omit [Inhabited T] [Fintype T] in
lemma primitiveReplacementStep.symm {X X' : Finset (ExtendedGoods T I)}
    (h : primitiveReplacementStep (IST := IST) X X') :
    primitiveReplacementStep (IST := IST) X' X := by
  rcases h with ⟨hX, hX', hne, Y, hY, hYX, hYX'⟩
  exact ⟨hX', hX, hne.symm, Y, hY, hYX', hYX⟩

lemma replacementStep_has_common_door {X X' : Finset (ExtendedGoods T I)}
    (h : primitiveReplacementStep (IST := IST) X X') :
    ∃ Y,
      isAlmostPrimitive (IST := IST) Y ∧
      Y ⊆ X ∧ Y ⊆ X' ∧
      IST.isDoorof (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y)
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) ∧
      IST.isDoorof (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y)
        (fromGoods (T := T) (I := I) X') (fromMissing (T := T) (I := I) X') := by
  rcases h with ⟨hX, hX', _hne, Y, hY, hYX, hYX'⟩
  exact ⟨Y, hY, hYX, hYX',
    (almostPrimitive_subset_primitive_iff_doorof hY hX).mp hYX,
    (almostPrimitive_subset_primitive_iff_doorof hY hX').mp hYX'⟩

lemma common_door_gives_replacementStep
    {τ : Finset T} {D : Finset I} {σ₁ σ₂ : Finset T} {C₁ C₂ : Finset I}
    (hDoor₁ : IST.isDoorof τ D σ₁ C₁)
    (hDoor₂ : IST.isDoorof τ D σ₂ C₂)
    (hNe : (σ₁, C₁) ≠ (σ₂, C₂)) :
    primitiveReplacementStep (IST := IST)
      (toPrimitiveSet (I := I) σ₁ C₁) (toPrimitiveSet (I := I) σ₂ C₂) := by
  have hRoom₁ : IST.isRoom σ₁ C₁ := IST.isRoom_of_Door hDoor₁
  have hRoom₂ : IST.isRoom σ₂ C₂ := IST.isRoom_of_Door hDoor₂
  refine ⟨room_to_primitive hRoom₁, room_to_primitive hRoom₂, ?_,
    toAlmostPrimitive (I := I) τ D, door_to_almostPrimitive hDoor₁, ?_, ?_⟩
  · intro hEq
    have hσ : σ₁ = σ₂ := by
      have := congrArg (fromGoods (T := T) (I := I)) hEq
      simpa using this
    have hC : C₁ = C₂ := by
      have := congrArg (fromMissing (T := T) (I := I)) hEq
      simpa using this
    exact hNe (by simp [hσ, hC])
  · exact doorof_toAlmost_subset_toPrimitive hDoor₁
  · exact doorof_toAlmost_subset_toPrimitive hDoor₂

theorem internal_almostPrimitive_replacementStep {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hInternal : (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃ X₁ X₂,
      primitiveReplacementStep (IST := IST) X₁ X₂ ∧ Y ⊆ X₁ ∧ Y ⊆ X₂ := by
  obtain ⟨X₁, X₂, hNe, hPrim₁, hPrim₂, hSub₁, hSub₂⟩ :=
    internal_almostPrimitive_two_incident_primitives hY hInternal
  exact ⟨X₁, X₂, ⟨hPrim₁, hPrim₂, hNe, Y, hY, hSub₁, hSub₂⟩, hSub₁, hSub₂⟩

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

/-- The lower contour set of `x` in the order indexed by `i`. -/
def orderLowerSet (i : I) (x : T) : Finset T :=
  letI : LinearOrder T := IST i
  Finset.univ.filter (fun y : T => y ≤ x)

/--
The finite rank utility associated to an indexed order. Adding `1` makes it
positive, matching the economic convention in the paper.
-/
def orderUtility (i : I) (x : T) : ℝ :=
  ((orderLowerSet (IST := IST) i x).card : ℝ) + 1

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_positive (i : I) (x : T) :
    0 < orderUtility (IST := IST) i x := by
  unfold orderUtility
  positivity

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_order_iff (i : I) (x y : T) :
    (IST i).lt x y ↔
      orderUtility (IST := IST) i x < orderUtility (IST := IST) i y := by
  letI : LinearOrder T := IST i
  constructor
  · intro hxy
    unfold orderUtility orderLowerSet
    have hSubset : Finset.univ.filter (fun z : T => z ≤ x) ⊂
        Finset.univ.filter (fun z : T => z ≤ y) := by
      constructor
      · intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, le_trans hz.2 (le_of_lt hxy)⟩
      · intro hEq
        have hy_mem_y : y ∈ Finset.univ.filter (fun z : T => z ≤ y) := by
          simp
        have hy_mem_x : y ∈ Finset.univ.filter (fun z : T => z ≤ x) := by
          exact hEq hy_mem_y
        rw [Finset.mem_filter] at hy_mem_x
        exact not_le_of_gt hxy hy_mem_x.2
    have hCard : (Finset.univ.filter (fun z : T => z ≤ x)).card <
        (Finset.univ.filter (fun z : T => z ≤ y)).card :=
      Finset.card_lt_card hSubset
    exact_mod_cast (Nat.succ_lt_succ hCard)
  · intro hlt
    by_contra hnot
    have hyx : y ≤ x := le_of_not_gt hnot
    unfold orderUtility orderLowerSet at hlt
    have hSubset : Finset.univ.filter (fun z : T => z ≤ y) ⊆
        Finset.univ.filter (fun z : T => z ≤ x) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, le_trans hz.2 hyx⟩
    have hCard : (Finset.univ.filter (fun z : T => z ≤ y)).card ≤
        (Finset.univ.filter (fun z : T => z ≤ x)).card :=
      Finset.card_le_card hSubset
    have hNot : ¬
        (((Finset.univ.filter (fun z : T => z ≤ x)).card : ℝ) + 1 <
          ((Finset.univ.filter (fun z : T => z ≤ y)).card : ℝ) + 1) := by
      apply not_lt.mpr
      exact_mod_cast Nat.succ_le_succ hCard
    exact hNot hlt

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_realization :
    UtilityRealization (IST := IST) (fun i x => orderUtility (IST := IST) i x) where
  order_iff := orderUtility_order_iff

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma positiveOrderUtility_realization :
    PositiveUtilityRealization (IST := IST) (fun i x => orderUtility (IST := IST) i x) where
  order_iff := orderUtility_order_iff
  positive := orderUtility_positive

/-- A utility vector embeds a good into `ℝ^I`. -/
def utilityVector (u : I → T → ℝ) (x : T) : I → ℝ :=
  fun i => u i x

/--
The coordinate model of Scarf's slack vector for face `i`: the `i`th
coordinate is zero and all other coordinates are the chosen large value `M i`.
-/
def slackVector (M : I → ℝ) (i : I) : I → ℝ :=
  fun j => if j = i then 0 else M i

/-- Interpret the enlarged set `T ∪ I` as points in `ℝ^I`. -/
def extendedCoordinatePoint (u : I → T → ℝ) (M : I → ℝ) :
    ExtendedGoods T I → I → ℝ
  | Sum.inl x => utilityVector (I := I) u x
  | Sum.inr i => slackVector (I := I) M i

/-- The slack heights are large enough to dominate all good coordinates. -/
def SlackBounds (u : I → T → ℝ) (M : I → ℝ) : Prop :=
  ∀ i j x, u j x < M i

/-- A uniform choice of slack heights for a finite utility realization. -/
def uniformSlackHeight : I → ℝ :=
  fun _ => (Fintype.card T : ℝ) + 2

omit [Fintype I] in
@[simp] lemma slackVector_self (M : I → ℝ) (i : I) :
    slackVector (I := I) M i i = 0 := by
  simp [slackVector]

omit [Fintype I] in
@[simp] lemma slackVector_of_ne (M : I → ℝ) {i j : I} (h : j ≠ i) :
    slackVector (I := I) M i j = M i := by
  simp [slackVector, h]

omit [Fintype I] in
lemma slackVector_other_coordinate_gt {M : I → ℝ} {i j : I} (hji : j ≠ i)
    {r : ℝ} (hr : r < M i) :
    r < slackVector (I := I) M i j := by
  simpa [slackVector, hji] using hr

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] IST in
@[simp] lemma extendedCoordinatePoint_good (u : I → T → ℝ) (M : I → ℝ) (x : T) :
    extendedCoordinatePoint (T := T) (I := I) u M (Sum.inl x) = utilityVector (I := I) u x := rfl

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] IST in
@[simp] lemma extendedCoordinatePoint_slack (u : I → T → ℝ) (M : I → ℝ) (i : I) :
    extendedCoordinatePoint (T := T) (I := I) u M (Sum.inr i) = slackVector (I := I) M i := rfl

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] IST in
lemma slackBounds_lt_slack_coordinate {u : I → T → ℝ} {M : I → ℝ}
    (hM : SlackBounds (T := T) (I := I) u M) {i j : I} (hji : j ≠ i) (x : T) :
    extendedCoordinatePoint (T := T) (I := I) u M (Sum.inl x) j <
      extendedCoordinatePoint (T := T) (I := I) u M (Sum.inr i) j := by
  simp [extendedCoordinatePoint, utilityVector, slackVector, hji, hM i j x]

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_lt_uniformSlackHeight (i : I) (x : T) :
    orderUtility (IST := IST) i x < uniformSlackHeight (T := T) (I := I) i := by
  unfold orderUtility uniformSlackHeight orderLowerSet
  have hCard : (Finset.univ.filter (fun y : T => (IST i).le y x)).card ≤ Fintype.card T := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hNat :
      (Finset.univ.filter (fun y : T => (IST i).le y x)).card + 1 <
        Fintype.card T + 2 := by
    omega
  exact_mod_cast hNat

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_slackBounds :
    SlackBounds (T := T) (I := I)
      (fun i x => orderUtility (IST := IST) i x) (uniformSlackHeight (T := T) (I := I)) := by
  intro i j x
  simpa [uniformSlackHeight] using orderUtility_lt_uniformSlackHeight j x

/-- A fixed finite tie-breaker for the enlarged set. -/
def extendedTieIndex (z : ExtendedGoods T I) : Fin (Fintype.card (ExtendedGoods T I)) :=
  Fintype.equivFin (ExtendedGoods T I) z

/--
The coordinate-induced strict order on `T ∪ I`, with a finite tie-breaker.
This is the formal version of "the values of coordinates define linear orders"
after perturbing/tie-breaking.
-/
def extendedCoordinateLt (u : I → T → ℝ) (M : I → ℝ) (i : I)
    (x y : ExtendedGoods T I) : Prop :=
  toLex (extendedCoordinatePoint (T := T) (I := I) u M x i, extendedTieIndex (T := T) (I := I) x) <
    toLex (extendedCoordinatePoint (T := T) (I := I) u M y i, extendedTieIndex (T := T) (I := I) y)

omit [Inhabited T] [DecidableEq T] [DecidableEq I] IST in
lemma extendedTieIndex_injective :
    Function.Injective (extendedTieIndex (T := T) (I := I)) := by
  intro x y h
  exact (Fintype.equivFin (ExtendedGoods T I)).injective h

omit [Inhabited T] [DecidableEq T] [DecidableEq I] IST in
instance extendedCoordinateLt_isStrictTotalOrder (u : I → T → ℝ) (M : I → ℝ) (i : I) :
    IsStrictTotalOrder (ExtendedGoods T I) (extendedCoordinateLt (T := T) (I := I) u M i) where
  trichotomous := by
    intro a b h_ab h_ba
    unfold extendedCoordinateLt at h_ab h_ba
    have h_eq :
        toLex (extendedCoordinatePoint (T := T) (I := I) u M a i,
            extendedTieIndex (T := T) (I := I) a) =
          toLex (extendedCoordinatePoint (T := T) (I := I) u M b i,
            extendedTieIndex (T := T) (I := I) b) :=
      le_antisymm (le_of_not_gt h_ba) (le_of_not_gt h_ab)
    have h_pair :
        (extendedCoordinatePoint (T := T) (I := I) u M a i,
            extendedTieIndex (T := T) (I := I) a) =
          (extendedCoordinatePoint (T := T) (I := I) u M b i,
            extendedTieIndex (T := T) (I := I) b) :=
      (EquivLike.injective (toLex : (ℝ × Fin (Fintype.card (ExtendedGoods T I))) ≃
        Lex (ℝ × Fin (Fintype.card (ExtendedGoods T I))))) h_eq
    exact extendedTieIndex_injective (congrArg Prod.snd h_pair)
  irrefl := by
    intro a
    unfold extendedCoordinateLt
    exact lt_irrefl _
  trans := by
    intro a b c h_ab h_bc
    unfold extendedCoordinateLt at *
    exact lt_trans h_ab h_bc

/-- The indexed family of coordinate-induced orders on the enlarged set. -/
@[reducible]
def coordinateIndexedLOrder (u : I → T → ℝ) (M : I → ℝ) :
    IndexedLOrder I (ExtendedGoods T I) where
  IST := fun i => linearOrderOfSTO (extendedCoordinateLt (T := T) (I := I) u M i)

omit [Inhabited T] [DecidableEq T] IST in
lemma extendedCoordinateLt_of_coord_lt {u : I → T → ℝ} {M : I → ℝ}
    {i : I} {x y : ExtendedGoods T I}
    (h : extendedCoordinatePoint (T := T) (I := I) u M x i <
      extendedCoordinatePoint (T := T) (I := I) u M y i) :
    extendedCoordinateLt (T := T) (I := I) u M i x y := by
  unfold extendedCoordinateLt
  change Prod.Lex (· < ·) (· < ·)
    (extendedCoordinatePoint (T := T) (I := I) u M x i, extendedTieIndex (T := T) (I := I) x)
    (extendedCoordinatePoint (T := T) (I := I) u M y i, extendedTieIndex (T := T) (I := I) y)
  exact Prod.Lex.left _ _ h

omit [Inhabited T] [DecidableEq T] in
lemma extendedCoordinateLt_goods_of_original_lt {u : I → T → ℝ} {M : I → ℝ}
    (hu : UtilityRealization (IST := IST) u) {i : I} {x y : T}
    (hxy : (IST i).lt x y) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl x) (Sum.inl y) := by
  apply extendedCoordinateLt_of_coord_lt
  simpa [extendedCoordinatePoint, utilityVector] using (hu.order_iff i x y).mp hxy

omit [Inhabited T] [DecidableEq T] in
lemma original_lt_of_extendedCoordinateLt_goods {u : I → T → ℝ} {M : I → ℝ}
    (hu : UtilityRealization (IST := IST) u) {i : I} {x y : T}
    (hxy : extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl x) (Sum.inl y)) :
    (IST i).lt x y := by
  letI : LinearOrder T := IST i
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact hlt
  · subst heq
    exact (lt_irrefl _ hxy).elim
  · have hyxCoord : u i y < u i x := (hu.order_iff i y x).mp hgt
    letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M) i
    have hnot : ¬ extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl x) (Sum.inl y) := by
      unfold extendedCoordinateLt
      apply not_lt.mpr
      apply le_of_lt
      apply extendedCoordinateLt_of_coord_lt
      simpa [extendedCoordinatePoint, utilityVector] using hyxCoord
    exact False.elim (hnot hxy)

omit [Inhabited T] [DecidableEq T] in
lemma extendedCoordinateLt_goods_iff {u : I → T → ℝ} {M : I → ℝ}
    (hu : UtilityRealization (IST := IST) u) (i : I) (x y : T) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl x) (Sum.inl y) ↔
      (IST i).lt x y :=
  ⟨original_lt_of_extendedCoordinateLt_goods hu, extendedCoordinateLt_goods_of_original_lt hu⟩

omit [Inhabited T] in
lemma coordinateGoods_le_of_original_le {u : I → T → ℝ} {M : I → ℝ}
    (hu : UtilityRealization (IST := IST) u) {i : I} {x y : T}
    (hxy : (IST i).le x y) :
    ((coordinateIndexedLOrder (T := T) (I := I) u M) i).le (Sum.inl x) (Sum.inl y) := by
  letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M) i
  letI : LinearOrder T := IST i
  by_cases hEq : x = y
  · subst hEq
    exact le_rfl
  · exact le_of_lt (extendedCoordinateLt_goods_of_original_lt hu (lt_of_le_of_ne hxy hEq))

omit [Inhabited T] [DecidableEq T] in
lemma original_le_of_coordinateGoods_le {u : I → T → ℝ} {M : I → ℝ}
    (hu : UtilityRealization (IST := IST) u) {i : I} {x y : T}
    (hxy : ((coordinateIndexedLOrder (T := T) (I := I) u M) i).le (Sum.inl x) (Sum.inl y)) :
    (IST i).le x y := by
  letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M) i
  letI : LinearOrder T := IST i
  by_contra hnot
  have hyx : (IST i).lt y x := lt_of_not_ge hnot
  have hCoord : extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl y) (Sum.inl x) :=
    extendedCoordinateLt_goods_of_original_lt hu hyx
  exact not_lt_of_ge hxy hCoord

omit [Inhabited T] [DecidableEq T] IST in
lemma coordinateGood_lt_slack_of_ne {u : I → T → ℝ} {M : I → ℝ}
    (hM : SlackBounds (T := T) (I := I) u M) {i k : I} (hik : i ≠ k) (x : T) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl x) (Sum.inr k) := by
  apply extendedCoordinateLt_of_coord_lt
  simp [extendedCoordinatePoint, utilityVector, slackVector, hik, hM k i x]

omit [Inhabited T] [DecidableEq T] in
lemma coordinateSlack_lt_good {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u) (i : I) (x : T) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inr i) (Sum.inl x) := by
  apply extendedCoordinateLt_of_coord_lt
  simpa [extendedCoordinatePoint, utilityVector, slackVector] using hu.positive i x

omit [DecidableEq T] in
lemma coordinateSlack_lt_slack_of_ne {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M) {i k : I} (hik : i ≠ k) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inr i) (Sum.inr k) := by
  apply extendedCoordinateLt_of_coord_lt
  have hposM : 0 < M k := lt_trans (hu.positive i (default : T)) (hM k i default)
  simpa [extendedCoordinatePoint, slackVector, hik] using hposM

/-- The literal coordinate-dominance primitive definition on the enlarged ordered set. -/
def isCoordinatePrimitive (u : I → T → ℝ) (M : I → ℝ)
    (X : Finset (ExtendedGoods T I)) : Prop :=
  X.card = Fintype.card I ∧
    (coordinateIndexedLOrder (T := T) (I := I) u M).isDominant X Finset.univ

theorem nativePrimitive_to_coordinatePrimitive {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M)
    {X : Finset (ExtendedGoods T I)} (hX : isPrimitiveNative (IST := IST) X) :
    isCoordinatePrimitive (T := T) (I := I) u M X := by
  constructor
  · exact hX.1
  · intro y
    let σ := fromGoods (T := T) (I := I) X
    let C := fromMissing (T := T) (I := I) X
    cases y with
    | inl t =>
        obtain ⟨i, hiC, hleGoods⟩ := hX.2 t
        refine ⟨i, Finset.mem_univ i, ?_⟩
        intro z hz
        cases z with
        | inl x =>
            have hxσ : x ∈ σ := by simpa [σ] using hz
            exact coordinateGoods_le_of_original_le hu.toUtilityRealization (hleGoods x hxσ)
        | inr k =>
            have hkNotC : k ∉ C := by simpa [C] using hz
            have hik : i ≠ k := by
              intro hEq
              exact hkNotC (hEq ▸ hiC)
            letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M) i
            exact le_of_lt (coordinateGood_lt_slack_of_ne hM hik t)
    | inr j =>
        refine ⟨j, Finset.mem_univ j, ?_⟩
        intro z hz
        cases z with
        | inl x =>
            letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M) j
            exact le_of_lt (coordinateSlack_lt_good (M := M) hu j x)
        | inr k =>
            by_cases hkj : k = j
            · subst hkj
              letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M) k
              exact le_rfl
            · letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M) j
              exact le_of_lt (coordinateSlack_lt_slack_of_ne hu hM (Ne.symm hkj))

omit [Inhabited T] in
theorem coordinatePrimitive_to_nativePrimitive {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    {X : Finset (ExtendedGoods T I)}
    (hX : isCoordinatePrimitive (T := T) (I := I) u M X) :
    isPrimitiveNative (IST := IST) X := by
  constructor
  · exact hX.1
  · intro y
    obtain ⟨i, _hi, hleX⟩ := hX.2 (Sum.inl y)
    have hiMissing : i ∈ fromMissing (T := T) (I := I) X := by
      rw [mem_fromMissing]
      intro hiSlack
      have hleSlack := hleX (Sum.inr i) hiSlack
      have hSlackLtGood := coordinateSlack_lt_good (M := M) hu i y
      letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M) i
      exact not_lt_of_ge hleSlack hSlackLtGood
    refine ⟨i, hiMissing, ?_⟩
    intro x hx
    have hleGood := hleX (Sum.inl x) (by simpa using hx)
    exact original_le_of_coordinateGoods_le hu.toUtilityRealization hleGood

theorem coordinatePrimitive_iff_native {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M)
    {X : Finset (ExtendedGoods T I)} :
    isCoordinatePrimitive (T := T) (I := I) u M X ↔ isPrimitiveNative (IST := IST) X :=
  ⟨coordinatePrimitive_to_nativePrimitive hu, nativePrimitive_to_coordinatePrimitive hu hM⟩

end IndexedLOrder

end
