import Mathlib.Data.Set.Finite.Basic

/-!
# Signed subsets

The signed-set language used throughout Sections 5--8 and Appendix A of Ivanov's
“Beyond Sperner's Lemma”.  A signed subset has disjoint positive and negative parts; its
support is their union.  The ground set is represented by the ambient type.
-/

namespace BeyondSperner

/-- A signed subset of `α`, represented by disjoint positive and negative parts. -/
@[ext]
structure SignedSubset (α : Type*) where
  positive : Set α
  negative : Set α
  disjoint : Disjoint positive negative

namespace SignedSubset

variable {α β : Type*}

/-- The unsigned support `C⁺ ∪ C⁻`. -/
def support (C : SignedSubset α) : Set α := C.positive ∪ C.negative

/-- Reverse every sign. -/
def negate (C : SignedSubset α) : SignedSubset α where
  positive := C.negative
  negative := C.positive
  disjoint := C.disjoint.symm

instance : Neg (SignedSubset α) := ⟨negate⟩

@[simp] theorem neg_positive (C : SignedSubset α) : (-C).positive = C.negative := rfl
@[simp] theorem neg_negative (C : SignedSubset α) : (-C).negative = C.positive := rfl

@[simp]
theorem support_neg (C : SignedSubset α) : (-C).support = C.support := by
  simp [support, Set.union_comm]

@[simp]
theorem neg_neg (C : SignedSubset α) : -(-C) = C := by
  cases C
  rfl

/-- Signed inclusion: both sign parts are included with their signs unchanged. -/
instance : LE (SignedSubset α) where
  le C D := C.positive ⊆ D.positive ∧ C.negative ⊆ D.negative

instance : PartialOrder (SignedSubset α) where
  le_refl C := ⟨Set.Subset.rfl, Set.Subset.rfl⟩
  le_trans _ _ _ hCD hDE := ⟨hCD.1.trans hDE.1, hCD.2.trans hDE.2⟩
  le_antisymm _ _ hCD hDC := SignedSubset.ext
    (Set.Subset.antisymm hCD.1 hDC.1) (Set.Subset.antisymm hCD.2 hDC.2)

theorem le_def {C D : SignedSubset α} :
    C ≤ D ↔ C.positive ⊆ D.positive ∧ C.negative ⊆ D.negative := Iff.rfl

theorem support_mono {C D : SignedSubset α} (h : C ≤ D) : C.support ⊆ D.support := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (h.1 hx)
  · exact Or.inr (h.2 hx)

/-- The empty signed subset. -/
def empty : SignedSubset α where
  positive := ∅
  negative := ∅
  disjoint := by simp

instance : EmptyCollection (SignedSubset α) := ⟨empty⟩

@[simp] theorem empty_positive : (∅ : SignedSubset α).positive = ∅ := rfl
@[simp] theorem empty_negative : (∅ : SignedSubset α).negative = ∅ := rfl
@[simp] theorem support_empty : (∅ : SignedSubset α).support = ∅ := by
  simp [support]

theorem eq_empty_iff (C : SignedSubset α) : C = ∅ ↔ C.support = ∅ := by
  constructor
  · rintro rfl
    simp
  · intro h
    apply SignedSubset.ext
    · apply Set.Subset.antisymm
      · intro x hx
        have : x ∈ C.support := Or.inl hx
        rw [h] at this
        exact this.elim
      · exact Set.empty_subset _
    · apply Set.Subset.antisymm
      · intro x hx
        have : x ∈ C.support := Or.inr hx
        rw [h] at this
        exact this.elim
      · exact Set.empty_subset _

/-- The signed singleton carrying a positive sign. -/
def positiveSingleton (x : α) : SignedSubset α where
  positive := {x}
  negative := ∅
  disjoint := Set.disjoint_empty _

/-- The signed singleton carrying a negative sign. -/
def negativeSingleton (x : α) : SignedSubset α where
  positive := ∅
  negative := {x}
  disjoint := Set.empty_disjoint _

@[simp]
theorem positiveSingleton_positive (x : α) :
    (positiveSingleton x).positive = {x} := rfl

@[simp]
theorem positiveSingleton_negative (x : α) :
    (positiveSingleton x).negative = ∅ := rfl

@[simp]
theorem negativeSingleton_positive (x : α) :
    (negativeSingleton x).positive = ∅ := rfl

@[simp]
theorem negativeSingleton_negative (x : α) :
    (negativeSingleton x).negative = {x} := rfl

@[simp]
theorem support_positiveSingleton (x : α) :
    (positiveSingleton x).support = {x} := by
  simp [support]

@[simp]
theorem support_negativeSingleton (x : α) :
    (negativeSingleton x).support = {x} := by
  simp [support]

@[simp]
theorem neg_positiveSingleton (x : α) :
    -(positiveSingleton x) = negativeSingleton x := rfl

@[simp]
theorem neg_negativeSingleton (x : α) :
    -(negativeSingleton x) = positiveSingleton x := rfl

/-- Remove an element from both signed parts. -/
def erase (C : SignedSubset α) (x : α) : SignedSubset α where
  positive := C.positive \ {x}
  negative := C.negative \ {x}
  disjoint := C.disjoint.mono Set.sdiff_subset Set.sdiff_subset

@[simp]
theorem erase_positive (C : SignedSubset α) (x : α) :
    (C.erase x).positive = C.positive \ {x} := rfl

@[simp]
theorem erase_negative (C : SignedSubset α) (x : α) :
    (C.erase x).negative = C.negative \ {x} := rfl

@[simp]
theorem support_erase (C : SignedSubset α) (x : α) :
    (C.erase x).support = C.support \ {x} := by
  simp [support, Set.union_sdiff_distrib]

@[simp]
theorem neg_erase (C : SignedSubset α) (x : α) :
    (-C).erase x = -(C.erase x) := by
  ext <;> simp

/-- Remove a set of coordinates from a sign vector. -/
def remove (C : SignedSubset α) (A : Set α) : SignedSubset α where
  positive := C.positive \ A
  negative := C.negative \ A
  disjoint := C.disjoint.mono Set.sdiff_subset Set.sdiff_subset

@[simp]
theorem remove_positive (C : SignedSubset α) (A : Set α) :
    (C.remove A).positive = C.positive \ A := rfl

@[simp]
theorem remove_negative (C : SignedSubset α) (A : Set α) :
    (C.remove A).negative = C.negative \ A := rfl

@[simp]
theorem support_remove (C : SignedSubset α) (A : Set α) :
    (C.remove A).support = C.support \ A := by
  simp [support, Set.union_sdiff_distrib]

@[simp]
theorem neg_remove (C : SignedSubset α) (A : Set α) :
    (-C).remove A = -(C.remove A) := by
  ext <;> simp

/-- Reorient a sign vector on a set of coordinates. -/
def reorient (C : SignedSubset α) (A : Set α) : SignedSubset α where
  positive := (C.positive \ A) ∪ (C.negative ∩ A)
  negative := (C.negative \ A) ∪ (C.positive ∩ A)
  disjoint := by
    rw [Set.disjoint_left]
    rintro x (hxp | hxn) (hxn' | hxp')
    · exact Set.disjoint_left.1 C.disjoint hxp.1 hxn'.1
    · exact hxp.2 hxp'.2
    · exact hxn'.2 hxn.2
    · exact Set.disjoint_left.1 C.disjoint hxp'.1 hxn.1

@[simp]
theorem reorient_positive (C : SignedSubset α) (A : Set α) :
    (C.reorient A).positive = (C.positive \ A) ∪ (C.negative ∩ A) := rfl

@[simp]
theorem reorient_negative (C : SignedSubset α) (A : Set α) :
    (C.reorient A).negative = (C.negative \ A) ∪ (C.positive ∩ A) := rfl

@[simp]
theorem support_reorient (C : SignedSubset α) (A : Set α) :
    (C.reorient A).support = C.support := by
  ext x
  by_cases hxA : x ∈ A <;> simp [support, hxA, or_comm]

@[simp]
theorem neg_reorient (C : SignedSubset α) (A : Set α) :
    (-C).reorient A = -(C.reorient A) := by
  ext <;> simp [reorient, Set.union_comm]

/-- Composition of sign vectors: keep the signs of `C` on its support and use
the signs of `D` at the remaining coordinates. -/
def compose (C D : SignedSubset α) : SignedSubset α where
  positive := C.positive ∪ (D.positive \ C.support)
  negative := C.negative ∪ (D.negative \ C.support)
  disjoint := by
    rw [Set.disjoint_left]
    rintro x (hxC | hxD) (hyC | hyD)
    · exact Set.disjoint_left.1 C.disjoint hxC hyC
    · exact hyD.2 (Or.inl hxC)
    · exact hxD.2 (Or.inr hyC)
    · exact Set.disjoint_left.1 D.disjoint hxD.1 hyD.1

@[simp]
theorem compose_positive (C D : SignedSubset α) :
    (C.compose D).positive = C.positive ∪ (D.positive \ C.support) := rfl

@[simp]
theorem compose_negative (C D : SignedSubset α) :
    (C.compose D).negative = C.negative ∪ (D.negative \ C.support) := rfl

@[simp]
theorem support_compose (C D : SignedSubset α) :
    (C.compose D).support = C.support ∪ D.support := by
  ext x
  constructor
  · rintro ((hxC | hxD) | (hxC | hxD))
    · exact Or.inl (Or.inl hxC)
    · exact Or.inr (Or.inl hxD.1)
    · exact Or.inl (Or.inr hxC)
    · exact Or.inr (Or.inr hxD.1)
  · rintro (hxC | hxD)
    · rcases hxC with hxC | hxC
      · exact Or.inl (Or.inl hxC)
      · exact Or.inr (Or.inl hxC)
    · by_cases hxC : x ∈ C.support
      · rcases hxC with hxC | hxC
        · exact Or.inl (Or.inl hxC)
        · exact Or.inr (Or.inl hxC)
      · rcases hxD with hxD | hxD
        · exact Or.inl (Or.inr ⟨hxD, hxC⟩)
        · exact Or.inr (Or.inr ⟨hxD, hxC⟩)

/-- Priority composition of a list of sign vectors.  Earlier vectors have
priority over later vectors at every coordinate. -/
def priorityCompose : List (SignedSubset α) → SignedSubset α
  | [] => ∅
  | C :: Cs => C.compose (priorityCompose Cs)

@[simp]
theorem priorityCompose_nil :
    priorityCompose ([] : List (SignedSubset α)) = ∅ := rfl

@[simp]
theorem priorityCompose_cons (C : SignedSubset α)
    (Cs : List (SignedSubset α)) :
    priorityCompose (C :: Cs) = C.compose (priorityCompose Cs) := rfl

@[simp]
theorem mem_priorityCompose_support_iff (Cs : List (SignedSubset α))
    (x : α) :
    x ∈ (priorityCompose Cs).support ↔
      ∃ C ∈ Cs, x ∈ C.support := by
  induction Cs with
  | nil => simp
  | cons C Cs ih =>
      rw [priorityCompose_cons, support_compose]
      simp [ih]

/-- A common support bound for all list members bounds their priority
composition. -/
theorem priorityCompose_support_subset {Cs : List (SignedSubset α)}
    {S : Set α} (h : ∀ C ∈ Cs, C.support ⊆ S) :
    (priorityCompose Cs).support ⊆ S := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := (mem_priorityCompose_support_iff Cs x).mp hx
  exact h C hC hxC

/-- `i` is the first member of `xs` whose assigned sign vector supports `x`. -/
def LexFirstSupportedBy {γ : Type*} (xs : List γ)
    (f : γ → SignedSubset α) (x : α) (i : Fin xs.length) : Prop :=
  x ∈ (f xs[i]).support ∧
    ∀ j : Fin xs.length, j < i → x ∉ (f xs[j]).support

theorem LexFirstSupportedBy.unique {γ : Type*} {xs : List γ}
    {f : γ → SignedSubset α} {x : α} {i j : Fin xs.length}
    (hi : LexFirstSupportedBy xs f x i)
    (hj : LexFirstSupportedBy xs f x j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hj.2 i hij hi.1).elim
  · exact hij
  · exact (hi.2 j hij hj.1).elim

/-- Some list member supports `x` exactly when there is a first such member. -/
theorem exists_lexFirstSupportedBy_iff {γ : Type*} {xs : List γ}
    {f : γ → SignedSubset α} {x : α} :
    (∃ i : Fin xs.length, LexFirstSupportedBy xs f x i) ↔
      ∃ a ∈ xs, x ∈ (f a).support := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨xs[i], List.get_mem xs i, hi.1⟩
  · intro h
    have hget : ∃ i : Fin xs.length, x ∈ (f xs[i]).support :=
      List.exists_mem_iff_get.mp h
    have hnat : ∃ n : ℕ, ∃ hn : n < xs.length,
        x ∈ (f xs[n]).support := by
      obtain ⟨i, hi⟩ := hget
      exact ⟨i, i.isLt, hi⟩
    let n : ℕ := Nat.find hnat
    have hnlt : n < xs.length := (Nat.find_spec hnat).choose
    let i : Fin xs.length := ⟨n, hnlt⟩
    refine ⟨i, (Nat.find_spec hnat).choose_spec, ?_⟩
    intro j hji hj
    exact Nat.find_min hnat (show j.val < n from hji) ⟨j.isLt, hj⟩

/-- Priority composition of a list-indexed family: at each coordinate, keep
the sign from the first family member that supports it. -/
noncomputable def lexPriority {γ : Type*} (xs : List γ)
    (f : γ → SignedSubset α) : SignedSubset α := by
  classical
  let P : Set α := {x | ∃ i : Fin xs.length,
    LexFirstSupportedBy xs f x i ∧ x ∈ (f xs[i]).positive}
  let N : Set α := {x | ∃ i : Fin xs.length,
    LexFirstSupportedBy xs f x i ∧ x ∈ (f xs[i]).negative}
  exact {
    positive := P
    negative := N
    disjoint := by
      rw [Set.disjoint_left]
      rintro x ⟨i, hi, hxpos⟩ ⟨j, hj, hxneg⟩
      have hij : i = j := hi.unique hj
      subst j
      exact Set.disjoint_left.1 (f xs[i]).disjoint hxpos hxneg }

@[simp]
theorem mem_lexPriority_support_iff {γ : Type*} (xs : List γ)
    (f : γ → SignedSubset α) (x : α) :
    x ∈ (lexPriority xs f).support ↔
      ∃ a ∈ xs, x ∈ (f a).support := by
  classical
  rw [← exists_lexFirstSupportedBy_iff]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
    · exact ⟨i, hi⟩
    · exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    rcases hi.1 with hx | hx
    · exact Or.inl ⟨i, hi, hx⟩
    · exact Or.inr ⟨i, hi, hx⟩

/-- A common support bound for every family member bounds priority
composition. -/
theorem lexPriority_support_subset {γ : Type*} {xs : List γ}
    {f : γ → SignedSubset α} {S : Set α}
    (h : ∀ a ∈ xs, (f a).support ⊆ S) :
    (lexPriority xs f).support ⊆ S := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ :=
    (mem_lexPriority_support_iff xs f x).mp hx
  exact h a ha hxa

/-- Push a signed subset forward along an embedding. -/
def map (f : α ↪ β) (C : SignedSubset α) : SignedSubset β where
  positive := f '' C.positive
  negative := f '' C.negative
  disjoint := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have : x = y := f.injective hxy.symm
    subst y
    exact Set.disjoint_left.1 C.disjoint hx hy

/-- Pull a signed subset back along a map. -/
def comap (f : α → β) (C : SignedSubset β) : SignedSubset α where
  positive := f ⁻¹' C.positive
  negative := f ⁻¹' C.negative
  disjoint := C.disjoint.preimage f

@[simp]
theorem map_positive (f : α ↪ β) (C : SignedSubset α) :
    (C.map f).positive = f '' C.positive := rfl

@[simp]
theorem map_negative (f : α ↪ β) (C : SignedSubset α) :
    (C.map f).negative = f '' C.negative := rfl

@[simp]
theorem comap_positive (f : α → β) (C : SignedSubset β) :
    (C.comap f).positive = f ⁻¹' C.positive := rfl

@[simp]
theorem comap_negative (f : α → β) (C : SignedSubset β) :
    (C.comap f).negative = f ⁻¹' C.negative := rfl

@[simp]
theorem support_map (f : α ↪ β) (C : SignedSubset α) :
    (C.map f).support = f '' C.support := by
  simp [support, Set.image_union]

@[simp]
theorem support_comap (f : α → β) (C : SignedSubset β) :
    (C.comap f).support = f ⁻¹' C.support := by
  simp [support, Set.preimage_union]

@[simp]
theorem map_neg (f : α ↪ β) (C : SignedSubset α) :
    (-C).map f = -(C.map f) := by
  ext <;> simp

/-- Mapping signed subsets along an embedding is injective. -/
theorem map_injective (f : α ↪ β) : Function.Injective (map f) := by
  intro C D h
  apply SignedSubset.ext
  · have hpos := congrArg SignedSubset.positive h
    have hpre := congrArg (fun S : Set β ↦ f ⁻¹' S) hpos
    simpa [Set.preimage_image_eq _ f.injective] using hpre
  · have hneg := congrArg SignedSubset.negative h
    have hpre := congrArg (fun S : Set β ↦ f ⁻¹' S) hneg
    simpa [Set.preimage_image_eq _ f.injective] using hpre

/-- Pulling back and then remapping recovers a signed subset supported in the embedding range. -/
theorem map_comap_of_support_subset_range (f : α ↪ β) (C : SignedSubset β)
    (hC : C.support ⊆ Set.range f) : (C.comap f).map f = C := by
  apply SignedSubset.ext
  · apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, rfl⟩ := hC (Or.inl hy)
      exact ⟨x, hy, rfl⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, rfl⟩ := hC (Or.inr hy)
      exact ⟨x, hy, rfl⟩

/-- The sign carried by a signed subset at an element. -/
inductive Sign where
  | positive
  | negative
  | zero
  deriving DecidableEq, Repr

/-- Evaluate the sign of `C` at `x`. -/
noncomputable def signAt (C : SignedSubset α) (x : α) : Sign := by
  classical
  exact if x ∈ C.positive then .positive else if x ∈ C.negative then .negative else .zero

/-- `C` and `D` carry the same nonzero sign at `x`. -/
def SameSignAt (C D : SignedSubset α) (x : α) : Prop :=
  (x ∈ C.positive ∧ x ∈ D.positive) ∨
    (x ∈ C.negative ∧ x ∈ D.negative)

/-- Priority composition keeps the sign of the first supporting member. -/
theorem lexPriority_sameSignAt {γ : Type*} {xs : List γ}
    {f : γ → SignedSubset α} {x : α} {i : Fin xs.length}
    (hi : LexFirstSupportedBy xs f x i) :
    (lexPriority xs f).SameSignAt (f xs[i]) x := by
  classical
  rcases hi.1 with hx | hx
  · exact Or.inl ⟨⟨i, hi, hx⟩, hx⟩
  · exact Or.inr ⟨⟨i, hi, hx⟩, hx⟩

/-- Two elements carry the same nonzero sign inside one signed subset. -/
def SameSignWithin (C : SignedSubset α) (x y : α) : Prop :=
  (x ∈ C.positive ∧ y ∈ C.positive) ∨
    (x ∈ C.negative ∧ y ∈ C.negative)

/-- `C` and `D` carry opposite signs at `x`. -/
def OppositeAt (C D : SignedSubset α) (x : α) : Prop :=
  (x ∈ C.positive ∧ x ∈ D.negative) ∨
    (x ∈ C.negative ∧ x ∈ D.positive)

theorem SameSignAt.mem_support_left {C D : SignedSubset α} {x : α}
    (h : C.SameSignAt D x) : x ∈ C.support := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem SameSignAt.mem_support_right {C D : SignedSubset α} {x : α}
    (h : C.SameSignAt D x) : x ∈ D.support := by
  rcases h with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

theorem SameSignAt.positive_iff {C D : SignedSubset α} {x : α}
    (h : C.SameSignAt D x) : x ∈ C.positive ↔ x ∈ D.positive := by
  rcases h with h | h
  · exact ⟨fun _ ↦ h.2, fun _ ↦ h.1⟩
  · constructor
    · intro hx
      exact (Set.disjoint_left.1 C.disjoint hx h.1).elim
    · intro hx
      exact (Set.disjoint_left.1 D.disjoint hx h.2).elim

theorem SameSignAt.negative_iff {C D : SignedSubset α} {x : α}
    (h : C.SameSignAt D x) : x ∈ C.negative ↔ x ∈ D.negative := by
  rcases h with h | h
  · constructor
    · intro hx
      exact (Set.disjoint_left.1 C.disjoint h.1 hx).elim
    · intro hx
      exact (Set.disjoint_left.1 D.disjoint h.2 hx).elim
  · exact ⟨fun _ ↦ h.2, fun _ ↦ h.1⟩

theorem OppositeAt.mem_support_left {C D : SignedSubset α} {x : α}
    (h : C.OppositeAt D x) : x ∈ C.support := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem OppositeAt.mem_support_right {C D : SignedSubset α} {x : α}
    (h : C.OppositeAt D x) : x ∈ D.support := by
  rcases h with h | h
  · exact Or.inr h.2
  · exact Or.inl h.2

@[simp]
theorem reorient_sameSignAt_iff {C D : SignedSubset α} {A : Set α} {x : α} :
    (C.reorient A).SameSignAt (D.reorient A) x ↔ C.SameSignAt D x := by
  by_cases hxA : x ∈ A <;>
    simp only [SameSignAt, reorient_positive, reorient_negative,
      Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, hxA, not_true_eq_false,
      and_false, false_or, and_true, not_false_eq_true] <;> aesop

@[simp]
theorem reorient_oppositeAt_iff {C D : SignedSubset α} {A : Set α} {x : α} :
    (C.reorient A).OppositeAt (D.reorient A) x ↔ C.OppositeAt D x := by
  by_cases hxA : x ∈ A <;>
    simp only [OppositeAt, reorient_positive, reorient_negative,
      Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, hxA, not_true_eq_false,
      and_false, false_or, and_true, not_false_eq_true] <;> aesop

/-- On the support of the first sign vector, composition keeps its sign. -/
theorem sameSignAt_compose_left {C D : SignedSubset α} {x : α}
    (hx : x ∈ C.support) : C.SameSignAt (C.compose D) x := by
  rcases hx with hx | hx
  · exact Or.inl ⟨hx, Or.inl hx⟩
  · exact Or.inr ⟨hx, Or.inl hx⟩

/-- Outside the support of the first sign vector, composition uses the second sign. -/
theorem sameSignAt_compose_right {C D : SignedSubset α} {x : α}
    (hxC : x ∉ C.support) (hxD : x ∈ D.support) :
    D.SameSignAt (C.compose D) x := by
  rcases hxD with hxD | hxD
  · exact Or.inl ⟨hxD, Or.inr ⟨hxD, hxC⟩⟩
  · exact Or.inr ⟨hxD, Or.inr ⟨hxD, hxC⟩⟩

/-- The separation set of two signed subsets: coordinates carrying opposite signs. -/
def separation (C D : SignedSubset α) : Set α :=
  (C.positive ∩ D.negative) ∪ (C.negative ∩ D.positive)

@[simp]
theorem mem_separation {C D : SignedSubset α} {x : α} :
    x ∈ C.separation D ↔ C.OppositeAt D x := Iff.rfl

theorem separation_comm (C D : SignedSubset α) : C.separation D = D.separation C := by
  ext x
  constructor <;> rintro (h | h)
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

theorem sameSignAt_comm {C D : SignedSubset α} {x : α} :
    C.SameSignAt D x ↔ D.SameSignAt C x := by
  constructor <;> rintro (h | h)
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr ⟨h.2, h.1⟩

theorem oppositeAt_comm {C D : SignedSubset α} {x : α} :
    C.OppositeAt D x ↔ D.OppositeAt C x := by
  constructor <;> rintro (h | h)
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

/-- Same nonzero sign is transitive at a fixed element. -/
theorem SameSignAt.trans {C D E : SignedSubset α} {x : α}
    (hCD : C.SameSignAt D x) (hDE : D.SameSignAt E x) :
    C.SameSignAt E x := by
  rcases hCD with hCD | hCD <;> rcases hDE with hDE | hDE
  · exact Or.inl ⟨hCD.1, hDE.2⟩
  · exact (Set.disjoint_left.1 D.disjoint hCD.2 hDE.1).elim
  · exact (Set.disjoint_left.1 D.disjoint hDE.1 hCD.2).elim
  · exact Or.inr ⟨hCD.1, hDE.2⟩

/-- Two signed subsets that are both opposite to a third one carry the same sign. -/
theorem OppositeAt.sameSignAt_of_oppositeAt
    {C D E : SignedSubset α} {x : α}
    (hCD : C.OppositeAt D x) (hED : E.OppositeAt D x) :
    C.SameSignAt E x := by
  rcases hCD with hCD | hCD <;> rcases hED with hED | hED
  · exact Or.inl ⟨hCD.1, hED.1⟩
  · exact (Set.disjoint_left.1 D.disjoint hED.2 hCD.2).elim
  · exact (Set.disjoint_left.1 D.disjoint hCD.2 hED.2).elim
  · exact Or.inr ⟨hCD.1, hED.1⟩

/-- An opposite-sign relation followed by a same-sign relation remains opposite. -/
theorem OppositeAt.trans_sameSignAt
    {C D E : SignedSubset α} {x : α}
    (hCD : C.OppositeAt D x) (hDE : D.SameSignAt E x) :
    C.OppositeAt E x := by
  rcases hCD with hCD | hCD <;> rcases hDE with hDE | hDE
  · exact (Set.disjoint_left.1 D.disjoint hDE.1 hCD.2).elim
  · exact Or.inl ⟨hCD.1, hDE.2⟩
  · exact Or.inr ⟨hCD.1, hDE.2⟩
  · exact (Set.disjoint_left.1 D.disjoint hCD.2 hDE.1).elim

/-- Equal nonzero signs and opposite signs cannot occur at the same element. -/
theorem SameSignAt.not_oppositeAt {C D : SignedSubset α} {x : α}
    (hsame : C.SameSignAt D x) : ¬ C.OppositeAt D x := by
  intro hopp
  rcases hsame with hsame | hsame <;> rcases hopp with hopp | hopp
  · exact Set.disjoint_left.1 D.disjoint hsame.2 hopp.2
  · exact Set.disjoint_left.1 C.disjoint hsame.1 hopp.1
  · exact Set.disjoint_left.1 C.disjoint hopp.1 hsame.1
  · exact Set.disjoint_left.1 D.disjoint hopp.2 hsame.2

/-- A signed set and its negation are opposite at every support element. -/
theorem oppositeAt_neg_self {C : SignedSubset α} {x : α} (hx : x ∈ C.support) :
    C.OppositeAt (-C) x := by
  rcases hx with hx | hx
  · exact Or.inl ⟨hx, by simpa using hx⟩
  · exact Or.inr ⟨hx, by simpa using hx⟩

/-- A signed set is never opposite to itself. -/
theorem not_oppositeAt_self (C : SignedSubset α) (x : α) :
    ¬ C.OppositeAt C x := by
  rintro (h | h)
  · exact Set.disjoint_left.1 C.disjoint h.1 h.2
  · exact Set.disjoint_left.1 C.disjoint h.2 h.1

/-- Orthogonality of signed subsets, as in Appendix A.2. -/
def Orthogonal (C D : SignedSubset α) : Prop :=
  Disjoint C.support D.support ∨
    ∃ u ∈ C.support ∩ D.support, ∃ v ∈ C.support ∩ D.support,
      C.SameSignAt D u ∧ C.OppositeAt D v

theorem orthogonal_comm {C D : SignedSubset α} :
    C.Orthogonal D ↔ D.Orthogonal C := by
  constructor
  · rintro (h | ⟨u, hu, v, hv, hsame, hopp⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨u, ⟨hu.2, hu.1⟩, v, ⟨hv.2, hv.1⟩,
        sameSignAt_comm.mp hsame, oppositeAt_comm.mp hopp⟩
  · rintro (h | ⟨u, hu, v, hv, hsame, hopp⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨u, ⟨hu.2, hu.1⟩, v, ⟨hv.2, hv.1⟩,
        sameSignAt_comm.mp hsame, oppositeAt_comm.mp hopp⟩

/-- Mapping both sign vectors along an embedding preserves orthogonality. -/
theorem Orthogonal.map {C D : SignedSubset α} (h : C.Orthogonal D)
    (f : α ↪ β) : (C.map f).Orthogonal (D.map f) := by
  rcases h with hdisjoint | ⟨u, hu, v, hv, husame, hvopp⟩
  · left
    rw [support_map, support_map, Set.disjoint_left]
    rintro _ ⟨x, hxC, rfl⟩ ⟨y, hyD, hxy⟩
    have hxy' : x = y := f.injective hxy.symm
    subst y
    exact Set.disjoint_left.1 hdisjoint hxC hyD
  · right
    refine ⟨f u, ?_, f v, ?_, ?_, ?_⟩
    · rw [support_map, support_map]
      exact ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩
    · rw [support_map, support_map]
      exact ⟨⟨v, hv.1, rfl⟩, ⟨v, hv.2, rfl⟩⟩
    · rcases husame with husame | husame
      · exact Or.inl ⟨⟨u, husame.1, rfl⟩, ⟨u, husame.2, rfl⟩⟩
      · exact Or.inr ⟨⟨u, husame.1, rfl⟩, ⟨u, husame.2, rfl⟩⟩
    · rcases hvopp with hvopp | hvopp
      · exact Or.inl ⟨⟨v, hvopp.1, rfl⟩, ⟨v, hvopp.2, rfl⟩⟩
      · exact Or.inr ⟨⟨v, hvopp.1, rfl⟩, ⟨v, hvopp.2, rfl⟩⟩

@[simp]
theorem reorient_orthogonal_iff {C D : SignedSubset α} {A : Set α} :
    (C.reorient A).Orthogonal (D.reorient A) ↔ C.Orthogonal D := by
  constructor
  · rintro (hdisjoint | ⟨u, hu, v, hv, husame, hvopp⟩)
    · left
      simpa using hdisjoint
    · right
      exact ⟨u, by simpa using hu, v, by simpa using hv,
        reorient_sameSignAt_iff.mp husame,
        reorient_oppositeAt_iff.mp hvopp⟩
  · rintro (hdisjoint | ⟨u, hu, v, hv, husame, hvopp⟩)
    · left
      simpa using hdisjoint
    · right
      exact ⟨u, by simpa using hu, v, by simpa using hv,
        reorient_sameSignAt_iff.mpr husame,
        reorient_oppositeAt_iff.mpr hvopp⟩

/-- Orthogonality to two sign vectors is preserved by priority composition on
the right. -/
theorem Orthogonal.compose_right {C D E : SignedSubset α}
    (hCD : C.Orthogonal D) (hCE : C.Orthogonal E) :
    C.Orthogonal (D.compose E) := by
  by_cases hinter : Disjoint C.support D.support
  · rcases hCE with hCE | ⟨u, hu, v, hv, husame, hvopp⟩
    · left
      rw [support_compose]
      exact hinter.union_right hCE
    · right
      have huD : u ∉ D.support := fun huD ↦
        Set.disjoint_left.1 hinter hu.1 huD
      have hvD : v ∉ D.support := fun hvD ↦
        Set.disjoint_left.1 hinter hv.1 hvD
      have hucomp : u ∈ C.support ∩ (D.compose E).support := by
        rw [support_compose]
        exact ⟨hu.1, Or.inr hu.2⟩
      have hvcomp : v ∈ C.support ∩ (D.compose E).support := by
        rw [support_compose]
        exact ⟨hv.1, Or.inr hv.2⟩
      refine ⟨u, hucomp, v, hvcomp, ?_, ?_⟩
      · rcases husame with husame | husame
        · exact Or.inl ⟨husame.1, Or.inr ⟨husame.2, huD⟩⟩
        · exact Or.inr ⟨husame.1, Or.inr ⟨husame.2, huD⟩⟩
      · rcases hvopp with hvopp | hvopp
        · exact Or.inl ⟨hvopp.1, Or.inr ⟨hvopp.2, hvD⟩⟩
        · exact Or.inr ⟨hvopp.1, Or.inr ⟨hvopp.2, hvD⟩⟩
  · rcases hCD with hCD | ⟨u, hu, v, hv, husame, hvopp⟩
    · exact (hinter hCD).elim
    · right
      have hucomp : u ∈ C.support ∩ (D.compose E).support := by
        rw [support_compose]
        exact ⟨hu.1, Or.inl hu.2⟩
      have hvcomp : v ∈ C.support ∩ (D.compose E).support := by
        rw [support_compose]
        exact ⟨hv.1, Or.inl hv.2⟩
      refine ⟨u, hucomp, v, hvcomp, ?_, ?_⟩
      · rcases husame with husame | husame
        · exact Or.inl ⟨husame.1, Or.inl husame.2⟩
        · exact Or.inr ⟨husame.1, Or.inl husame.2⟩
      · rcases hvopp with hvopp | hvopp
        · exact Or.inl ⟨hvopp.1, Or.inl hvopp.2⟩
        · exact Or.inr ⟨hvopp.1, Or.inl hvopp.2⟩

/-- Orthogonality to two sign vectors is preserved by priority composition on
the left. -/
theorem Orthogonal.compose_left {C D E : SignedSubset α}
    (hCE : C.Orthogonal E) (hDE : D.Orthogonal E) :
    (C.compose D).Orthogonal E := by
  rw [orthogonal_comm]
  exact (orthogonal_comm.mp hCE).compose_right (orthogonal_comm.mp hDE)

/-- Orthogonality to every member of a list is preserved by their priority
composition on the right. -/
theorem Orthogonal.priorityCompose_right {C : SignedSubset α}
    {Cs : List (SignedSubset α)}
    (h : ∀ D ∈ Cs, C.Orthogonal D) :
    C.Orthogonal (priorityCompose Cs) := by
  induction Cs with
  | nil =>
      left
      simp
  | cons D Ds ih =>
      rw [priorityCompose_cons]
      exact (h D (by simp)).compose_right
        (ih (fun E hE ↦ h E (by simp [hE])))

/-- Orthogonality to every member of a list is preserved by their priority
composition on the left. -/
theorem Orthogonal.priorityCompose_left {D : SignedSubset α}
    {Cs : List (SignedSubset α)}
    (h : ∀ C ∈ Cs, C.Orthogonal D) :
    (priorityCompose Cs).Orthogonal D := by
  rw [orthogonal_comm]
  exact Orthogonal.priorityCompose_right
    (fun C hC ↦ orthogonal_comm.mp (h C hC))

/-- Erasing a coordinate from the right preserves orthogonality when that
coordinate is absent from the left support. -/
theorem orthogonal_erase_right_of_not_mem_left
    {C D : SignedSubset α} {x : α} (hCD : C.Orthogonal D)
    (hxC : x ∉ C.support) : C.Orthogonal (D.erase x) := by
  rcases hCD with hdisjoint | ⟨u, hu, v, hv, husame, hvopp⟩
  · left
    apply hdisjoint.mono_right
    rw [support_erase]
    exact Set.sdiff_subset
  · right
    have hux : u ≠ x := fun h ↦ hxC (h ▸ hu.1)
    have hvx : v ≠ x := fun h ↦ hxC (h ▸ hv.1)
    refine ⟨u, ⟨hu.1, by simpa [hux] using hu.2⟩,
      v, ⟨hv.1, by simpa [hvx] using hv.2⟩, ?_, ?_⟩
    · rcases husame with husame | husame
      · exact Or.inl ⟨husame.1, by simpa [hux] using husame.2⟩
      · exact Or.inr ⟨husame.1, by simpa [hux] using husame.2⟩
    · rcases hvopp with hvopp | hvopp
      · exact Or.inl ⟨hvopp.1, by simpa [hvx] using hvopp.2⟩
      · exact Or.inr ⟨hvopp.1, by simpa [hvx] using hvopp.2⟩

/-- Erasing a coordinate from the left preserves orthogonality when that
coordinate is absent from the right support. -/
theorem orthogonal_erase_left_of_not_mem_right
    {C D : SignedSubset α} {x : α} (hCD : C.Orthogonal D)
    (hxD : x ∉ D.support) : (C.erase x).Orthogonal D := by
  rw [show (C.erase x).Orthogonal D ↔ D.Orthogonal (C.erase x) from by
    constructor <;> intro h
    · rcases h with h | ⟨u, hu, v, hv, hs, ho⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨u, ⟨hu.2, hu.1⟩, v, ⟨hv.2, hv.1⟩,
          SignedSubset.sameSignAt_comm.mp hs,
          SignedSubset.oppositeAt_comm.mp ho⟩
    · rcases h with h | ⟨u, hu, v, hv, hs, ho⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨u, ⟨hu.2, hu.1⟩, v, ⟨hv.2, hv.1⟩,
          SignedSubset.sameSignAt_comm.mp hs,
          SignedSubset.oppositeAt_comm.mp ho⟩]
  exact orthogonal_erase_right_of_not_mem_left
    (by
      rcases hCD with h | ⟨u, hu, v, hv, hs, ho⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨u, ⟨hu.2, hu.1⟩, v, ⟨hv.2, hv.1⟩,
          SignedSubset.sameSignAt_comm.mp hs,
          SignedSubset.oppositeAt_comm.mp ho⟩) hxD

/-- Signed subsets whose supports meet in exactly one element cannot be orthogonal. -/
theorem not_orthogonal_of_support_inter_eq_singleton
    {C D : SignedSubset α} {x : α}
    (hinter : C.support ∩ D.support = {x}) : ¬ C.Orthogonal D := by
  rintro (hdisjoint | ⟨u, hu, v, hv, hsame, hopposite⟩)
  · have hx : x ∈ C.support ∩ D.support := by
      rw [hinter]
      simp
    exact (Set.disjoint_left.1 hdisjoint hx.1 hx.2)
  · have huEq : u = x := by simpa [hinter] using hu
    have hvEq : v = x := by simpa [hinter] using hv
    subst u
    subst v
    exact hsame.not_oppositeAt hopposite

/-- At a common support element, two signed subsets have either the same or opposite sign. -/
theorem sameSignAt_or_oppositeAt_of_mem
    {C D : SignedSubset α} {x : α}
    (hx : x ∈ C.support ∩ D.support) :
    C.SameSignAt D x ∨ C.OppositeAt D x := by
  rcases hx.1 with hxCp | hxCn <;> rcases hx.2 with hxDp | hxDn
  · exact Or.inl (Or.inl ⟨hxCp, hxDp⟩)
  · exact Or.inr (Or.inl ⟨hxCp, hxDn⟩)
  · exact Or.inr (Or.inr ⟨hxCn, hxDp⟩)
  · exact Or.inl (Or.inr ⟨hxCn, hxDn⟩)

/-- A same-sign intersection and an opposite-sign intersection witness orthogonality. -/
theorem orthogonal_of_sameSignAt_of_oppositeAt
    {C D : SignedSubset α} {x y : α}
    (hx : x ∈ C.support ∩ D.support) (hy : y ∈ C.support ∩ D.support)
    (hsame : C.SameSignAt D x) (hopposite : C.OppositeAt D y) :
    C.Orthogonal D :=
  Or.inr ⟨x, hx, y, hy, hsame, hopposite⟩

/-- For an orthogonal pair meeting only at `a` and `b`, a same-sign relation at `a`
forces an opposite-sign relation at `b`. -/
theorem oppositeAt_of_orthogonal_of_inter_eq_pair_of_sameSignAt
    {C D : SignedSubset α} {a b : α} (horth : C.Orthogonal D)
    (hinter : C.support ∩ D.support = {a, b}) (hsame : C.SameSignAt D a) :
    C.OppositeAt D b := by
  rcases horth with hdisjoint | ⟨u, hu, v, hv, _, hvopp⟩
  · have ha : a ∈ C.support ∩ D.support := by
      rw [hinter]
      simp
    exact (Set.disjoint_left.1 hdisjoint ha.1 ha.2).elim
  · have hvCases : v = a ∨ v = b := by
      rw [hinter] at hv
      simpa using hv
    rcases hvCases with rfl | rfl
    · exact (hsame.not_oppositeAt hvopp).elim
    · exact hvopp

/-- For an orthogonal pair meeting only at `a` and `b`, an opposite-sign relation at `a`
forces a same-sign relation at `b`. -/
theorem sameSignAt_of_orthogonal_of_inter_eq_pair_of_oppositeAt
    {C D : SignedSubset α} {a b : α} (horth : C.Orthogonal D)
    (hinter : C.support ∩ D.support = {a, b}) (hopp : C.OppositeAt D a) :
    C.SameSignAt D b := by
  rcases horth with hdisjoint | ⟨u, hu, _, _, husame, _⟩
  · have ha : a ∈ C.support ∩ D.support := by
      rw [hinter]
      simp
    exact (Set.disjoint_left.1 hdisjoint ha.1 ha.2).elim
  · have huCases : u = a ∨ u = b := by
      rw [hinter] at hu
      simpa using hu
    rcases huCases with rfl | rfl
    · exact (husame.not_oppositeAt hopp).elim
    · exact husame

/-- If `C` is orthogonal to `D` and `E`, each intersection consists of the same two
points, and `D,E` agree at the first point, then they also agree at the second. -/
theorem sameSignAt_of_orthogonal_pair_of_sameSignAt
    {C D E : SignedSubset α} {a b : α}
    (hCDorth : C.Orthogonal D) (hCEorth : C.Orthogonal E)
    (hCDinter : C.support ∩ D.support = {a, b})
    (hCEinter : C.support ∩ E.support = {a, b})
    (hDEa : D.SameSignAt E a) : D.SameSignAt E b := by
  have haCD : a ∈ C.support ∩ D.support := by
    rw [hCDinter]
    simp
  rcases sameSignAt_or_oppositeAt_of_mem haCD with hCDsame | hCDopp
  · have hCEsame : C.SameSignAt E a := hCDsame.trans hDEa
    have hCDbOpp :=
      oppositeAt_of_orthogonal_of_inter_eq_pair_of_sameSignAt
        hCDorth hCDinter hCDsame
    have hCEbOpp :=
      oppositeAt_of_orthogonal_of_inter_eq_pair_of_sameSignAt
        hCEorth hCEinter hCEsame
    exact (oppositeAt_comm.mp hCDbOpp).sameSignAt_of_oppositeAt
      (oppositeAt_comm.mp hCEbOpp)
  · have hCEopp : C.OppositeAt E a := hCDopp.trans_sameSignAt hDEa
    have hCDbSame :=
      sameSignAt_of_orthogonal_of_inter_eq_pair_of_oppositeAt
        hCDorth hCDinter hCDopp
    have hCEbSame :=
      sameSignAt_of_orthogonal_of_inter_eq_pair_of_oppositeAt
        hCEorth hCEinter hCEopp
    exact sameSignAt_comm.mp hCDbSame |>.trans hCEbSame

/-- Equal supports together with pointwise equal nonzero signs determine a signed subset. -/
theorem eq_of_support_eq_of_forall_sameSignAt
    {C D : SignedSubset α} (hsupport : C.support = D.support)
    (hsame : ∀ x, x ∈ C.support → C.SameSignAt D x) : C = D := by
  apply SignedSubset.ext
  · ext x
    constructor
    · intro hx
      rcases hsame x (Or.inl hx) with h | h
      · exact h.2
      · exact (Set.disjoint_left.1 C.disjoint hx h.1).elim
    · intro hx
      have hxC : x ∈ C.support := by
        rw [hsupport]
        exact Or.inl hx
      rcases hsame x hxC with h | h
      · exact h.1
      · exact (Set.disjoint_left.1 D.disjoint hx h.2).elim
  · ext x
    constructor
    · intro hx
      rcases hsame x (Or.inr hx) with h | h
      · exact (Set.disjoint_left.1 C.disjoint h.1 hx).elim
      · exact h.2
    · intro hx
      have hxC : x ∈ C.support := by
        rw [hsupport]
        exact Or.inr hx
      rcases hsame x hxC with h | h
      · exact (Set.disjoint_left.1 D.disjoint h.2 hx).elim
      · exact h.1

/-- A nonorthogonal pair with nonempty support intersection has one uniform sign relation. -/
theorem uniform_of_not_orthogonal
    {C D : SignedSubset α} (hnot : ¬ C.Orthogonal D)
    (hinter : (C.support ∩ D.support).Nonempty) :
    (∀ x, x ∈ C.support ∩ D.support → C.SameSignAt D x) ∨
      (∀ x, x ∈ C.support ∩ D.support → C.OppositeAt D x) := by
  obtain ⟨x, hx⟩ := hinter
  rcases sameSignAt_or_oppositeAt_of_mem hx with hxsame | hxopp
  · left
    intro y hy
    rcases sameSignAt_or_oppositeAt_of_mem hy with hysame | hyopp
    · exact hysame
    · exact (hnot (orthogonal_of_sameSignAt_of_oppositeAt hx hy hxsame hyopp)).elim
  · right
    intro y hy
    rcases sameSignAt_or_oppositeAt_of_mem hy with hysame | hyopp
    · exact (hnot (orthogonal_of_sameSignAt_of_oppositeAt hy hx hysame hxopp)).elim
    · exact hyopp

@[simp]
theorem neg_sameSignAt_iff_oppositeAt
    {C D : SignedSubset α} {x : α} :
    (-C).SameSignAt D x ↔ C.OppositeAt D x := by
  constructor <;> rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

@[simp]
theorem neg_oppositeAt_iff_sameSignAt
    {C D : SignedSubset α} {x : α} :
    (-C).OppositeAt D x ↔ C.SameSignAt D x := by
  constructor <;> rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

@[simp]
theorem sameSignAt_neg_right_iff_oppositeAt
    {C D : SignedSubset α} {x : α} :
    C.SameSignAt (-D) x ↔ C.OppositeAt D x := by
  rw [sameSignAt_comm, neg_sameSignAt_iff_oppositeAt, oppositeAt_comm]

@[simp]
theorem oppositeAt_neg_right_iff_sameSignAt
    {C D : SignedSubset α} {x : α} :
    C.OppositeAt (-D) x ↔ C.SameSignAt D x := by
  rw [oppositeAt_comm, neg_oppositeAt_iff_sameSignAt, sameSignAt_comm]

@[simp]
theorem orthogonal_neg_right_iff {C D : SignedSubset α} :
    C.Orthogonal (-D) ↔ C.Orthogonal D := by
  constructor
  · rintro (hdisjoint | ⟨u, hu, v, hv, husame, hvopp⟩)
    · exact Or.inl (by simpa using hdisjoint)
    · exact Or.inr ⟨v, by simpa using hv, u, by simpa using hu,
        by simpa using hvopp, by simpa using husame⟩
  · rintro (hdisjoint | ⟨u, hu, v, hv, husame, hvopp⟩)
    · exact Or.inl (by simpa using hdisjoint)
    · exact Or.inr ⟨v, by simpa using hv, u, by simpa using hu,
        by simpa using hvopp, by simpa using husame⟩
end SignedSubset

end BeyondSperner
