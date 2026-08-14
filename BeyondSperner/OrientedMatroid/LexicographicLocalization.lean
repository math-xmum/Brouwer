import BeyondSperner.OrientedMatroid.CocircuitElimination

/-!
# Lexicographic cocircuit localization data

This file defines the canonical signed lift prescribed by a positive
lexicographic localization.  It does not assume that the localization already
comes from a single-element extension.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid

variable {α : Type*}

/-- `i` is the first coordinate of `order` contained in the support of `D`. -/
def LexFirstSupported (order : List α) (D : SignedSubset α)
    (i : Fin order.length) : Prop :=
  order[i] ∈ D.support ∧
    ∀ j : Fin order.length, j < i → order[j] ∉ D.support

theorem LexFirstSupported.unique {order : List α} {D : SignedSubset α}
    {i j : Fin order.length} (hi : LexFirstSupported order D i)
    (hj : LexFirstSupported order D j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hj.2 i hij hi.1).elim
  · exact hij
  · exact (hi.2 j hij hj.1).elim

/-- A list meets a signed support exactly when it has a first supported
coordinate. -/
theorem exists_lexFirstSupported_iff {order : List α} {D : SignedSubset α} :
    (∃ i : Fin order.length, LexFirstSupported order D i) ↔
      ∃ a ∈ order, a ∈ D.support := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨order[i], List.get_mem order i, hi.1⟩
  · intro h
    have hget : ∃ i : Fin order.length, order[i] ∈ D.support :=
      List.exists_mem_iff_get.mp h
    have hnat : ∃ n : ℕ, ∃ hn : n < order.length,
        order[n] ∈ D.support := by
      obtain ⟨i, hi⟩ := hget
      exact ⟨i, i.isLt, hi⟩
    let n : ℕ := Nat.find hnat
    have hnlt : n < order.length := (Nat.find_spec hnat).choose
    let i : Fin order.length := ⟨n, hnlt⟩
    refine ⟨i, (Nat.find_spec hnat).choose_spec, ?_⟩
    intro j hji hj
    exact Nat.find_min hnat (show j.val < n from hji) ⟨j.isLt, hj⟩

/-- The canonical old-element embedding for a single-element extension. -/
def canonicalOld (α : Type*) : α ↪ α ⊕ Unit :=
  Function.Embedding.inl

/-- The new coordinate on the canonical carrier. -/
def canonicalNew (α : Type*) : α ⊕ Unit := Sum.inr ()

/-- Lift a signed subset by assigning the new coordinate the sign of its first
supported coordinate in `order`; leave the new coordinate zero if no coordinate
of `order` is supported. -/
noncomputable def lexLift (order : List α) (D : SignedSubset α) :
    SignedSubset (α ⊕ Unit) := by
  classical
  let P : Prop := ∃ i : Fin order.length,
    LexFirstSupported order D i ∧ order[i] ∈ D.positive
  let N : Prop := ∃ i : Fin order.length,
    LexFirstSupported order D i ∧ order[i] ∈ D.negative
  have hPN : ¬ (P ∧ N) := by
    rintro ⟨⟨i, hi, hipos⟩, ⟨j, hj, hjneg⟩⟩
    have hij : i = j := hi.unique hj
    subst j
    exact Set.disjoint_left.1 D.disjoint hipos hjneg
  exact {
    positive := Sum.inl '' D.positive ∪ {x | x = canonicalNew α ∧ P}
    negative := Sum.inl '' D.negative ∪ {x | x = canonicalNew α ∧ N}
    disjoint := by
      rw [Set.disjoint_left]
      intro x hxpos hxneg
      rcases hxpos with hxpos | hxnewPos <;>
        rcases hxneg with hxneg | hxnewNeg
      · obtain ⟨a, ha, rfl⟩ := hxpos
        obtain ⟨b, hb, hab⟩ := hxneg
        exact Set.disjoint_left.1 D.disjoint ha
          (Sum.inl_injective hab ▸ hb)
      · obtain ⟨a, _, rfl⟩ := hxpos
        simpa [canonicalNew] using hxnewNeg.1
      · obtain ⟨a, _, rfl⟩ := hxneg
        simpa [canonicalNew] using hxnewPos.1
      · exact hPN ⟨hxnewPos.2, hxnewNeg.2⟩ }

@[simp]
theorem lexLift_comap_canonicalOld (order : List α) (D : SignedSubset α) :
    (lexLift order D).comap (canonicalOld α) = D := by
  classical
  ext x <;>
    simp [lexLift, canonicalOld, canonicalNew]

theorem lexLift_injective (order : List α) :
    Function.Injective (lexLift order) := by
  intro D E h
  have h' := congrArg (fun X ↦ X.comap (canonicalOld α)) h
  simpa using h'

@[simp]
theorem lexLift_neg (order : List α) (D : SignedSubset α) :
    lexLift order (-D) = -(lexLift order D) := by
  classical
  ext <;> simp [lexLift, LexFirstSupported]

@[simp]
theorem canonicalNew_mem_lexLift_support_iff
    (order : List α) (D : SignedSubset α) :
    canonicalNew α ∈ (lexLift order D).support ↔
      ∃ a ∈ order, a ∈ D.support := by
  classical
  rw [← exists_lexFirstSupported_iff]
  constructor
  · rintro (hpos | hneg)
    · rcases hpos with hold | ⟨_, ⟨i, hi, _⟩⟩
      · obtain ⟨a, _, ha⟩ := hold
        simp [canonicalNew] at ha
      · exact ⟨i, hi⟩
    · rcases hneg with hold | ⟨_, ⟨i, hi, _⟩⟩
      · obtain ⟨a, _, ha⟩ := hold
        simp [canonicalNew] at ha
      · exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    rcases hi.1 with hipos | hineg
    · exact Or.inl (Or.inr ⟨rfl, ⟨i, hi, hipos⟩⟩)
    · exact Or.inr (Or.inr ⟨rfl, ⟨i, hi, hineg⟩⟩)

@[simp]
theorem canonicalNew_not_mem_lexLift_support_iff
    [DecidableEq α] (order : List α) (D : SignedSubset α) :
    canonicalNew α ∉ (lexLift order D).support ↔
      Disjoint D.support (order.toFinset : Set α) := by
  rw [not_congr (canonicalNew_mem_lexLift_support_iff order D)]
  constructor
  · intro h
    rw [Set.disjoint_left]
    intro x hxD hxOrder
    exact h ⟨x, List.mem_toFinset.mp hxOrder, hxD⟩
  · intro h ⟨x, hxOrder, hxD⟩
    exact Set.disjoint_left.1 h hxD (List.mem_toFinset.mpr hxOrder)

/-- At the first supported coordinate, the canonical lift gives the new
coordinate the same sign. -/
theorem lexLift_sameSignWithin {order : List α} {D : SignedSubset α}
    {i : Fin order.length} (hi : LexFirstSupported order D i) :
    (lexLift order D).SameSignWithin (canonicalNew α)
      (canonicalOld α order[i]) := by
  classical
  rcases hi.1 with hipos | hineg
  · apply Or.inl
    constructor
    · exact Or.inr ⟨rfl, ⟨i, hi, hipos⟩⟩
    · exact Or.inl ⟨order[i], hipos, rfl⟩
  · apply Or.inr
    constructor
    · exact Or.inr ⟨rfl, ⟨i, hi, hineg⟩⟩
    · exact Or.inl ⟨order[i], hineg, rfl⟩

end OrientedMatroid
end BeyondSperner
