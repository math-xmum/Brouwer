import BeyondSperner.Orders.LinearOrders
import BeyondSperner.Coloring.Matroid.Nondegenerate

/-!
# Classical Scarf's theorem

This file derives the classical coloring theorem used in Section 3 from the
nondegenerate oriented-matroid coloring theorem.  The specialization uses the
rank-`|I|` simplex oriented matroid on `I ⊕ Unit`; its only signed circuits
are the full positive simplex with the distinguished element negative, and
its negative.
-/

namespace BeyondSperner

open Classical Set

namespace ClassicalScarf

variable {I V : Type*}

/-- The unique positively oriented circuit of the simplex oriented matroid. -/
def simplexCircuit (I : Type*) : SignedSubset (I ⊕ Unit) where
  positive := Set.range Sum.inl
  negative := {Sum.inr ()}
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨i, rfl⟩ hx
    simp at hx

@[simp]
theorem simplexCircuit_positive (I : Type*) :
    (simplexCircuit I).positive = Set.range Sum.inl := rfl

@[simp]
theorem simplexCircuit_negative (I : Type*) :
    (simplexCircuit I).negative = {Sum.inr ()} := rfl

@[simp]
theorem simplexCircuit_support (I : Type*) :
    (simplexCircuit I).support = Set.univ := by
  ext x
  cases x with
  | inl i => simp [SignedSubset.support, simplexCircuit]
  | inr u => cases u; simp [SignedSubset.support, simplexCircuit]

theorem simplexCircuit_ne_neg [Nonempty I] :
    simplexCircuit I ≠ -(simplexCircuit I) := by
  intro h
  let i : I := Classical.choice (inferInstance : Nonempty I)
  have hi : Sum.inl i ∈ (simplexCircuit I).positive := ⟨i, rfl⟩
  have : Sum.inl i ∈ (-(simplexCircuit I)).positive := h ▸ hi
  simp at this

/-- The simplex oriented matroid has precisely the two orientations of its
full-support circuit. -/
def simplexOrientedMatroid (I : Type*) [Nonempty I] :
    OrientedMatroid.Data (I ⊕ Unit) where
  circuits := {simplexCircuit I, -(simplexCircuit I)}
  support_nonempty := by
    intro C hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl <;> simp
  neg_mem := by
    intro C hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC ⊢
    rcases hC with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (by simp)
  eq_or_eq_neg_of_support_subset := by
    intro C D hC hD _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC hD
    rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by simp)
    · exact Or.inr rfl
    · exact Or.inl rfl
  weakElimination := by
    intro C D hC hD hne u hop
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC hD
    rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
    · exact (SignedSubset.not_oppositeAt_self _ _ hop).elim
    · exact (hne rfl).elim
    · exact (hne (by simp)).elim
    · exact (SignedSubset.not_oppositeAt_self _ _ hop).elim

@[simp]
theorem simplexOrientedMatroid_isCircuit [Nonempty I]
    {C : SignedSubset (I ⊕ Unit)} :
    (simplexOrientedMatroid I).IsCircuit C ↔
      C = simplexCircuit I ∨ C = -(simplexCircuit I) := by
  rfl

theorem simplexOrientedMatroid_isAcyclic [Nonempty I] :
    (simplexOrientedMatroid I).IsAcyclic := by
  intro C hC
  rw [simplexOrientedMatroid_isCircuit] at hC
  rcases hC with rfl | rfl
  · exact ⟨Sum.inr (), by simp⟩
  · let i : I := Classical.choice (inferInstance : Nonempty I)
    exact ⟨Sum.inl i, by simp [simplexCircuit]⟩

private theorem simplexBasis_isIndependent [Nonempty I] :
    (simplexOrientedMatroid I).IsIndependent (Set.range Sum.inl) := by
  intro C hC hsub
  have hb : Sum.inr () ∈ C.support := by
    rw [simplexOrientedMatroid_isCircuit] at hC
    rcases hC with rfl | rfl <;> simp
  obtain ⟨i, hi⟩ := hsub hb
  cases hi

private theorem simplexBasis_isBasis [Nonempty I] :
    (simplexOrientedMatroid I).IsBasis (Set.range Sum.inl) := by
  refine ⟨simplexBasis_isIndependent, ?_⟩
  intro X hX hBX x hx
  cases x with
  | inl i => exact ⟨i, rfl⟩
  | inr u =>
      cases u
      exfalso
      apply hX (C := simplexCircuit I)
      · simp
      · intro y _
        cases y with
        | inl i => exact hBX ⟨i, rfl⟩
        | inr u => cases u; exact hx

/-- The canonical framework whose basis is the simplex vertex set and whose
distinguished element is its formal interior point. -/
def simplexFramework (I : Type*) [Nonempty I] :
    MatroidColoring.Framework I (I ⊕ Unit) where
  matroid := simplexOrientedMatroid I
  vertex := Function.Embedding.inl
  distinguished := Sum.inr ()
  basis_isBasis := simplexBasis_isBasis
  distinguished_notMem_basis := by simp
  acyclic := simplexOrientedMatroid_isAcyclic
  distinguished_mem_convexHull := by
    exact Or.inr ⟨simplexCircuit I, by simp, Set.Subset.rfl, rfl⟩

@[simp]
theorem simplexFramework_vertex [Nonempty I] (i : I) :
    (simplexFramework I).vertex i = Sum.inl i := by
  rfl

@[simp]
theorem simplexFramework_distinguished [Nonempty I] :
    (simplexFramework I).distinguished = Sum.inr () := by
  rfl

/-- The simplex framework is nondegenerate: the distinguished point is not in
the oriented convex hull of fewer than all `|I|` basis vertices. -/
theorem simplexFramework_isNondegenerate [Fintype I] [DecidableEq I] [Nonempty I] :
    (simplexFramework I).IsNondegenerate := by
  intro X hbX hcard hconv
  rcases hconv with hbmem | ⟨C, hC, hCpos, hCneg⟩
  · exact hbX hbmem
  · change (simplexOrientedMatroid I).IsCircuit C at hC
    change C.positive ⊆ (X : Set (I ⊕ Unit)) at hCpos
    change C.negative = {Sum.inr ()} at hCneg
    rw [simplexOrientedMatroid_isCircuit] at hC
    rcases hC with rfl | rfl
    · have hsub : (Finset.univ.image Sum.inl : Finset (I ⊕ Unit)) ⊆ X := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact hCpos ⟨i, rfl⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ] at hle
      omega
    · let i : I := Classical.choice (inferInstance : Nonempty I)
      have hi : Sum.inl i ∈ (-(simplexCircuit I)).negative := by
        exact ⟨i, rfl⟩
      rw [hCneg] at hi
      simp at hi

section Coloring

variable [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  [Nonempty I] [Nonempty V]

/-- Regard an ordinary `I`-coloring as a coloring by the non-distinguished
elements of the simplex framework. -/
def liftColoring (D : SimplexFamily I V) (c : V → I) :
    MatroidColoring.Coloring D (simplexFramework I) :=
  fun v ↦ ⟨Sum.inl (c v.1), by simp [simplexFramework]⟩

omit [Fintype I] [Fintype V] [DecidableEq I] [Nonempty V] in @[simp]
theorem liftColoring_value (D : SimplexFamily I V) (c : V → I)
    (v : D.Vertex) :
    (liftColoring D c v).1 = Sum.inl (c v.1) := rfl

omit [Fintype V] [Nonempty V] in
/-- In the simplex specialization, formula (33) is just the union of the
ordinary color image with the complementary set of indices, embedded by
`Sum.inl`. -/
theorem completedImage_liftColoring
    (D : SimplexFamily I V) (c : V → I) (C : Finset I) (τ : Finset V)
    (hτ : τ ∈ D.complex C) :
    MatroidColoring.completedImage D (simplexFramework I)
        (liftColoring D c) C τ hτ =
      (τ.image c ∪ (Finset.univ \ C)).image Sum.inl := by
  simp only [MatroidColoring.completedImage, MatroidColoring.colorImage,
    liftColoring_value, Finset.image_union]
  congr 1
  ext x
  simp

/-- Among subsets of the old simplex vertices, a good basis is necessarily
the complete old vertex set. -/
theorem isGoodBasis_coe_of_subset_range_iff
    (S : Finset (I ⊕ Unit)) (hS : (S : Set (I ⊕ Unit)) ⊆ Set.range Sum.inl) :
    (simplexFramework I).matroid.IsGoodBasis
        (simplexFramework I).distinguished (S : Set (I ⊕ Unit)) ↔
      S = Finset.univ.image Sum.inl := by
  constructor
  · intro hgood
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, rfl⟩ := hS hx
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · have hcard := (simplexFramework I).card_eq_card_index_of_isBasis S hgood.1
      rw [Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ,
        hcard]
  · intro hSfull
    subst S
    have hrange : Set.range (simplexFramework I).vertex =
        Set.range (Sum.inl : I → I ⊕ Unit) := by
      ext x
      cases x <;> simp [simplexFramework]
    rw [Finset.coe_image]
    simp only [Finset.coe_univ, Set.image_univ]
    rw [← hrange]
    exact (simplexFramework I).basis_isGoodBasis

omit [Fintype V] [Nonempty V] in
/-- The good-basis conclusion in the specialized matroid theorem is exactly
the elementary covering equation `c(τ) ∪ (I \ C) = I`. -/
theorem completedImage_isGoodBasis_iff
    (D : SimplexFamily I V) (c : V → I) (C : Finset I) (τ : Finset V)
    (hτ : τ ∈ D.complex C) :
    (simplexFramework I).matroid.IsGoodBasis
        (simplexFramework I).distinguished
        (MatroidColoring.completedImage D (simplexFramework I)
          (liftColoring D c) C τ hτ : Set (I ⊕ Unit)) ↔
      τ.image c ∪ (Finset.univ \ C) = Finset.univ := by
  rw [completedImage_liftColoring]
  rw [isGoodBasis_coe_of_subset_range_iff]
  · constructor
    · intro h
      exact Finset.image_injective
        (f := (Sum.inl : I → I ⊕ Unit)) Sum.inl_injective h
    · intro h
      exact congrArg (Finset.image (Sum.inl : I → I ⊕ Unit)) h
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, rfl⟩

omit [Fintype V] [DecidableEq V] [Nonempty I] [Nonempty V] in
/-- The cardinality hypothesis in a top-dimensional cell upgrades the covering
equation to exact use of every color in `C`. -/
theorem image_union_sdiff_eq_univ_iff_image_eq
    (c : V → I) (C : Finset I) (τ : Finset V)
    (hcard : τ.card = C.card) :
    τ.image c ∪ (Finset.univ \ C) = Finset.univ ↔ τ.image c = C := by
  constructor
  · intro hcover
    have hCsub : C ⊆ τ.image c := by
      intro i hiC
      have hi : i ∈ τ.image c ∪ (Finset.univ \ C) := by
        rw [hcover]
        exact Finset.mem_univ i
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hi
      · exact (Finset.mem_sdiff.mp hi).2 hiC |>.elim
    have himagecard : (τ.image c).card ≤ C.card := by
      rw [← hcard]
      exact Finset.card_image_le
    exact (Finset.eq_of_subset_of_card_le hCsub himagecard).symm
  · intro himage
    subst C
    ext i
    simp

omit [Fintype V] [Nonempty V] in
/-- A solution of the matroid-coloring theorem in the simplex framework is
exactly a nonempty top simplex whose ordinary color image is its index set. -/
theorem isSolution_liftColoring_iff
    (D : SimplexFamily I V) (c : V → I) (C : Finset I) (τ : Finset V) :
    MatroidColoring.IsSolution D (simplexFramework I)
        (liftColoring D c) C τ ↔
      ∃ _hτ : τ ∈ D.complex C,
        C.Nonempty ∧ τ.card = C.card ∧ τ.image c = C := by
  constructor
  · rintro ⟨hτ, hC, hcard, hgood⟩
    refine ⟨hτ, hC, hcard, ?_⟩
    exact (image_union_sdiff_eq_univ_iff_image_eq c C τ hcard).mp
      ((completedImage_isGoodBasis_iff D c C τ hτ).mp hgood)
  · rintro ⟨hτ, hC, hcard, himage⟩
    refine ⟨hτ, hC, hcard, ?_⟩
    exact (completedImage_isGoodBasis_iff D c C τ hτ).mpr
      ((image_union_sdiff_eq_univ_iff_image_eq c C τ hcard).mpr himage)

end Coloring

section Theorem

variable [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  [Nonempty I] [Nonempty V]

/-- The finite set of the pairs counted in the classical Scarf theorem:
`C` is nonempty automatically because it supports a cell. -/
noncomputable def colorfulCellPairs (F : IndexedLinearOrders I V) (c : V → I) :
    Finset (Finset I × Finset V) :=
  Finset.univ.filter fun p ↦ F.IsCell p.2 p.1 ∧ p.2.image c = p.1

omit [Nonempty I] [Fintype I] [Nonempty V] in private theorem mem_associated_top_iff_isCell
    (F : IndexedLinearOrders I V) {C : Finset I} (hC : C.Nonempty)
    {τ : Finset V} :
    τ ∈ F.associatedFamily.complex C ∧ τ.card = C.card ↔
      F.IsCell τ C := by
  constructor
  · rintro ⟨hτ, hcard⟩
    have hassoc : F.IsAssociatedSimplex C τ := (Finset.mem_filter.mp hτ).2
    rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg hC.ne_empty] at hassoc
    rcases hassoc with rfl | ⟨σ, hσcell, hτσ⟩
    · have : 0 < C.card := Finset.card_pos.mpr hC
      simp at hcard
      omega
    · have hτσeq : τ = σ := Finset.eq_of_subset_of_card_le hτσ (by
        rw [hcard, hσcell.2])
      simpa [hτσeq] using hσcell
  · intro hcell
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hcell.2⟩
    rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg hC.ne_empty]
    exact Or.inr ⟨τ, hcell, Finset.Subset.rfl⟩

omit [Nonempty V] in
/-- For associated order complexes, the solutions counted by Theorem 6.5 are
definitionally the colorful cells counted by classical Scarf. -/
theorem isSolution_associated_iff_colorful
    (F : IndexedLinearOrders I V) (c : V → I) (C : Finset I) (τ : Finset V) :
    MatroidColoring.IsSolution F.associatedFamily (simplexFramework I)
        (liftColoring F.associatedFamily c) C τ ↔
      F.IsCell τ C ∧ τ.image c = C := by
  rw [isSolution_liftColoring_iff]
  constructor
  · rintro ⟨hτ, hC, hcard, hcolor⟩
    exact ⟨(mem_associated_top_iff_isCell F hC).mp ⟨hτ, hcard⟩, hcolor⟩
  · rintro ⟨hcell, hcolor⟩
    have hC := hcell.1.1
    obtain ⟨hτ, hcard⟩ := (mem_associated_top_iff_isCell F hC).mpr hcell
    exact ⟨hτ, hC, hcard, hcolor⟩

omit [Nonempty V] in theorem solutionPairs_associated_eq_colorfulCellPairs
    (F : IndexedLinearOrders I V) (c : V → I) :
    MatroidColoring.solutionPairs F.associatedFamily (simplexFramework I)
        (liftColoring F.associatedFamily c) = colorfulCellPairs F c := by
  ext p
  simp only [MatroidColoring.solutionPairs, colorfulCellPairs, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact isSolution_associated_iff_colorful F c p.1 p.2

/-- Classical Scarf theorem (Theorem 1.9): the number of colorful cells is
odd, and in particular at least one exists. -/
theorem classicalScarf_odd
    (F : IndexedLinearOrders I V) (c : V → I) :
    (colorfulCellPairs F c).Nonempty ∧ Odd (colorfulCellPairs F c).card := by
  have h := MatroidColoring.theorem6_5 F.associatedFamily (simplexFramework I)
    F.associatedFamily_isChainSimplex simplexFramework_isNondegenerate
    (liftColoring F.associatedFamily c)
  rwa [solutionPairs_associated_eq_colorfulCellPairs F c] at h

/-- Existence form of classical Scarf's theorem, used in Section 3. -/
theorem exists_colorfulCell
    (F : IndexedLinearOrders I V) (c : V → I) :
    ∃ C : Finset I, ∃ σ : Finset V,
      F.IsCell σ C ∧ σ.image c = C := by
  obtain ⟨p, hp⟩ := (classicalScarf_odd F c).1
  exact ⟨p.1, p.2, (Finset.mem_filter.mp hp).2⟩

end Theorem

end ClassicalScarf

end BeyondSperner
