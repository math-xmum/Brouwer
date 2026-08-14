import BeyondSperner.Simplicial.ChainSimplex
import Mathlib.Data.Sum.Order

/-!
# Families of linear orders and dominant sets

The definitions in Section 2 and the extended orders used in Sections 7--8.  This module is
independent of the older game-theory implementation.
-/

namespace BeyondSperner

open Classical

/-- A family of linear orders on `X`, indexed by `I`. -/
structure IndexedLinearOrders (I X : Type*) where
  order : I → LinearOrder X

namespace IndexedLinearOrders

variable {I X : Type*}

instance : FunLike (IndexedLinearOrders I X) I (LinearOrder X) where
  coe F := F.order
  coe_injective F G h := by cases F; cases G; congr

/--
Dominance with respect to `C`, in the quantifier form equivalent to Ivanov's minimum-based
definition.  The explicit `C.Nonempty` records the paper's convention: `∅` is dominant with
respect to every nonempty `C`, but no set is dominant with respect to `∅`.
-/
def IsDominant [Fintype X] [DecidableEq I]
    (F : IndexedLinearOrders I X) (σ : Finset X) (C : Finset I) : Prop :=
  C.Nonempty ∧
    ∀ y : X, ∃ i ∈ C, ∀ x ∈ σ, (F i).le y x

/-- A `C`-cell is a dominant set having exactly `|C|` elements. -/
def IsCell [Fintype X] [DecidableEq I]
    (F : IndexedLinearOrders I X) (σ : Finset X) (C : Finset I) : Prop :=
  F.IsDominant σ C ∧ σ.card = C.card

/-- Dominance is invariant under simultaneous equivalences of the index and
vertex types, provided the corresponding linear orders agree. -/
theorem isDominant_image_iff {J Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq I] [DecidableEq J]
    [DecidableEq X] [DecidableEq Y]
    (F : IndexedLinearOrders I X) (G : IndexedLinearOrders J Y)
    (eI : I ≃ J) (eX : X ≃ Y)
    (horder : ∀ i x y,
      (F i).le x y ↔ (G (eI i)).le (eX x) (eX y))
    (sigma : Finset X) (C : Finset I) :
    G.IsDominant (sigma.image eX) (C.image eI) ↔
      F.IsDominant sigma C := by
  constructor
  · intro hG
    refine ⟨?_, ?_⟩
    · simpa using hG.1
    · intro y
      obtain ⟨j, hjC, hj⟩ := hG.2 (eX y)
      obtain ⟨i, hiC, rfl⟩ := Finset.mem_image.mp hjC
      refine ⟨i, hiC, ?_⟩
      intro x hx
      exact (horder i y x).2
        (hj (eX x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  · intro hF
    refine ⟨?_, ?_⟩
    · simpa using hF.1
    · intro y
      obtain ⟨i, hiC, hi⟩ := hF.2 (eX.symm y)
      refine ⟨eI i, Finset.mem_image.mpr ⟨i, hiC, rfl⟩, ?_⟩
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      simpa using (horder i (eX.symm y) x).1 (hi x hx)

/-- Cellhood is invariant under the same simultaneous relabeling. -/
theorem isCell_image_iff {J Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq I] [DecidableEq J]
    [DecidableEq X] [DecidableEq Y]
    (F : IndexedLinearOrders I X) (G : IndexedLinearOrders J Y)
    (eI : I ≃ J) (eX : X ≃ Y)
    (horder : ∀ i x y,
      (F i).le x y ↔ (G (eI i)).le (eX x) (eX y))
    (sigma : Finset X) (C : Finset I) :
    G.IsCell (sigma.image eX) (C.image eI) ↔ F.IsCell sigma C := by
  rw [IsCell, IsCell, isDominant_image_iff F G eI eX horder]
  rw [Finset.card_image_of_injective _ eX.injective,
    Finset.card_image_of_injective _ eI.injective]

/-- A `C`-face is a dominant set of cardinality `|C|-1`. -/
def IsFace [Fintype X] [DecidableEq I]
    (F : IndexedLinearOrders I X) (σ : Finset X) (C : Finset I) : Prop :=
  F.IsDominant σ C ∧ σ.card + 1 = C.card

theorem empty_isDominant [Fintype X] [DecidableEq I]
    (F : IndexedLinearOrders I X) {C : Finset I} (hC : C.Nonempty) :
    F.IsDominant ∅ C := by
  refine ⟨hC, fun _ ↦ ?_⟩
  obtain ⟨i, hi⟩ := hC
  exact ⟨i, hi, by simp⟩

theorem IsDominant.of_subset [Fintype X] [DecidableEq I]
    {F : IndexedLinearOrders I X} {σ τ : Finset X} {C : Finset I}
    (hτ : F.IsDominant τ C) (hστ : σ ⊆ τ) : F.IsDominant σ C := by
  refine ⟨hτ.1, fun y ↦ ?_⟩
  obtain ⟨i, hi, hiy⟩ := hτ.2 y
  exact ⟨i, hi, fun x hx ↦ hiy x (hστ hx)⟩

theorem IsDominant.mono_indices [Fintype X] [DecidableEq I]
    {F : IndexedLinearOrders I X} {σ : Finset X} {C D : Finset I}
    (hC : F.IsDominant σ C) (hCD : C ⊆ D) : F.IsDominant σ D := by
  refine ⟨hC.1.mono hCD, fun y ↦ ?_⟩
  obtain ⟨i, hi, hiy⟩ := hC.2 y
  exact ⟨i, hCD hi, hiy⟩

/-- Lemma 2.1, stated without choosing the minima explicitly. -/
theorem eq_image_min_of_isDominant [Fintype X] [DecidableEq I]
    (F : IndexedLinearOrders I X) {σ : Finset X} {C : Finset I}
    (hσ : σ.Nonempty) (hdom : F.IsDominant σ C) :
    σ = C.image (fun i ↦ @Finset.min' X (F i) σ hσ) := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨i, hiC, hi⟩ := hdom.2 x
    apply Finset.mem_image.mpr
    refine ⟨i, hiC, ?_⟩
    let _ : LinearOrder X := F i
    exact le_antisymm (Finset.min'_le σ x hx)
      (hi (Finset.min' σ hσ) (Finset.min'_mem σ hσ))
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact @Finset.min'_mem X (F i) σ hσ

/-- Corollary 2.2. -/
theorem card_le_of_isDominant [Fintype X] [DecidableEq I]
    (F : IndexedLinearOrders I X) {σ : Finset X} {C : Finset I}
    (hdom : F.IsDominant σ C) : σ.card ≤ C.card := by
  by_cases hσ : σ.Nonempty
  · rw [F.eq_image_min_of_isDominant hσ hdom]
    exact Finset.card_image_le
  · rw [Finset.not_nonempty_iff_eq_empty.mp hσ]
    simp

/--
If the image of a finite map has exactly one fewer element than its domain, exactly two domain
elements can be erased without changing the image.  This is the finite-map core of the pair
`{k,l}` occurring before Lemma 2.3.
-/
private theorem card_erasable_eq_two {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → β)
    (himage : s.image f = t) (hcard : s.card = t.card + 1) :
    (s.filter fun a ↦ (s.erase a).image f = t).card = 2 := by
  have himage_lt : (s.image f).card < s.card := by
    rw [himage, hcard]
    omega
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_image_lt himage_lt
  have herase_a : (s.erase a).image f = t := by
    rw [← himage]
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨x, (Finset.erase_subset a s) hx, rfl⟩
    · intro hy
      obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hy
      by_cases hxa : x = a
      · subst x
        exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨hab.symm, hb⟩,
          hfab.symm.trans hfx⟩
      · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxa, hx⟩, hfx⟩
  have herase_b : (s.erase b).image f = t := by
    rw [← himage]
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨x, (Finset.erase_subset b s) hx, rfl⟩
    · intro hy
      obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hy
      by_cases hxb : x = b
      · subst x
        exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hab, ha⟩,
          hfab.trans hfx⟩
      · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxb, hx⟩, hfx⟩
  have hfilter : s.filter (fun x ↦ (s.erase x).image f = t) = {a, b} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxs, hximage⟩
      by_contra hx
      push Not at hx
      have hcard_erase : (s.erase x).card = t.card := by
        have := Finset.card_erase_add_one hxs
        omega
      have hinj : Set.InjOn f (s.erase x) :=
        Finset.injOn_of_card_image_eq (by rw [hximage, hcard_erase])
      exact hab (hinj (Finset.mem_erase.mpr ⟨hx.1.symm, ha⟩)
        (Finset.mem_erase.mpr ⟨hx.2.symm, hb⟩) hfab)
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨ha, herase_a⟩
      · exact ⟨hb, herase_b⟩
  rw [hfilter]
  simp [hab]

section AssociatedFamily

variable [Fintype I] [Fintype X] [Nonempty X] [DecidableEq I] [DecidableEq X]

/-- The minimum of a fixed nonempty set in the order indexed by `i`. -/
private noncomputable def minimumOn (F : IndexedLinearOrders I X) (σ : Finset X)
    (hσ : σ.Nonempty) (i : I) : X :=
  @Finset.min' X (F i) σ hσ

/--
The indices which can be removed from the minimum map without changing its image.  For a nonempty
`C`-face these are exactly the two indices denoted `k,l` in Section 2.
-/
private noncomputable def exceptionalIndices (F : IndexedLinearOrders I X) (σ : Finset X)
    (hσ : σ.Nonempty) (C : Finset I) : Finset I :=
  C.filter fun j ↦ (C.erase j).image (minimumOn F σ hσ) = σ

omit [Fintype I] [Nonempty X] in private theorem image_minimumOn_eq_of_isDominant (F : IndexedLinearOrders I X)
    {σ : Finset X} (hσ : σ.Nonempty) {C : Finset I} (hdom : F.IsDominant σ C) :
    C.image (minimumOn F σ hσ) = σ := by
  have himage := (F.eq_image_min_of_isDominant hσ hdom).symm
  ext x
  have hmem := Finset.ext_iff.mp himage x
  constructor
  · intro hx
    apply hmem.mp
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    exact (@Finset.mem_image I X (Classical.decEq X) _ C x).mpr
      ⟨i, hi, by simpa [minimumOn] using hix⟩
  · intro hx
    obtain ⟨i, hi, hix⟩ :=
      (@Finset.mem_image I X (Classical.decEq X) _ C x).mp (hmem.mpr hx)
    exact Finset.mem_image.mpr ⟨i, hi, by simpa [minimumOn] using hix⟩

omit [Fintype I] [Nonempty X] in
/-- A nonempty `C`-face has exactly two exceptional indices. -/
private theorem card_exceptionalIndices_eq_two (F : IndexedLinearOrders I X)
    {σ : Finset X} {C : Finset I} (hσ : σ.Nonempty) (hface : F.IsFace σ C) :
    (exceptionalIndices F σ hσ C).card = 2 := by
  apply card_erasable_eq_two C σ (minimumOn F σ hσ)
  · exact image_minimumOn_eq_of_isDominant F hσ hface.1
  · exact hface.2.symm

/-- The set `M_j` from Section 2. -/
private noncomputable def escapeSet (F : IndexedLinearOrders I X) (σ : Finset X)
    (hσ : σ.Nonempty) (C : Finset I) (j : I) : Finset X :=
  Finset.univ.filter fun y ↦
    ∀ i ∈ C.erase j, (F i).lt (minimumOn F σ hσ i) y

omit [Nonempty X] [DecidableEq X] in
/-- `M_j` is nonempty exactly when `σ` fails to be dominant after deleting `j`. -/
private theorem escapeSet_nonempty_iff_not_isDominant (F : IndexedLinearOrders I X)
    {σ : Finset X} (hσ : σ.Nonempty) {C : Finset I} {j : I}
    (hCj : (C.erase j).Nonempty) :
    (escapeSet F σ hσ C j).Nonempty ↔ ¬ F.IsDominant σ (C.erase j) := by
  constructor
  · rintro ⟨y, hy⟩ hdom
    have hyM := (Finset.mem_filter.mp hy).2
    obtain ⟨i, hi, hiy⟩ := hdom.2 y
    have hlt := hyM i hi
    let _ : LinearOrder X := F i
    exact (not_le_of_gt hlt) (hiy (minimumOn F σ hσ i)
      (by simpa [minimumOn] using @Finset.min'_mem X (F i) σ hσ))
  · intro hnot
    by_contra hM
    apply hnot
    refine ⟨hCj, ?_⟩
    intro y
    have hy : y ∉ escapeSet F σ hσ C j := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hM]
      simp
    simp only [escapeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    push Not at hy
    obtain ⟨i, hi, hyle⟩ := hy
    refine ⟨i, hi, fun x hx ↦ ?_⟩
    let _ : LinearOrder X := F i
    exact hyle.trans (by simpa [minimumOn] using Finset.min'_le σ x hx)

/-- The point `m_j`, with an irrelevant default value when `M_j` is empty. -/
private noncomputable def extensionPoint (F : IndexedLinearOrders I X) (σ : Finset X)
    (hσ : σ.Nonempty) (C : Finset I) (j : I) : X :=
  if hM : (escapeSet F σ hσ C j).Nonempty then
    @Finset.max' X (F j) (escapeSet F σ hσ C j) hM
  else Classical.choice inferInstance

omit [DecidableEq X] in private theorem extensionPoint_mem_escapeSet (F : IndexedLinearOrders I X)
    {σ : Finset X} (hσ : σ.Nonempty) {C : Finset I} {j : I}
    (hM : (escapeSet F σ hσ C j).Nonempty) :
    extensionPoint F σ hσ C j ∈ escapeSet F σ hσ C j := by
  rw [extensionPoint, dif_pos hM]
  exact @Finset.max'_mem X (F j) _ hM

omit [DecidableEq X] in private theorem le_extensionPoint (F : IndexedLinearOrders I X)
    {σ : Finset X} (hσ : σ.Nonempty) {C : Finset I} {j : I}
    (hM : (escapeSet F σ hσ C j).Nonempty) {y : X}
    (hy : y ∈ escapeSet F σ hσ C j) :
    (F j).le y (extensionPoint F σ hσ C j) := by
  rw [extensionPoint, dif_pos hM]
  exact @Finset.le_max' X (F j) _ y hy

/-- Lemma 2.3, in the direction constructing a cell from a nonempty `M_j`. -/
private theorem extensionPoint_isCell (F : IndexedLinearOrders I X)
    {σ : Finset X} (hσ : σ.Nonempty) {C : Finset I} {j : I}
    (hface : F.IsFace σ C) (hj : j ∈ exceptionalIndices F σ hσ C)
    (hnot : ¬ F.IsDominant σ (C.erase j)) :
    F.IsCell (insert (extensionPoint F σ hσ C j) σ) C := by
  have hjC : j ∈ C := (Finset.mem_filter.mp hj).1
  have himage : (C.erase j).image (minimumOn F σ hσ) = σ :=
    (Finset.mem_filter.mp hj).2
  have hCjcard : (C.erase j).card = σ.card := by
    have hfacecard : σ.card + 1 = C.card := hface.2
    rw [Finset.card_erase_of_mem hjC]
    omega
  have hCj : (C.erase j).Nonempty := by
    apply Finset.card_pos.mp
    rw [hCjcard]
    exact Finset.card_pos.mpr hσ
  have hM : (escapeSet F σ hσ C j).Nonempty :=
    (escapeSet_nonempty_iff_not_isDominant F hσ hCj).2 hnot
  let a := extensionPoint F σ hσ C j
  have haM : a ∈ escapeSet F σ hσ C j :=
    extensionPoint_mem_escapeSet F hσ hM
  have haM' : ∀ i ∈ C.erase j, (F i).lt (minimumOn F σ hσ i) a :=
    (Finset.mem_filter.mp haM).2
  have haσ : a ∉ σ := by
    intro ha
    have haimage : a ∈ (C.erase j).image (minimumOn F σ hσ) :=
      (Finset.ext_iff.mp himage a).mpr ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp haimage
    have hlt := haM' i hi
    let _ : LinearOrder X := F i
    exact (ne_of_lt hlt) hia
  have haj : ∀ x ∈ σ, (F j).le a x := by
    obtain ⟨i, hiC, hia⟩ := hface.1.2 a
    have hij : i = j := by
      by_contra hij
      have hiErase : i ∈ C.erase j := Finset.mem_erase.mpr ⟨hij, hiC⟩
      have hlt := haM' i hiErase
      have hale := hia (minimumOn F σ hσ i)
        (by simpa [minimumOn] using @Finset.min'_mem X (F i) σ hσ)
      let _ : LinearOrder X := F i
      exact (not_le_of_gt hlt) hale
    subst i
    exact hia
  refine ⟨?_, ?_⟩
  · refine ⟨hface.1.1, fun y ↦ ?_⟩
    by_cases hy : (F j).le y a
    · refine ⟨j, hjC, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hy
      · let _ : LinearOrder X := F j
        exact hy.trans (haj x hx)
    · have hay : (F j).lt a y := by
        let _ : LinearOrder X := F j
        exact lt_of_not_ge hy
      have hyM : y ∉ escapeSet F σ hσ C j := by
        intro hyM
        have hya := le_extensionPoint F hσ hM hyM
        let _ : LinearOrder X := F j
        exact (not_le_of_gt hay) hya
      simp only [escapeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hyM
      push Not at hyM
      obtain ⟨i, hi, hymin⟩ := hyM
      refine ⟨i, (Finset.mem_erase.mp hi).2, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxσ
      · let _ : LinearOrder X := F i
        exact hymin.trans (le_of_lt (haM' i hi))
      · have hminx : (F i).le (minimumOn F σ hσ i) x := by
          let _ : LinearOrder X := F i
          simpa [minimumOn] using Finset.min'_le σ x hxσ
        let _ : LinearOrder X := F i
        exact hymin.trans hminx
  · rw [Finset.card_insert_of_notMem haσ]
    exact hface.2

private theorem extensionPoint_not_mem (F : IndexedLinearOrders I X)
    {σ : Finset X} (hσ : σ.Nonempty) {C : Finset I} {j : I}
    (hface : F.IsFace σ C) (hj : j ∈ exceptionalIndices F σ hσ C)
    (hnot : ¬ F.IsDominant σ (C.erase j)) :
    extensionPoint F σ hσ C j ∉ σ := by
  intro hmem
  have hcell := extensionPoint_isCell F hσ hface hj hnot
  have hcard := hcell.2
  have hfacecard : σ.card + 1 = C.card := hface.2
  rw [Finset.insert_eq_of_mem hmem] at hcard
  omega

/-- Lemma 2.4: the cells constructed from distinct exceptional indices are distinct. -/
private theorem extensionPoint_injOn (F : IndexedLinearOrders I X)
    {σ : Finset X} (hσ : σ.Nonempty) {C : Finset I} (hface : F.IsFace σ C) :
    Set.InjOn (fun j ↦ insert (extensionPoint F σ hσ C j) σ)
      {j | j ∈ exceptionalIndices F σ hσ C ∧
        ¬ F.IsDominant σ (C.erase j)} := by
  intro j hj k hk heq
  have hjC : j ∈ C := (Finset.mem_filter.mp hj.1).1
  have hkC : k ∈ C := (Finset.mem_filter.mp hk.1).1
  have hfacecard : σ.card + 1 = C.card := hface.2
  have hCjcard : (C.erase j).card = σ.card := by
    have hfacecard : σ.card + 1 = C.card := hface.2
    rw [Finset.card_erase_of_mem hjC]
    omega
  have hCkcard : (C.erase k).card = σ.card := by
    rw [Finset.card_erase_of_mem hkC]
    omega
  have hCj : (C.erase j).Nonempty := by
    apply Finset.card_pos.mp
    rw [hCjcard]
    exact Finset.card_pos.mpr hσ
  have hCk : (C.erase k).Nonempty := by
    apply Finset.card_pos.mp
    rw [hCkcard]
    exact Finset.card_pos.mpr hσ
  have hjM : (escapeSet F σ hσ C j).Nonempty :=
    (escapeSet_nonempty_iff_not_isDominant F hσ hCj).2 hj.2
  have hkM : (escapeSet F σ hσ C k).Nonempty :=
    (escapeSet_nonempty_iff_not_isDominant F hσ hCk).2 hk.2
  let a := extensionPoint F σ hσ C j
  let b := extensionPoint F σ hσ C k
  have haσ : a ∉ σ := extensionPoint_not_mem F hσ hface hj.1 hj.2
  have hab : a = b := (Finset.insert_inj haσ).mp heq
  have haM : a ∈ escapeSet F σ hσ C j := extensionPoint_mem_escapeSet F hσ hjM
  have hbM : b ∈ escapeSet F σ hσ C k := extensionPoint_mem_escapeSet F hσ hkM
  have haM' := (Finset.mem_filter.mp haM).2
  have hbM' := (Finset.mem_filter.mp hbM).2
  obtain ⟨i, hiC, hia⟩ := hface.1.2 a
  have hij : i = j := by
    by_contra hij
    have hi : i ∈ C.erase j := Finset.mem_erase.mpr ⟨hij, hiC⟩
    have hlt := haM' i hi
    have hle := hia (minimumOn F σ hσ i)
      (by simpa [minimumOn] using @Finset.min'_mem X (F i) σ hσ)
    let _ : LinearOrder X := F i
    exact (not_le_of_gt hlt) hle
  have hik : i = k := by
    by_contra hik
    have hi : i ∈ C.erase k := Finset.mem_erase.mpr ⟨hik, hiC⟩
    have hlt : (F i).lt (minimumOn F σ hσ i) a := by
      simpa [hab] using hbM' i hi
    have hle := hia (minimumOn F σ hσ i)
      (by simpa [minimumOn] using @Finset.min'_mem X (F i) σ hσ)
    let _ : LinearOrder X := F i
    exact (not_le_of_gt hlt) hle
  exact hij.symm.trans hik

/-- Every `C`-cell containing a nonempty `C`-face is obtained from its exceptional index. -/
private theorem exists_exceptional_extensionPoint_eq_of_cell
    (F : IndexedLinearOrders I X) {σ : Finset X} (hσ : σ.Nonempty)
    {C : Finset I} (hface : F.IsFace σ C) {τ : Finset X}
    (hcell : F.IsCell τ C) (hστ : σ ⊆ τ) :
    ∃ j ∈ exceptionalIndices F σ hσ C,
      ¬ F.IsDominant σ (C.erase j) ∧
        insert (extensionPoint F σ hσ C j) σ = τ := by
  have hcards : σ.card + 1 = τ.card := hface.2.trans hcell.2.symm
  obtain ⟨a, haσ, haτ⟩ := Finset.exists_eq_insert_iff.mpr ⟨hστ, hcards⟩
  have hτ : τ.Nonempty := hσ.mono hστ
  let mτ : I → X := fun i ↦ @Finset.min' X (F i) τ hτ
  have hmτ_mem (i : I) : mτ i ∈ τ := by
    simpa [mτ] using @Finset.min'_mem X (F i) τ hτ
  have hτimage := F.eq_image_min_of_isDominant hτ hcell.1
  let g : {i // i ∈ C} → {x // x ∈ τ} := fun i ↦ ⟨mτ i, hmτ_mem i⟩
  have hgsurj : Function.Surjective g := by
    intro x
    have hximage := (Finset.ext_iff.mp hτimage x.1).mp x.2
    obtain ⟨i, hiC, hix⟩ :=
      (@Finset.mem_image I X (Classical.decEq X) _ C x.1).mp hximage
    refine ⟨⟨i, hiC⟩, Subtype.ext ?_⟩
    simpa [g, mτ] using hix
  have hgcard : Fintype.card {i // i ∈ C} = Fintype.card {x // x ∈ τ} := by
    simpa using hcell.2.symm
  have hginj : Function.Injective g :=
    ((Fintype.bijective_iff_surjective_and_card g).2 ⟨hgsurj, hgcard⟩).1
  have haτmem : a ∈ τ := by
    rw [← haτ]
    simp
  obtain ⟨jsub, hjg⟩ := hgsurj ⟨a, haτmem⟩
  let j : I := jsub.1
  have hjC : j ∈ C := jsub.2
  have hmτj : mτ j = a := Subtype.ext_iff.mp hjg
  have hmτ_ne_a {i : I} (hi : i ∈ C.erase j) : mτ i ≠ a := by
    intro hia
    have hgi : g ⟨i, (Finset.mem_erase.mp hi).2⟩ = g jsub := by
      apply Subtype.ext
      exact hia.trans hmτj.symm
    have hij := Subtype.ext_iff.mp (hginj hgi)
    exact (Finset.mem_erase.mp hi).1 hij
  have hmτ_mem_σ {i : I} (hi : i ∈ C.erase j) : mτ i ∈ σ := by
    have hiτ := hmτ_mem i
    rw [← haτ] at hiτ
    rcases Finset.mem_insert.mp hiτ with hia | hiσ
    · exact (hmτ_ne_a hi hia).elim
    · exact hiσ
  have hminimum_eq {i : I} (hi : i ∈ C.erase j) :
      minimumOn F σ hσ i = mτ i := by
    let _ : LinearOrder X := F i
    apply le_antisymm
    · simpa [minimumOn] using Finset.min'_le σ (mτ i) (hmτ_mem_σ hi)
    · have hminστ : @Finset.min' X (F i) τ hτ ≤ minimumOn F σ hσ i :=
        Finset.min'_le τ _ (hστ (by simpa [minimumOn] using
          (@Finset.min'_mem X (F i) σ hσ)))
      change @Finset.min' X (F i) τ hτ ≤ minimumOn F σ hσ i
      exact hminστ
  have hjexceptional : j ∈ exceptionalIndices F σ hσ C := by
    apply Finset.mem_filter.mpr
    refine ⟨hjC, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [hminimum_eq hi]
      exact hmτ_mem_σ hi
    · intro hxσ
      have hxτ : x ∈ τ := hστ hxσ
      obtain ⟨isub, hig⟩ := hgsurj ⟨x, hxτ⟩
      have hmi : mτ isub.1 = x := Subtype.ext_iff.mp hig
      have hij : isub.1 ≠ j := by
        intro hij
        have hisub : isub = jsub := Subtype.ext hij
        subst isub
        exact haσ (hmτj.symm.trans hmi ▸ hxσ)
      have hiErase : isub.1 ∈ C.erase j :=
        Finset.mem_erase.mpr ⟨hij, isub.2⟩
      exact Finset.mem_image.mpr ⟨isub.1, hiErase,
        (hminimum_eq hiErase).trans hmi⟩
  have hCjcard : (C.erase j).card = σ.card := by
    have hfacecard : σ.card + 1 = C.card := hface.2
    rw [Finset.card_erase_of_mem hjC]
    omega
  have hCj : (C.erase j).Nonempty := by
    apply Finset.card_pos.mp
    rw [hCjcard]
    exact Finset.card_pos.mpr hσ
  have haM : a ∈ escapeSet F σ hσ C j := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, fun i hi ↦ ?_⟩
    have hle : (F i).le (mτ i) a := by
      simpa [mτ, hmτj] using @Finset.min'_le X (F i) τ a haτmem
    have hne : mτ i ≠ a := hmτ_ne_a hi
    let _ : LinearOrder X := F i
    rw [hminimum_eq hi]
    exact lt_of_le_of_ne hle hne
  have hnot : ¬ F.IsDominant σ (C.erase j) :=
    (escapeSet_nonempty_iff_not_isDominant F hσ hCj).1 ⟨a, haM⟩
  have hM : (escapeSet F σ hσ C j).Nonempty := ⟨a, haM⟩
  have heM : extensionPoint F σ hσ C j ∈ escapeSet F σ hσ C j :=
    extensionPoint_mem_escapeSet F hσ hM
  have he_le_a : (F j).le (extensionPoint F σ hσ C j) a := by
    obtain ⟨i, hiC, hie⟩ := hcell.1.2 (extensionPoint F σ hσ C j)
    have hij : i = j := by
      by_contra hij
      have hi : i ∈ C.erase j := Finset.mem_erase.mpr ⟨hij, hiC⟩
      have hlt := (Finset.mem_filter.mp heM).2 i hi
      have hle := hie (mτ i) (hmτ_mem i)
      let _ : LinearOrder X := F i
      rw [hminimum_eq hi] at hlt
      exact (not_le_of_gt hlt) hle
    subst i
    exact hie a haτmem
  have ha_le_e : (F j).le a (extensionPoint F σ hσ C j) :=
    le_extensionPoint F hσ hM haM
  have hea : extensionPoint F σ hσ C j = a := by
    let _ : LinearOrder X := F j
    exact le_antisymm he_le_a ha_le_e
  exact ⟨j, hjexceptional, hnot, by simpa [hea] using haτ⟩

private theorem card_cells_containing_eq_card_exceptional_not_dominant
    (F : IndexedLinearOrders I X) {σ : Finset X} (hσ : σ.Nonempty)
    {C : Finset I} (hface : F.IsFace σ C) :
    (Finset.univ.filter fun τ ↦ F.IsCell τ C ∧ σ ⊆ τ).card =
      ((exceptionalIndices F σ hσ C).filter fun j ↦
        ¬ F.IsDominant σ (C.erase j)).card := by
  let E := (exceptionalIndices F σ hσ C).filter fun j ↦
    ¬ F.IsDominant σ (C.erase j)
  let addPoint : I → Finset X := fun j ↦ insert (extensionPoint F σ hσ C j) σ
  have himage : E.image addPoint =
      Finset.univ.filter (fun τ ↦ F.IsCell τ C ∧ σ ⊆ τ) := by
    ext τ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' := (Finset.mem_filter.mp hj)
      exact ⟨extensionPoint_isCell F hσ hface hj'.1 hj'.2,
        Finset.subset_insert _ _⟩
    · rintro ⟨hcell, hsub⟩
      obtain ⟨j, hj, hnot, hjcell⟩ :=
        exists_exceptional_extensionPoint_eq_of_cell F hσ hface hcell hsub
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, hnot⟩, hjcell⟩
  have hinj : Set.InjOn addPoint E := by
    apply (extensionPoint_injOn F hσ hface).mono
    intro j hj
    exact Finset.mem_filter.mp hj
  rw [← himage, Finset.card_image_of_injOn hinj]

omit [Fintype I] [Nonempty X] in private theorem card_boundary_cells_eq_card_exceptional_dominant
    (F : IndexedLinearOrders I X) {σ : Finset X} (hσ : σ.Nonempty)
    {C : Finset I} (hface : F.IsFace σ C) :
    ((SimplexFamily.boundaryIndices C).filter fun B ↦ F.IsCell σ B).card =
      ((exceptionalIndices F σ hσ C).filter fun j ↦
        F.IsDominant σ (C.erase j)).card := by
  let E := (exceptionalIndices F σ hσ C).filter fun j ↦
    F.IsDominant σ (C.erase j)
  let drop : I → Finset I := fun j ↦ C.erase j
  have himage : E.image drop =
      (SimplexFamily.boundaryIndices C).filter fun B ↦ F.IsCell σ B := by
    ext B
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' := Finset.mem_filter.mp hj
      have hjC : j ∈ C := (Finset.mem_filter.mp hj'.1).1
      have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨j, hjC⟩
      refine ⟨?_, hj'.2, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (Finset.erase_subset j C), ?_⟩
        rw [Finset.card_erase_of_mem hjC]
        omega
      · rw [Finset.card_erase_of_mem hjC]
        have hfacecard : σ.card + 1 = C.card := hface.2
        omega
    · rintro ⟨hBboundary, hBcell⟩
      have hBdata := Finset.mem_filter.mp hBboundary
      have hBC : B ⊆ C := Finset.mem_powerset.mp hBdata.1
      obtain ⟨j, hjB, hjinsert⟩ := Finset.exists_eq_insert_iff.mpr ⟨hBC, hBdata.2⟩
      have hjC : j ∈ C := by rw [← hjinsert]; simp
      have hdrop : C.erase j = B := by
        rw [← hjinsert]
        simp [hjB]
      refine ⟨j, Finset.mem_filter.mpr ⟨?_, ?_⟩, hdrop⟩
      · apply Finset.mem_filter.mpr
        refine ⟨hjC, ?_⟩
        rw [hdrop]
        exact image_minimumOn_eq_of_isDominant F hσ hBcell.1
      · simpa [hdrop] using hBcell.1
  have hinj : Set.InjOn drop E := by
    intro j hj k hk hjk
    apply C.erase_injOn
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
    · exact hjk
  rw [← himage, Finset.card_image_of_injOn hinj]

/-- Theorem 2.6, expressed directly as the sum of the two finite incidence counts. -/
private theorem mainCombinatorialLemma (F : IndexedLinearOrders I X)
    {σ : Finset X} (hσ : σ.Nonempty) {C : Finset I} (hface : F.IsFace σ C) :
    (Finset.univ.filter fun τ ↦ F.IsCell τ C ∧ σ ⊆ τ).card +
      ((SimplexFamily.boundaryIndices C).filter fun B ↦ F.IsCell σ B).card = 2 := by
  rw [card_cells_containing_eq_card_exceptional_not_dominant F hσ hface,
    card_boundary_cells_eq_card_exceptional_dominant F hσ hface, add_comm,
    Finset.card_filter_add_card_filter_not,
    card_exceptionalIndices_eq_two F hσ hface]

/-- The simplices of the complex `T(A)` associated with a family of orders. -/
def IsAssociatedSimplex (F : IndexedLinearOrders I X)
    (A : Finset I) (τ : Finset X) : Prop :=
  if A = ∅ then τ = ∅
  else τ = ∅ ∨ ∃ σ : Finset X, F.IsCell σ A ∧ τ ⊆ σ

omit [Fintype I] [Nonempty X] [DecidableEq X] in
/-- The associated-simplex predicate is closed under taking faces. -/
theorem IsAssociatedSimplex.of_subset (F : IndexedLinearOrders I X)
    {A : Finset I} {σ τ : Finset X} (hσ : F.IsAssociatedSimplex A σ)
    (hτσ : τ ⊆ σ) : F.IsAssociatedSimplex A τ := by
  by_cases hA : A = ∅
  · rw [IsAssociatedSimplex, if_pos hA] at hσ ⊢
    subst σ
    exact Finset.Subset.antisymm hτσ (Finset.empty_subset τ)
  · rw [IsAssociatedSimplex, if_neg hA] at hσ ⊢
    rcases hσ with rfl | ⟨ρ, hρcell, hσρ⟩
    · left
      exact Finset.Subset.antisymm hτσ (Finset.empty_subset τ)
    · right
      exact ⟨ρ, hρcell, hτσ.trans hσρ⟩

/-- The complex `T(A)` whose facets are the `A`-cells. -/
noncomputable def associatedComplex (F : IndexedLinearOrders I X) (A : Finset I) :
    FiniteSimplicialComplex X where
  simplices := Finset.univ.filter fun τ ↦ F.IsAssociatedSimplex A τ
  empty_mem := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hA : A = ∅
    · rw [IsAssociatedSimplex, if_pos hA]
    · rw [IsAssociatedSimplex, if_neg hA]
      exact Or.inl rfl
  downward_closed := by
    intro σ τ hσ hτσ
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, IsAssociatedSimplex.of_subset F
      (Finset.mem_filter.mp hσ).2 hτσ⟩

omit [Fintype I] [Nonempty X] in
/-- Associated simplices are invariant under simultaneous relabeling of
indices and vertices when the corresponding orders agree. -/
theorem isAssociatedSimplex_image_iff {J Y : Type*}
    [Fintype J] [Fintype Y] [Nonempty Y]
    [DecidableEq J] [DecidableEq Y]
    (F : IndexedLinearOrders I X) (G : IndexedLinearOrders J Y)
    (eI : I ≃ J) (eX : X ≃ Y)
    (horder : ∀ i x y,
      (F i).le x y ↔ (G (eI i)).le (eX x) (eX y))
    (tau : Finset X) (A : Finset I) :
    G.IsAssociatedSimplex (A.image eI) (tau.image eX) ↔
      F.IsAssociatedSimplex A tau := by
  by_cases hA : A = ∅
  · subst A
    simp [IsAssociatedSimplex]
  · have hAimage : A.image eI ≠ ∅ := by
      simpa using hA
    rw [IsAssociatedSimplex, if_neg hAimage,
      IsAssociatedSimplex, if_neg hA]
    constructor
    · intro hG
      rcases hG with hzero | ⟨rho, hrho, hsub⟩
      · left
        exact (Finset.image_eq_empty.mp hzero)
      · right
        let sigma : Finset X := rho.image eX.symm
        have hsigmaImage : sigma.image eX = rho := by
          ext y
          simp [sigma]
        refine ⟨sigma, ?_, ?_⟩
        · apply (isCell_image_iff F G eI eX horder sigma A).1
          simpa [hsigmaImage] using hrho
        · intro x hx
          have hex : eX x ∈ tau.image eX :=
            Finset.mem_image.mpr ⟨x, hx, rfl⟩
          have herho : eX x ∈ rho := hsub hex
          exact Finset.mem_image.mpr ⟨eX x, herho, eX.symm_apply_apply x⟩
    · intro hF
      rcases hF with rfl | ⟨sigma, hsigma, hsub⟩
      · exact Or.inl (by simp)
      · exact Or.inr ⟨sigma.image eX,
          (isCell_image_iff F G eI eX horder sigma A).2 hsigma,
          Finset.image_mono eX hsub⟩

omit [Fintype I] [Nonempty X] in
/-- Consequently the associated complexes themselves are exactly related by
`FiniteSimplicialComplex.relabel`; this is an equality of bundled finite
complexes, not an informal identification. -/
theorem associatedComplex_relabel {J Y : Type*}
    [Fintype J] [Fintype Y] [Nonempty Y]
    [DecidableEq J] [DecidableEq Y]
    (F : IndexedLinearOrders I X) (G : IndexedLinearOrders J Y)
    (eI : I ≃ J) (eX : X ≃ Y)
    (horder : ∀ i x y,
      (F i).le x y ↔ (G (eI i)).le (eX x) (eX y))
    (A : Finset I) :
    (F.associatedComplex A).relabel eX =
      G.associatedComplex (A.image eI) := by
  apply FiniteSimplicialComplex.ext
  ext tau
  constructor
  · intro htau
    obtain ⟨sigma, hsigma, hsigmaImage⟩ :=
      (FiniteSimplicialComplex.mem_relabel_iff
        (F.associatedComplex A) eX tau).1 htau
    have hsigmaAssoc : F.IsAssociatedSimplex A sigma :=
      (Finset.mem_filter.mp hsigma).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hsigmaImage]
    exact (isAssociatedSimplex_image_iff F G eI eX horder sigma A).2
      hsigmaAssoc
  · intro htau
    have htauAssoc : G.IsAssociatedSimplex (A.image eI) tau :=
      (Finset.mem_filter.mp htau).2
    let sigma : Finset X := tau.image eX.symm
    have hsigmaImage : sigma.image eX = tau := by
      ext y
      simp [sigma]
    apply (FiniteSimplicialComplex.mem_relabel_iff
      (F.associatedComplex A) eX tau).2
    refine ⟨sigma, ?_, hsigmaImage⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (isAssociatedSimplex_image_iff F G eI eX horder sigma A).1
    simpa [hsigmaImage] using htauAssoc

/-- Scarf's simplex-family associated with the orders. -/
noncomputable def associatedFamily (F : IndexedLinearOrders I X) : SimplexFamily I X where
  complex := F.associatedComplex
  dimension := by
    intro A τ hτ
    have hτsimp : F.IsAssociatedSimplex A τ := (Finset.mem_filter.mp hτ).2
    by_cases hA : A = ∅
    · rw [IsAssociatedSimplex, if_pos hA] at hτsimp
      subst A
      subst τ
      simp
    · rw [IsAssociatedSimplex, if_neg hA] at hτsimp
      rcases hτsimp with rfl | ⟨σ, hσcell, hτσ⟩
      · simp
      · exact (Finset.card_le_card hτσ).trans_eq hσcell.2

omit [Fintype I] [Nonempty X] in private theorem cofaceCount_associated_eq_card_cells (F : IndexedLinearOrders I X)
    {σ : Finset X} {C : Finset I} (hC : C.Nonempty) :
    F.associatedFamily.cofaceCount C σ =
      (Finset.univ.filter fun τ ↦ F.IsCell τ C ∧ σ ⊆ τ).card := by
  apply congrArg Finset.card
  ext τ
  simp only [FiniteSimplicialComplex.topSimplices,
    associatedFamily, associatedComplex, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hassoc, hτcard⟩, hστ⟩
    rw [IsAssociatedSimplex, if_neg hC.ne_empty] at hassoc
    rcases hassoc with hτempty | ⟨ρ, hρcell, hτρ⟩
    · subst τ
      have hCpos : 0 < C.card := Finset.card_pos.mpr hC
      simp at hτcard
      omega
    · have hτρeq : τ = ρ := Finset.eq_of_subset_of_card_le hτρ (by
        rw [hτcard, hρcell.2])
      subst ρ
      exact ⟨hρcell, hστ⟩
  · rintro ⟨hτcell, hστ⟩
    refine ⟨⟨?_, hτcell.2⟩, hστ⟩
    rw [IsAssociatedSimplex, if_neg hC.ne_empty]
    exact Or.inr ⟨τ, hτcell, Finset.Subset.rfl⟩

omit [Fintype I] [Nonempty X] in private theorem boundaryMembershipCount_associated_eq_card_cells
    (F : IndexedLinearOrders I X) {σ : Finset X} (hσ : σ.Nonempty)
    {C : Finset I} (hcard : σ.card + 1 = C.card) :
    F.associatedFamily.boundaryMembershipCount C σ =
      ((SimplexFamily.boundaryIndices C).filter fun B ↦ F.IsCell σ B).card := by
  change ((SimplexFamily.boundaryIndices C).filter
    (fun B ↦ σ ∈ F.associatedComplex B)).card = _
  apply congrArg Finset.card
  ext B
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hBboundary, hassocMem⟩
    refine ⟨hBboundary, ?_⟩
    have hassoc := (Finset.mem_filter.mp hassocMem).2
    have hBdata := Finset.mem_filter.mp hBboundary
    have hBcard : B.card = σ.card := by omega
    have hB : B ≠ ∅ := by
      intro hB
      subst B
      have hσpos : 0 < σ.card := Finset.card_pos.mpr hσ
      simp at hBcard
      omega
    rw [IsAssociatedSimplex, if_neg hB] at hassoc
    rcases hassoc with hσempty | ⟨ρ, hρcell, hσρ⟩
    · exact (hσ.ne_empty hσempty).elim
    · have hσρeq : σ = ρ := Finset.eq_of_subset_of_card_le hσρ (by
        rw [hρcell.2, hBcard])
      simpa [hσρeq] using hρcell
  · rintro ⟨hBboundary, hBcell⟩
    refine ⟨hBboundary, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hB : B ≠ ∅ := hBcell.1.1.ne_empty
    rw [IsAssociatedSimplex, if_neg hB]
    exact Or.inr ⟨σ, hBcell, Finset.Subset.rfl⟩

private noncomputable def orderMaximum (F : IndexedLinearOrders I X) (i : I) : X :=
  @Finset.max' X (F i) Finset.univ Finset.univ_nonempty

omit [Fintype I] [DecidableEq X] in private theorem isCell_singleton_index_iff (F : IndexedLinearOrders I X)
    (i : I) (τ : Finset X) :
    F.IsCell τ {i} ↔ τ = {orderMaximum F i} := by
  constructor
  · intro hcell
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp (by simpa using hcell.2)
    obtain ⟨j, hji, hj⟩ := hcell.1.2 (orderMaximum F i)
    have hji' : j = i := by simpa using hji
    subst j
    have hmax_le : (F i).le (orderMaximum F i) z := hj z (by simp)
    have hz_le : (F i).le z (orderMaximum F i) := by
      simpa [orderMaximum] using
        (@Finset.le_max' X (F i) Finset.univ z (Finset.mem_univ z))
    have hz : z = orderMaximum F i := by
      let _ : LinearOrder X := F i
      exact le_antisymm hz_le hmax_le
    rw [hz]
  · rintro rfl
    refine ⟨⟨Finset.singleton_nonempty i, fun y ↦ ⟨i, by simp, ?_⟩⟩, by simp⟩
    intro z hz
    simp only [Finset.mem_singleton] at hz
    subst z
    simpa [orderMaximum] using
      (@Finset.le_max' X (F i) Finset.univ y (Finset.mem_univ y))

omit [Fintype I] in private theorem empty_incidence_eq_two (F : IndexedLinearOrders I X)
    {C : Finset I} (hCcard : C.card = 1) :
    F.associatedFamily.cofaceCount C ∅ +
      F.associatedFamily.boundaryMembershipCount C ∅ = 2 := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hCcard
  rw [cofaceCount_associated_eq_card_cells F (Finset.singleton_nonempty i)]
  have hcells :
      (Finset.univ.filter fun τ ↦ F.IsCell τ {i} ∧ (∅ : Finset X) ⊆ τ) =
        {{orderMaximum F i}} := by
    ext τ
    simp [isCell_singleton_index_iff F i]
  rw [hcells]
  have hboundary : F.associatedFamily.boundaryMembershipCount {i} ∅ = 1 := by
    change (((SimplexFamily.boundaryIndices {i}).filter
      fun B ↦ (∅ : Finset X) ∈ F.associatedComplex B).card) = 1
    have hset : (SimplexFamily.boundaryIndices {i}).filter
        (fun B ↦ (∅ : Finset X) ∈ F.associatedComplex B) = {∅} := by
      ext B
      simp [SimplexFamily.boundaryIndices, associatedComplex, IsAssociatedSimplex]; aesop
    rw [hset]
    simp
  rw [hboundary]
  simp

omit [Fintype I] [Nonempty X] in private theorem isFace_of_relevant_nonempty (F : IndexedLinearOrders I X)
    {C : Finset I} {σ : Finset X} (hσ : σ.Nonempty)
    (hrel : F.associatedFamily.IsRelevantCodimOne C σ) : F.IsFace σ C := by
  have hrelcard : σ.card + 1 = C.card := hrel.1
  refine ⟨?_, hrel.1⟩
  rcases hrel.2 with hsame | ⟨B, hBboundary, hBmem⟩
  · change σ ∈ F.associatedComplex C at hsame
    have hassoc := (Finset.mem_filter.mp hsame).2
    have hCcard : 0 < C.card := by
      have hσpos : 0 < σ.card := Finset.card_pos.mpr hσ
      omega
    have hC : C ≠ ∅ := (Finset.card_ne_zero.mp (Nat.ne_of_gt hCcard)).ne_empty
    rw [IsAssociatedSimplex, if_neg hC] at hassoc
    rcases hassoc with hσempty | ⟨ρ, hρcell, hσρ⟩
    · exact (hσ.ne_empty hσempty).elim
    · exact hρcell.1.of_subset hσρ
  · have hBdata := Finset.mem_filter.mp hBboundary
    have hBC : B ⊆ C := Finset.mem_powerset.mp hBdata.1
    have hBcard : B.card = σ.card := by omega
    have hB : B ≠ ∅ := by
      intro hB
      subst B
      have hσpos : 0 < σ.card := Finset.card_pos.mpr hσ
      simp at hBcard
      omega
    change σ ∈ F.associatedComplex B at hBmem
    have hassoc := (Finset.mem_filter.mp hBmem).2
    rw [IsAssociatedSimplex, if_neg hB] at hassoc
    rcases hassoc with hσempty | ⟨ρ, hρcell, hσρ⟩
    · exact (hσ.ne_empty hσempty).elim
    · exact (hρcell.1.of_subset hσρ).mono_indices hBC

/-- Theorem 2.7. -/
theorem associatedFamily_isPseudoSimplex (F : IndexedLinearOrders I X) :
    F.associatedFamily.IsPseudoSimplex := by
  intro C σ hrel
  by_cases hσ : σ.Nonempty
  · have hface := isFace_of_relevant_nonempty F hσ hrel
    rw [cofaceCount_associated_eq_card_cells F hface.1.1,
      boundaryMembershipCount_associated_eq_card_cells F hσ hface.2]
    exact mainCombinatorialLemma F hσ hface
  · have hσempty : σ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hσ
    subst σ
    have hrelcard : (∅ : Finset X).card + 1 = C.card := hrel.1
    have hCcard : C.card = 1 := by simpa using hrelcard.symm
    exact empty_incidence_eq_two F hCcard

/-- Corollary 2.9. -/
theorem associatedFamily_isChainSimplex (F : IndexedLinearOrders I X) :
    F.associatedFamily.IsChainSimplex :=
  (F.associatedFamily_isPseudoSimplex).isChainSimplex

end AssociatedFamily

section ExtendedOrders

variable [DecidableEq I] [LinearOrder I]

/--
The three-level key for the `i`-th extended order: first `i`, then all elements of `X` in their
original order, then the remaining formal indices.  The order among the latter is arbitrary in the
paper; the chosen `LinearOrder I` makes it canonical here.
-/
private def extendedOrderKey [LinearOrder X] (i : I) :
    X ⊕ I → ((Unit ⊕ₗ X) ⊕ₗ I)
  | Sum.inl x => toLex (Sum.inl (toLex (Sum.inr x)))
  | Sum.inr j =>
      if j = i then toLex (Sum.inl (toLex (Sum.inl ()))) else toLex (Sum.inr j)

omit [LinearOrder I] in
private theorem extendedOrderKey_injective [LinearOrder X] (i : I) :
    Function.Injective (extendedOrderKey (X := X) i) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          simp only [extendedOrderKey, toLex_inj, Sum.inl.injEq] at hxy
          exact congrArg Sum.inl (Sum.inr.inj hxy)
      | inr y =>
          by_cases hy : y = i <;> simp [extendedOrderKey, hy] at hxy
  | inr x =>
      cases y with
      | inl y =>
          by_cases hx : x = i <;> simp [extendedOrderKey, hx] at hxy
      | inr y =>
          by_cases hx : x = i
          · subst x
            by_cases hy : y = i
            · subst y; rfl
            · simp [extendedOrderKey, hy] at hxy
          · by_cases hy : y = i
            · subst y
              simp [extendedOrderKey, hx] at hxy
            · simp only [extendedOrderKey, hx, hy, ↓reduceIte, toLex_inj,
                Sum.inr.injEq] at hxy
              exact congrArg Sum.inr hxy

/-- The `i`-th order extended from `X` to `X ⊕ I`. -/
@[instance_reducible]
noncomputable def extendedOrder (F : IndexedLinearOrders I X) (i : I) :
    LinearOrder (X ⊕ I) := by
  let _ : LinearOrder X := F i
  exact LinearOrder.lift' (extendedOrderKey (X := X) i) (extendedOrderKey_injective i)

/-- The whole extended family of orders. -/
noncomputable def extend (F : IndexedLinearOrders I X) : IndexedLinearOrders I (X ⊕ I) where
  order := F.extendedOrder

@[simp]
theorem extend_apply (F : IndexedLinearOrders I X) (i : I) :
    F.extend i = F.extendedOrder i := rfl

/-- The formal copy of `i` is minimal in the `i`-th extended order. -/
theorem inr_self_le (F : IndexedLinearOrders I X) (i : I) (x : X ⊕ I) :
    (F.extendedOrder i).le (Sum.inr i) x := by
  let _ : LinearOrder X := F i
  change extendedOrderKey (X := X) i (Sum.inr i) ≤ extendedOrderKey i x
  cases x with
  | inl x => simp [extendedOrderKey]
  | inr j =>
      by_cases hji : j = i
      · subst j
        simp [extendedOrderKey]
      · simp [extendedOrderKey, hji]

/-- Every old element lies below every formal `k ≠ i` in the `i`-th extended order. -/
theorem inl_le_inr_of_ne (F : IndexedLinearOrders I X) (i k : I) (x : X)
    (hki : k ≠ i) :
    (F.extendedOrder i).le (Sum.inl x) (Sum.inr k) := by
  let _ : LinearOrder X := F i
  change extendedOrderKey (X := X) i (Sum.inl x) ≤
    extendedOrderKey i (Sum.inr k)
  simp [extendedOrderKey, hki]

/-- The extended order restricts to the original `i`-th order on old elements. -/
theorem inl_le_inl_iff (F : IndexedLinearOrders I X) (i : I) (x y : X) :
    (F.extendedOrder i).le (Sum.inl x) (Sum.inl y) ↔ (F i).le x y := by
  let _ : LinearOrder X := F i
  change extendedOrderKey (X := X) i (Sum.inl x) ≤
      extendedOrderKey i (Sum.inl y) ↔ (F i).le x y
  simp [extendedOrderKey]

/-- No old element lies below the distinguished formal minimum. -/
theorem not_inl_le_inr_self (F : IndexedLinearOrders I X) (i : I) (x : X) :
    ¬ (F.extendedOrder i).le (Sum.inl x) (Sum.inr i) := by
  intro h
  have h' := (F.extendedOrder i).le_antisymm (Sum.inl x) (Sum.inr i) h
    (F.inr_self_le i (Sum.inl x))
  exact Sum.inl_ne_inr h'

/-- `τ ∪ (I\C)` inside the disjoint union. -/
def extendCell [Fintype I] [DecidableEq X]
    (τ : Finset X) (C : Finset I) : Finset (X ⊕ I) :=
  τ.image Sum.inl ∪ (Finset.univ \ C).image Sum.inr

omit [LinearOrder I] in
@[simp]
theorem inl_mem_extendCell_iff [Fintype I] [DecidableEq X]
    {τ : Finset X} {C : Finset I} {x : X} :
    Sum.inl x ∈ extendCell τ C ↔ x ∈ τ := by
  simp [extendCell]

omit [LinearOrder I] in
@[simp]
theorem inr_mem_extendCell_iff [Fintype I] [DecidableEq X]
    {τ : Finset X} {C : Finset I} {i : I} :
    Sum.inr i ∈ extendCell τ C ↔ i ∉ C := by
  simp [extendCell]

/-- Ivanov's Lemma 7.3. -/
theorem dominant_extendCell_iff [Fintype I] [Fintype X] [Nonempty X] [DecidableEq X]
    (F : IndexedLinearOrders I X) (τ : Finset X) (C : Finset I) :
    F.extend.IsDominant (extendCell τ C) Finset.univ ↔ F.IsDominant τ C := by
  change
    ((Finset.univ : Finset I).Nonempty ∧
        ∀ y : X ⊕ I, ∃ i ∈ (Finset.univ : Finset I),
          ∀ x ∈ extendCell τ C, (F.extendedOrder i).le y x) ↔
      C.Nonempty ∧ ∀ y : X, ∃ i ∈ C, ∀ x ∈ τ, (F i).le y x
  constructor
  · rintro ⟨_, hdom⟩
    have hold : ∀ y : X, ∃ i ∈ C, ∀ x ∈ τ, (F i).le y x := by
      intro y
      obtain ⟨i, _, hi⟩ := hdom (Sum.inl y)
      have hiC : i ∈ C := by
        by_contra hnot
        have hle := hi (Sum.inr i) (inr_mem_extendCell_iff.mpr hnot)
        exact F.not_inl_le_inr_self i y hle
      refine ⟨i, hiC, ?_⟩
      intro x hx
      have hle := hi (Sum.inl x) (inl_mem_extendCell_iff.mpr hx)
      exact (F.inl_le_inl_iff i y x).mp hle
    obtain ⟨y₀⟩ := (inferInstance : Nonempty X)
    have hC : C.Nonempty := by
      obtain ⟨i, hiC, _⟩ := hold y₀
      exact ⟨i, hiC⟩
    exact ⟨hC, hold⟩
  · rintro ⟨hC, hdom⟩
    have hI : (Finset.univ : Finset I).Nonempty := by
      obtain ⟨i, _⟩ := hC
      exact ⟨i, Finset.mem_univ i⟩
    refine ⟨hI, ?_⟩
    intro u
    cases u with
    | inl y =>
        obtain ⟨i, hiC, hi⟩ := hdom y
        refine ⟨i, Finset.mem_univ i, ?_⟩
        intro z hz
        cases z with
        | inl x =>
            have hx : x ∈ τ := inl_mem_extendCell_iff.mp hz
            have hle := (F.inl_le_inl_iff i y x).mpr (hi x hx)
            exact hle
        | inr j =>
            have hjC : j ∉ C := inr_mem_extendCell_iff.mp hz
            have hji : j ≠ i := by
              intro hji
              subst j
              exact hjC hiC
            have hle := F.inl_le_inr_of_ne i j y hji
            exact hle
    | inr j =>
        refine ⟨j, Finset.mem_univ j, ?_⟩
        intro z _
        exact F.inr_self_le j z

end ExtendedOrders

end IndexedLinearOrders

end BeyondSperner
