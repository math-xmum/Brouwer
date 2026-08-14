import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Minor.Restrict
import Mathlib.Data.Finite.Sum

/-!
# Finite principal single-element extensions

This file constructs, from a finite matroid `U` on the full type `α` and a set
`A`, the matroid obtained by adjoining a point freely in `closure A`.  The
construction is by the finite independence axioms.
-/

namespace BeyondSperner

open Set

namespace PrincipalExtension

variable {α : Type*}

/-- The old coordinates of a set on the canonical one-point carrier. -/
def oldPart (I : Set (α ⊕ Unit)) : Set α := Sum.inl ⁻¹' I

/-- The canonical new element. -/
def new (α : Type*) : α ⊕ Unit := Sum.inr ()

@[simp]
theorem mem_oldPart {I : Set (α ⊕ Unit)} {x : α} :
    x ∈ oldPart I ↔ Sum.inl x ∈ I := Iff.rfl

@[simp]
theorem oldPart_empty : oldPart (∅ : Set (α ⊕ Unit)) = ∅ := rfl

@[simp]
theorem oldPart_insert_inl (x : α) (I : Set (α ⊕ Unit)) :
    oldPart (insert (Sum.inl x) I) = insert x (oldPart I) := by
  ext
  simp [oldPart]

@[simp]
theorem oldPart_insert_new (I : Set (α ⊕ Unit)) :
    oldPart (insert (new α) I) = oldPart I := by
  ext
  simp [oldPart, new]

@[simp]
theorem inl_image_oldPart (I : Set (α ⊕ Unit)) :
    Sum.inl '' oldPart I = I \ {new α} := by
  ext z
  rcases z with x | u
  · simp [oldPart, new]
  · obtain rfl : u = () := Subsingleton.elim _ _
    simp [oldPart, new]

/-- A set containing the new point is its old part together with that point. -/
theorem image_oldPart_union_new_of_mem (I : Set (α ⊕ Unit)) (hp : new α ∈ I) :
    Sum.inl '' oldPart I ∪ {new α} = I := by
  classical
  rw [inl_image_oldPart]
  ext z
  by_cases hz : z = new α
  · subst z
    simp [hp]
  · simp [hz]

/-- A set not containing the new point consists only of its old coordinates. -/
theorem image_oldPart_eq_of_notMem (I : Set (α ⊕ Unit)) (hp : new α ∉ I) :
    Sum.inl '' oldPart I = I := by
  rw [inl_image_oldPart, Set.sdiff_singleton_eq_self hp]

/-- Cardinality of a set containing the new point. -/
theorem ncard_eq_oldPart_add_one [Finite α] (I : Set (α ⊕ Unit)) (hp : new α ∈ I) :
    I.ncard = (oldPart I).ncard + 1 := by
  classical
  have hdisj : Disjoint (Sum.inl '' oldPart I) {new α} := by
    rw [Set.disjoint_left]
    rintro z ⟨x, _, rfl⟩ hz
    simp [new] at hz
  calc
    I.ncard = (Sum.inl '' oldPart I ∪ {new α}).ncard :=
      congrArg Set.ncard (image_oldPart_union_new_of_mem I hp).symm
    _ = (Sum.inl '' oldPart I).ncard + ({new α} : Set (α ⊕ Unit)).ncard :=
      Set.ncard_union_eq hdisj
    _ = (oldPart I).ncard + 1 := by
      rw [Set.ncard_image_of_injective _ Sum.inl_injective]
      simp

/-- Cardinality of a set not containing the new point. -/
theorem ncard_eq_oldPart_of_notMem [Finite α] (I : Set (α ⊕ Unit)) (hp : new α ∉ I) :
    I.ncard = (oldPart I).ncard := by
  classical
  calc
    I.ncard = (Sum.inl '' oldPart I).ncard :=
      congrArg Set.ncard (image_oldPart_eq_of_notMem I hp).symm
    _ = (oldPart I).ncard := Set.ncard_image_of_injective _ Sum.inl_injective

/-- Independence in the principal extension. -/
def Indep (U : Matroid α) (A : Set α) (I : Set (α ⊕ Unit)) : Prop :=
  U.Indep (oldPart I) ∧
    (new α ∈ I → ¬ A ⊆ U.closure (oldPart I))

/-- An independent old set which minimally spans the principal set.  These are
exactly the old parts of circuits containing the new point. -/
def IsMinimalSpanning (U : Matroid α) (A B : Set α) : Prop :=
  U.Indep B ∧ A ⊆ U.closure B ∧
    ∀ b ∈ B, ¬ A ⊆ U.closure (B \ {b})

theorem Indep.subset {U : Matroid α} {A : Set α} {I J : Set (α ⊕ Unit)}
    (hJ : Indep U A J) (hIJ : I ⊆ J) : Indep U A I := by
  refine ⟨hJ.1.subset (fun x hx ↦ hIJ hx), ?_⟩
  intro hpI hA
  apply hJ.2 (hIJ hpI)
  exact hA.trans (U.closure_mono (fun x hx ↦ hIJ hx))

private theorem encard_lt_of_ncard_lt {β : Type*} {I J : Set β}
    (hI : I.Finite) (hJ : J.Finite) (h : I.ncard < J.ncard) :
    I.encard < J.encard := by
  rw [← hI.cast_ncard_eq, ← hJ.cast_ncard_eq]
  exact_mod_cast h

/-- Independent sets that do not span `A` satisfy the augmentation axiom.  This is
the matroid-theoretic core of the principal-extension construction. -/
private theorem exists_augment_not_spanning [Finite α] {U : Matroid α} {A I J : Set α}
    (hI : U.Indep I) (hJ : U.Indep J) (hcard : I.ncard < J.ncard)
    (hAI : ¬ A ⊆ U.closure I) (hAJ : ¬ A ⊆ U.closure J) :
    ∃ e ∈ J, e ∉ I ∧ U.Indep (insert e I) ∧ ¬ A ⊆ U.closure (insert e I) := by
  classical
  have hIfin : I.Finite := Set.toFinite I
  have hJfin : J.Finite := Set.toFinite J
  have hencard : I.encard < J.encard :=
    encard_lt_of_ncard_lt hIfin hJfin hcard
  obtain ⟨x, hxJI, hIx⟩ := hI.augment hJ hencard
  have hxJ : x ∈ J := hxJI.1
  have hxI : x ∉ I := hxJI.2
  by_contra! hbad
  have hspan_x : A ⊆ U.closure (insert x I) := hbad x hxJ hxI hIx
  obtain ⟨a, haA, haI⟩ := Set.not_subset.1 hAI
  have haGround : a ∈ U.E := U.closure_subset_ground _ (hspan_x haA)
  have hxGround : x ∈ U.E := hJ.subset_ground hxJ
  have hxClosureIA : x ∈ U.closure (I ∪ A) := by
    have haInsert : a ∈ U.closure (insert x I) \ U.closure I := ⟨hspan_x haA, haI⟩
    have hxInsert : x ∈ U.closure (insert a I) := (U.closure_exchange haInsert).1
    exact (U.closure_mono (insert_subset (Or.inr haA) subset_union_left)) hxInsert
  have hclosure_eq : U.closure (insert x I) = U.closure (I ∪ A) := by
    apply subset_antisymm
    · exact U.closure_subset_closure_of_subset_closure
        (insert_subset hxClosureIA (fun y hy ↦
          U.subset_closure _ (union_subset hI.subset_ground (fun z hz ↦
            U.closure_subset_ground _ (hspan_x hz))) (Or.inl hy)))
    · exact U.closure_subset_closure_of_subset_closure
        (union_subset
          (fun y hy ↦ U.subset_closure _ (insert_subset hxGround hI.subset_ground) (Or.inr hy))
          hspan_x)
  have hJclosure : J ⊆ U.closure (I ∪ A) := by
    intro y hyJ
    by_cases hyIcl : y ∈ U.closure I
    · exact (U.closure_mono subset_union_left) hyIcl
    · have hyI : y ∉ I := fun hyI ↦ hyIcl
          (U.subset_closure _ hI.subset_ground hyI)
      have hIy : U.Indep (insert y I) := by
        rw [hI.insert_indep_iff]
        exact Or.inl ⟨hJ.subset_ground hyJ, hyIcl⟩
      have hspan_y : A ⊆ U.closure (insert y I) := hbad y hyJ hyI hIy
      have haInsert : a ∈ U.closure (insert y I) \ U.closure I := ⟨hspan_y haA, haI⟩
      have hyInsert : y ∈ U.closure (insert a I) := (U.closure_exchange haInsert).1
      exact (U.closure_mono (insert_subset (Or.inr haA) subset_union_left)) hyInsert
  have hIxBasis : U.IsBasis (insert x I) (U.closure (I ∪ A)) := by
    rw [← hclosure_eq]
    exact hIx.isBasis_closure
  obtain ⟨B, hB, hJB⟩ := hJ.subset_isBasis_of_subset hJclosure
  have hBfin : B.Finite := Set.toFinite B
  have hIxfin : (insert x I).Finite := hIfin.insert x
  have hBcard : B.ncard = I.ncard + 1 := by
    have heq : B.encard = (insert x I).encard := hB.encard_eq_encard hIxBasis
    rw [← hBfin.cast_ncard_eq, ← hIxfin.cast_ncard_eq,
      Set.ncard_insert_of_notMem hxI hIfin] at heq
    exact ENat.natCast_inj.mp heq
  have hBJcard : B.ncard ≤ J.ncard := by omega
  have hJB_eq : J = B := Set.eq_of_subset_of_ncard_le hJB hBJcard hBfin
  apply hAJ
  have hAcl : A ⊆ U.closure (I ∪ A) := fun y hy ↦
    U.subset_closure _ (union_subset hI.subset_ground (fun z hz ↦
      U.closure_subset_ground _ (hspan_x hz))) (Or.inr hy)
  rw [hJB_eq]
  exact hAcl.trans hB.subset_closure

/-- If `I` spans `A` while an at-least-as-large independent set `J` does not,
then some element of `J` augments `I`. -/
private theorem exists_augment_spanning [Finite α] {U : Matroid α} {A I J : Set α}
    (hI : U.Indep I) (hJ : U.Indep J) (hcard : I.ncard ≤ J.ncard)
    (hAI : A ⊆ U.closure I) (hAJ : ¬ A ⊆ U.closure J) :
    ∃ e ∈ J, e ∉ I ∧ U.Indep (insert e I) := by
  classical
  have hIfin : I.Finite := Set.toFinite I
  have hJfin : J.Finite := Set.toFinite J
  have hJnot : ¬ J ⊆ U.closure I := by
    intro hJcl
    have hIBasis : U.IsBasis I (U.closure I) := hI.isBasis_closure
    obtain ⟨B, hB, hJB⟩ := hJ.subset_isBasis_of_subset hJcl
    have hBfin : B.Finite := Set.toFinite B
    have hBcard : B.ncard = I.ncard := by
      have heq : B.encard = I.encard := hB.encard_eq_encard hIBasis
      rw [← hBfin.cast_ncard_eq, ← hIfin.cast_ncard_eq] at heq
      exact ENat.natCast_inj.mp heq
    have hJB_eq : J = B := Set.eq_of_subset_of_ncard_le hJB (by omega) hBfin
    apply hAJ
    rw [hJB_eq]
    exact hAI.trans hB.subset_closure
  obtain ⟨e, heJ, heClosure⟩ := Set.not_subset.1 hJnot
  have heI : e ∉ I := fun heI ↦ heClosure (U.subset_closure _ hI.subset_ground heI)
  refine ⟨e, heJ, heI, ?_⟩
  rw [hI.insert_indep_iff]
  exact Or.inl ⟨hJ.subset_ground heJ, heClosure⟩

/-- The principal-extension independence predicate satisfies augmentation. -/
theorem Indep.augment [Finite α] {U : Matroid α} {A : Set α}
    (_hUE : U.E = Set.univ) (hA : U.Indep A)
    {I J : Set (α ⊕ Unit)} (hI : Indep U A I) (hJ : Indep U A J)
    (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ Indep U A (insert e I) := by
  classical
  let I₀ := oldPart I
  let J₀ := oldPart J
  have hI₀fin : I₀.Finite := Set.toFinite I₀
  have hJ₀fin : J₀.Finite := Set.toFinite J₀
  by_cases hpI : new α ∈ I
  · by_cases hpJ : new α ∈ J
    · have hcardOld : I₀.ncard < J₀.ncard := by
        dsimp only [I₀, J₀]
        rw [ncard_eq_oldPart_add_one I hpI,
          ncard_eq_oldPart_add_one J hpJ] at hcard
        omega
      obtain ⟨x, hxJ, hxI, hxIndep, hxNotSpan⟩ :=
        exists_augment_not_spanning hI.1 hJ.1 hcardOld (hI.2 hpI) (hJ.2 hpJ)
      refine ⟨Sum.inl x, hxJ, hxI, ?_⟩
      exact ⟨by simpa [I₀] using hxIndep, fun _ ↦ by simpa [I₀] using hxNotSpan⟩
    · have hcardOld : I₀.ncard + 1 < J₀.ncard := by
        dsimp only [I₀, J₀]
        rwa [ncard_eq_oldPart_add_one I hpI,
          ncard_eq_oldPart_of_notMem J hpJ] at hcard
      obtain ⟨a, haA, haClosure⟩ := Set.not_subset.1 (hI.2 hpI)
      have haGround : a ∈ U.E := hA.subset_ground haA
      have hIa : U.Indep (insert a I₀) := by
        rw [hI.1.insert_indep_iff]
        exact Or.inl ⟨haGround, haClosure⟩
      have haI₀ : a ∉ I₀ := fun haI ↦
        haClosure (U.subset_closure I₀ hI.1.subset_ground haI)
      have hcardIa : (insert a I₀).ncard < J₀.ncard := by
        rw [Set.ncard_insert_of_notMem haI₀ hI₀fin]
        exact hcardOld
      obtain ⟨x, ⟨hxJ, hxIa⟩, hxIndep⟩ :=
        hIa.augment hJ.1
          (encard_lt_of_ncard_lt (hI₀fin.insert a) hJ₀fin hcardIa)
      have hxI₀ : x ∉ I₀ := fun hx ↦ hxIa (Or.inr hx)
      have hxa : x ≠ a := fun h ↦ hxIa (h ▸ Or.inl rfl)
      have hIx : U.Indep (insert x I₀) := hxIndep.subset (by
        intro y hy
        rcases hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hy))
      refine ⟨Sum.inl x, hxJ, hxI₀, ?_⟩
      refine ⟨by simpa [I₀] using hIx, ?_⟩
      intro _ hspan
      apply haClosure
      have haNotClosure : a ∉ U.closure (insert x I₀) := by
        apply (hIx.notMem_closure_iff haGround).2
        refine ⟨?_, ?_⟩
        · simpa [Set.insert_comm] using hxIndep
        · simp [hxa.symm, haI₀]
      have hspan' : A ⊆ U.closure (insert x I₀) := by simpa [I₀] using hspan
      exact (haNotClosure (hspan' haA)).elim
  · by_cases hpJ : new α ∈ J
    · have hcardOld : I₀.ncard ≤ J₀.ncard := by
        dsimp only [I₀, J₀]
        rw [ncard_eq_oldPart_of_notMem I hpI,
          ncard_eq_oldPart_add_one J hpJ] at hcard
        omega
      by_cases hspan : A ⊆ U.closure I₀
      · obtain ⟨x, hxJ, hxI, hxIndep⟩ :=
          exists_augment_spanning hI.1 hJ.1 hcardOld hspan (hJ.2 hpJ)
        refine ⟨Sum.inl x, hxJ, hxI,
          ⟨by simpa [I₀] using hxIndep, ?_⟩⟩
        intro hnew
        have : new α ∈ I := by simpa [new] using hnew
        exact (hpI this).elim
      · refine ⟨new α, hpJ, hpI, ?_⟩
        exact ⟨by simpa [I₀] using hI.1, fun _ ↦ by simpa [I₀] using hspan⟩
    · have hcardOld : I₀.ncard < J₀.ncard := by
        dsimp only [I₀, J₀]
        rwa [ncard_eq_oldPart_of_notMem I hpI,
          ncard_eq_oldPart_of_notMem J hpJ] at hcard
      obtain ⟨x, ⟨hxJ, hxI⟩, hxIndep⟩ :=
        hI.1.augment hJ.1
          (encard_lt_of_ncard_lt hI₀fin hJ₀fin hcardOld)
      refine ⟨Sum.inl x, hxJ, hxI,
        ⟨by simpa [I₀] using hxIndep, ?_⟩⟩
      intro hnew
      have : new α ∈ I := by simpa [new] using hnew
      exact (hpI this).elim

/-- The finite ordinary matroid obtained by adding a point freely in
`closure A`. -/
noncomputable def matroid [Finite α] (U : Matroid α) (A : Set α)
    (hUE : U.E = Set.univ) (hA : U.Indep A) : Matroid (α ⊕ Unit) :=
  (IndepMatroid.ofFinite (E := Set.univ) Set.finite_univ (Indep U A)
    (by simp [Indep, oldPart])
    (by
      intro I J hJ hIJ
      exact Indep.subset hJ hIJ)
    (by
      intro I J hI hJ hcard
      exact Indep.augment hUE hA hI hJ hcard)
    (by
      intro I hI
      exact Set.subset_univ I)).matroid

@[simp]
theorem matroid_ground [Finite α] (U : Matroid α) (A : Set α)
    (hUE : U.E = Set.univ) (hA : U.Indep A) :
    (matroid U A hUE hA).E = Set.univ := by
  unfold matroid
  rfl

@[simp]
theorem matroid_indep_iff [Finite α] (U : Matroid α) (A : Set α)
    (hUE : U.E = Set.univ) (hA : U.Indep A) {I : Set (α ⊕ Unit)} :
    (matroid U A hUE hA).Indep I ↔ Indep U A I := by
  unfold matroid
  rfl

/-- Independence on the old coordinates is unchanged by principal extension. -/
@[simp]
theorem matroid_indep_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {I : Set α} :
    (matroid U A hUE hA).Indep (Sum.inl '' I) ↔ U.Indep I := by
  rw [matroid_indep_iff]
  have hpre : oldPart (Sum.inl '' I) = I := by
    ext x
    simp [oldPart]
  simp [Indep, new, hpre]

/-- Adding the new point to an old independent set is independent exactly
when that old set does not yet span `A`. -/
@[simp]
theorem matroid_indep_insert_new_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {I : Set α} :
    (matroid U A hUE hA).Indep (insert (new α) (Sum.inl '' I)) ↔
      U.Indep I ∧ ¬ A ⊆ U.closure I := by
  rw [matroid_indep_iff]
  have hpre : oldPart (insert (new α) (Sum.inl '' I)) = I := by
    ext x
    simp [oldPart, new]
  simp only [Indep, Set.mem_insert_iff, true_or, true_implies]
  rw [hpre]

/-- The old circuits are exactly the circuits of the principal extension that
avoid the new point. -/
@[simp]
theorem matroid_isCircuit_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {C : Set α} :
    (matroid U A hUE hA).IsCircuit (Sum.inl '' C) ↔ U.IsCircuit C := by
  classical
  let U' := matroid U A hUE hA
  have hdep : U'.Dep (Sum.inl '' C) ↔ U.Dep C := by
    rw [Matroid.dep_iff, Matroid.dep_iff]
    rw [show U'.E = Set.univ by simp [U'], hUE]
    simp only [Set.subset_univ, and_true]
    exact not_congr (matroid_indep_image_inl_iff U A hUE hA)
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep,
    Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep, hdep]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h e heC
    have hdiff : ((Sum.inl : α → α ⊕ Unit) '' C) \ {Sum.inl e} =
        (Sum.inl : α → α ⊕ Unit) '' (C \ {e}) := by
      ext z
      rcases z with z | z
      · simp
      · simp
    have heImage : (Sum.inl e : α ⊕ Unit) ∈
        (Sum.inl : α → α ⊕ Unit) '' C := ⟨e, heC, rfl⟩
    have hind := h _ heImage
    rw [hdiff, matroid_indep_image_inl_iff U A hUE hA] at hind
    exact hind
  · intro h z hz
    obtain ⟨e, heC, rfl⟩ := hz
    have hdiff : ((Sum.inl : α → α ⊕ Unit) '' C) \ {Sum.inl e} =
        (Sum.inl : α → α ⊕ Unit) '' (C \ {e}) := by
      ext z
      rcases z with z | z
      · simp
      · simp
    rw [hdiff, matroid_indep_image_inl_iff U A hUE hA]
    exact h e heC

/-- Exact classification of circuits of the principal extension containing the
new point. -/
@[simp]
theorem matroid_isCircuit_insert_new_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {B : Set α} :
    (matroid U A hUE hA).IsCircuit
        (insert (new α) (Sum.inl '' B)) ↔
      IsMinimalSpanning U A B := by
  classical
  let U' := matroid U A hUE hA
  have hpImage (X : Set α) : new α ∉ (Sum.inl : α → α ⊕ Unit) '' X := by
    simp [new]
  have hremoveNew :
      insert (new α) ((Sum.inl : α → α ⊕ Unit) '' B) \ {new α} =
        Sum.inl '' B := by
    ext z
    rcases z with x | u
    · simp [new]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [new]
  have hremoveOld (b : α) :
      insert (new α) ((Sum.inl : α → α ⊕ Unit) '' B) \ {Sum.inl b} =
        insert (new α) (Sum.inl '' (B \ {b})) := by
    ext z
    rcases z with x | u
    · by_cases hxb : x = b
      · subst x
        simp [new]
      · simp [new, hxb]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [new]
  constructor
  · intro hC
    have hBindep : U.Indep B := by
      have h := hC.sdiff_singleton_indep (show new α ∈
        insert (new α) ((Sum.inl : α → α ⊕ Unit) '' B) by simp)
      rw [hremoveNew, matroid_indep_image_inl_iff U A hUE hA] at h
      exact h
    have hAspans : A ⊆ U.closure B := by
      by_contra hnot
      have hWholeIndep : U'.Indep
          (insert (new α) ((Sum.inl : α → α ⊕ Unit) '' B)) :=
        (matroid_indep_insert_new_image_inl_iff U A hUE hA).mpr
          ⟨hBindep, hnot⟩
      exact hC.not_indep hWholeIndep
    refine ⟨hBindep, hAspans, ?_⟩
    intro b hb hAspansRemove
    have hbC : Sum.inl b ∈
        insert (new α) ((Sum.inl : α → α ⊕ Unit) '' B) :=
      Or.inr ⟨b, hb, rfl⟩
    have hRemoveIndep := hC.sdiff_singleton_indep hbC
    rw [hremoveOld,
      matroid_indep_insert_new_image_inl_iff U A hUE hA] at hRemoveIndep
    exact hRemoveIndep.2 hAspansRemove
  · rintro ⟨hBindep, hAspans, hminimal⟩
    rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
    refine ⟨?_, ?_⟩
    · rw [Matroid.dep_iff]
      refine ⟨?_, by simp⟩
      rw [matroid_indep_insert_new_image_inl_iff U A hUE hA]
      exact fun h ↦ h.2 hAspans
    · intro z hz
      rcases hz with hz | hz
      · have hzNew : z = new α := hz
        subst z
        rw [hremoveNew, matroid_indep_image_inl_iff U A hUE hA]
        exact hBindep
      · obtain ⟨b, hb, rfl⟩ := hz
        rw [hremoveOld,
          matroid_indep_insert_new_image_inl_iff U A hUE hA]
        exact ⟨hBindep.sdiff _, hminimal b hb⟩

/-- Old bases remain bases, and every base of the extension supported entirely
on old coordinates comes from an old base.  In particular, the principal
extension preserves rank. -/
@[simp]
theorem matroid_isBase_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {B : Set α} :
    (matroid U A hUE hA).IsBase (Sum.inl '' B) ↔ U.IsBase B := by
  classical
  let U' := matroid U A hUE hA
  constructor
  · intro hBext
    have hBmax := (Matroid.isBase_iff_maximal_indep.mp hBext)
    rw [maximal_subset_iff] at hBmax
    apply Matroid.isBase_iff_maximal_indep.mpr
    rw [maximal_subset_iff]
    refine ⟨(matroid_indep_image_inl_iff U A hUE hA).mp hBmax.1, ?_⟩
    intro J hJ hBJ
    have hImageJ : U'.Indep (Sum.inl '' J) :=
      (matroid_indep_image_inl_iff U A hUE hA).mpr hJ
    have hImageEq : Sum.inl '' B = (Sum.inl : α → α ⊕ Unit) '' J :=
      hBmax.2 hImageJ (Set.image_mono hBJ)
    exact Sum.inl_injective.image_injective hImageEq
  · intro hB
    have hBmax := Matroid.isBase_iff_maximal_indep.mp hB
    rw [maximal_subset_iff] at hBmax
    apply Matroid.isBase_iff_maximal_indep.mpr
    rw [maximal_subset_iff]
    refine ⟨(matroid_indep_image_inl_iff U A hUE hA).mpr hBmax.1, ?_⟩
    intro J hJ hBJ
    have hJspec : Indep U A J := (matroid_indep_iff U A hUE hA).mp hJ
    have hB_old : B ⊆ oldPart J := by
      intro b hb
      exact hBJ ⟨b, hb, rfl⟩
    have hOldEq : B = oldPart J := hBmax.2 hJspec.1 hB_old
    have hpJ : new α ∉ J := by
      intro hp
      apply hJspec.2 hp
      rw [← hOldEq, hB.closure_eq, hUE]
      exact Set.subset_univ A
    calc
      Sum.inl '' B = Sum.inl '' oldPart J := congrArg _ hOldEq
      _ = J := image_oldPart_eq_of_notMem J hpJ

/-- Taking a basis inside an old-coordinate set is unchanged by principal
extension. -/
@[simp]
theorem matroid_isBasis_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {I X : Set α} :
    (matroid U A hUE hA).IsBasis (Sum.inl '' I) (Sum.inl '' X) ↔
      U.IsBasis I X := by
  classical
  let U' := matroid U A hUE hA
  constructor
  · intro hI
    rw [Matroid.isBasis_iff (by simp [hUE])]
    refine ⟨(matroid_indep_image_inl_iff U A hUE hA).mp hI.indep,
      fun x hx ↦ ?_, ?_⟩
    · have : Sum.inl x ∈ (Sum.inl : α → α ⊕ Unit) '' X :=
        hI.subset ⟨x, hx, rfl⟩
      simpa using this
    · intro J hJ hIJ hJX
      have hImageJ : U'.Indep (Sum.inl '' J) :=
        (matroid_indep_image_inl_iff U A hUE hA).mpr hJ
      have hEq := hI.eq_of_subset_indep hImageJ
        (Set.image_mono hIJ) (Set.image_mono hJX)
      exact Sum.inl_injective.image_injective hEq
  · intro hI
    rw [Matroid.isBasis_iff (by simp)]
    refine ⟨(matroid_indep_image_inl_iff U A hUE hA).mpr hI.indep,
      Set.image_mono hI.subset, ?_⟩
    intro J hJ hImageIJ hJImageX
    have hpJ : new α ∉ J := by
      intro hp
      have : new α ∈ (Sum.inl : α → α ⊕ Unit) '' X := hJImageX hp
      simp [new] at this
    have hJold : U.Indep (oldPart J) :=
      (matroid_indep_iff U A hUE hA).mp hJ |>.1
    have hIold : I ⊆ oldPart J := by
      intro x hx
      exact hImageIJ ⟨x, hx, rfl⟩
    have hOldX : oldPart J ⊆ X := by
      intro x hx
      have : Sum.inl x ∈ (Sum.inl : α → α ⊕ Unit) '' X := hJImageX hx
      simpa using this
    have hOldEq : I = oldPart J :=
      hI.eq_of_subset_indep hJold hIold hOldX
    calc
      Sum.inl '' I = Sum.inl '' oldPart J := congrArg _ hOldEq
      _ = J := image_oldPart_eq_of_notMem J hpJ

/-- The new point is spanned by an old set exactly when that old set spans the
principal set `A`. -/
theorem new_mem_matroid_closure_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    (X : Set α) :
    new α ∈ (matroid U A hUE hA).closure (Sum.inl '' X) ↔
      A ⊆ U.closure X := by
  classical
  let U' := matroid U A hUE hA
  obtain ⟨I, hIX⟩ := U.exists_isBasis X (by simp [hUE])
  have hIext : U'.IsBasis (Sum.inl '' I) (Sum.inl '' X) :=
    (matroid_isBasis_image_inl_iff U A hUE hA).mpr hIX
  have hIindep : U'.Indep (Sum.inl '' I) := hIext.indep
  have hpI : new α ∉ (Sum.inl : α → α ⊕ Unit) '' I := by
    simp [new]
  have hnot := hIindep.notMem_closure_iff_of_notMem hpI
  rw [matroid_indep_insert_new_image_inl_iff U A hUE hA] at hnot
  simp only [hIX.indep, true_and] at hnot
  have hmem : new α ∈ U'.closure (Sum.inl '' I) ↔ A ⊆ U.closure I := by
    simpa using not_congr hnot
  rw [← hIext.closure_eq_closure, ← hIX.closure_eq_closure]
  exact hmem

/-- Closure on old coordinates is unchanged by principal extension. -/
theorem inl_mem_matroid_closure_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    (X : Set α) (x : α) :
    Sum.inl x ∈ (matroid U A hUE hA).closure (Sum.inl '' X) ↔
      x ∈ U.closure X := by
  classical
  let U' := matroid U A hUE hA
  obtain ⟨I, hIX⟩ := U.exists_isBasis X (by simp [hUE])
  have hIext : U'.IsBasis (Sum.inl '' I) (Sum.inl '' X) :=
    (matroid_isBasis_image_inl_iff U A hUE hA).mpr hIX
  have hinsert : insert (Sum.inl x) (Sum.inl '' I) =
      (Sum.inl : α → α ⊕ Unit) '' insert x I := by
    rw [Set.image_insert_eq]
  have hIndepInsert : U'.Indep ((Sum.inl : α → α ⊕ Unit) '' insert x I) ↔
      U.Indep (insert x I) := by
    exact matroid_indep_image_inl_iff U A hUE hA
  have hmem : Sum.inl x ∈ U'.closure (Sum.inl '' I) ↔
      x ∈ U.closure I := by
    rw [hIext.indep.mem_closure_iff', hIX.indep.mem_closure_iff']
    simp only [show Sum.inl x ∈ U'.E by simp [U'], true_and,
      show x ∈ U.E by simp [hUE], hinsert,
      hIndepInsert, Set.mem_image,
      Sum.inl.injEq, exists_eq_right]
  rw [← hIext.closure_eq_closure, ← hIX.closure_eq_closure]
  exact hmem

/-- An old-coordinate set spans the principal extension exactly when it spans
the original matroid. -/
theorem matroid_spanning_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    (X : Set α) :
    (matroid U A hUE hA).Spanning (Sum.inl '' X) ↔ U.Spanning X := by
  classical
  let U' := matroid U A hUE hA
  rw [U'.spanning_iff_exists_isBase_subset (by simp [U']),
    U.spanning_iff_exists_isBase_subset (by simp [hUE])]
  constructor
  · rintro ⟨B, hB, hBX⟩
    have hpB : new α ∉ B := by
      intro hp
      have : new α ∈ (Sum.inl : α → α ⊕ Unit) '' X := hBX hp
      simp [new] at this
    have hshape : Sum.inl '' oldPart B = B :=
      image_oldPart_eq_of_notMem B hpB
    have hOldBase : U.IsBase (oldPart B) := by
      apply (matroid_isBase_image_inl_iff U A hUE hA).mp
      simpa [hshape] using hB
    refine ⟨oldPart B, hOldBase, ?_⟩
    intro x hx
    have : Sum.inl x ∈ (Sum.inl : α → α ⊕ Unit) '' X := by
      apply hBX
      rw [← hshape]
      exact ⟨x, hx, rfl⟩
    simpa using this
  · rintro ⟨B, hB, hBX⟩
    exact ⟨Sum.inl '' B,
      (matroid_isBase_image_inl_iff U A hUE hA).mpr hB,
      Set.image_mono hBX⟩

/-- An old cocircuit disjoint from the principal set remains a cocircuit after
principal extension, with zero new coordinate. -/
theorem matroid_isCocircuit_image_inl_of_disjoint [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {K : Set α} (hK : U.IsCocircuit K) (hKA : Disjoint K A) :
    (matroid U A hUE hA).IsCocircuit (Sum.inl '' K) := by
  classical
  let U' := matroid U A hUE hA
  rw [Matroid.isCocircuit_iff_minimal_compl_nonspanning,
    minimal_subset_iff]
  have hKmin := (Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hK)
  have hcompl : U'.E \ (Sum.inl : α → α ⊕ Unit) '' K =
      insert (new α) (Sum.inl '' (U.E \ K)) := by
    ext z
    rcases z with x | u
    · simp [U', hUE, new]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [U', new]
  have hAcompl : A ⊆ U.closure (U.E \ K) := by
    intro a haA
    apply U.subset_closure _ sdiff_subset
    exact ⟨by simp [hUE], fun haK ↦ Set.disjoint_left.1 hKA haK haA⟩
  have hpClosure : new α ∈ U'.closure (Sum.inl '' (U.E \ K)) :=
    (new_mem_matroid_closure_image_inl_iff U A hUE hA _).mpr hAcompl
  have hnotSpanning : ¬ U'.Spanning (U'.E \ (Sum.inl : α → α ⊕ Unit) '' K) := by
    rw [hcompl]
    intro hsp
    have hspOld : U'.Spanning (Sum.inl '' (U.E \ K)) := by
      refine ⟨?_, by simp [U']⟩
      rw [← U'.closure_insert_eq_of_mem_closure hpClosure]
      exact hsp.closure_eq
    exact hKmin.1
      ((matroid_spanning_image_inl_iff U A hUE hA _).mp hspOld)
  refine ⟨hnotSpanning, ?_⟩
  intro T hTnonspanning hTK
  let K₀ : Set α := oldPart T
  have hpT : new α ∉ T := by
    intro hp
    have : new α ∈ (Sum.inl : α → α ⊕ Unit) '' K := hTK hp
    simp [new] at this
  have hK₀K : K₀ ⊆ K := by
    intro x hx
    have hxImage : Sum.inl x ∈ (Sum.inl : α → α ⊕ Unit) '' K := hTK hx
    simpa using hxImage
  have hK₀nonspanning : ¬ U.Spanning (U.E \ K₀) := by
    intro hspOld
    have hspImage : U'.Spanning (Sum.inl '' (U.E \ K₀)) :=
      (matroid_spanning_image_inl_iff U A hUE hA _).mpr hspOld
    apply hTnonspanning
    apply hspImage.superset
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨by simp, hx.2⟩
  have hKK₀ : K = K₀ :=
    Set.Subset.antisymm (hKmin.2 hK₀nonspanning hK₀K) hK₀K
  calc
    Sum.inl '' K = Sum.inl '' K₀ := congrArg _ hKK₀
    _ = T := image_oldPart_eq_of_notMem T hpT

/-- Conversely, an ordinary cocircuit of the principal extension which avoids
the new point and whose old part misses the principal set was already an old
cocircuit.  Thus every genuinely new cocircuit avoiding the new point must
meet the principal set. -/
theorem oldPart_isCocircuit_of_isCocircuit_of_new_not_mem_of_disjoint
    [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {L : Set (α ⊕ Unit)}
    (hL : (matroid U A hUE hA).IsCocircuit L)
    (hpL : new α ∉ L) (hdisjoint : Disjoint (oldPart L) A) :
    U.IsCocircuit (oldPart L) := by
  classical
  let U' := matroid U A hUE hA
  let K : Set α := oldPart L
  have hshape : Sum.inl '' K = L := image_oldPart_eq_of_notMem L hpL
  have hLmin := Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hL
  rw [Matroid.isCocircuit_iff_minimal_compl_nonspanning,
    minimal_subset_iff]
  have hKnonspanning : ¬ U.Spanning (U.E \ K) := by
    intro hsp
    have hspImage : U'.Spanning (Sum.inl '' (U.E \ K)) :=
      (matroid_spanning_image_inl_iff U A hUE hA _).mpr hsp
    apply hLmin.1
    apply hspImage.superset
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨by simp, ?_⟩
      intro hxL
      have hxK : x ∈ K := by
        rw [← hshape] at hxL
        simpa using hxL
      exact hx.2 hxK
  refine ⟨hKnonspanning, ?_⟩
  intro T hTnonspanning hTK
  let S : Set (α ⊕ Unit) := Sum.inl '' T
  have hSL : S ⊆ L := by
    rw [← hshape]
    exact Set.image_mono hTK
  have hAH : A ⊆ U.closure (U.E \ T) := by
    intro a haA
    apply U.subset_closure _ sdiff_subset
    refine ⟨by simp [hUE], ?_⟩
    intro haT
    exact Set.disjoint_left.1 hdisjoint (hTK haT) haA
  have hpClosure : new α ∈ U'.closure (Sum.inl '' (U.E \ T)) :=
    (new_mem_matroid_closure_image_inl_iff U A hUE hA _).mpr hAH
  have hScompl : U'.E \ S =
      insert (new α) (Sum.inl '' (U.E \ T)) := by
    ext z
    rcases z with x | u
    · simp [S, U', hUE, new]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [S, U', new]
  have hSnonspanning : ¬ U'.Spanning (U'.E \ S) := by
    rw [hScompl]
    intro hsp
    have hspOldImage : U'.Spanning (Sum.inl '' (U.E \ T)) := by
      refine ⟨?_, by simp [U']⟩
      rw [← U'.closure_insert_eq_of_mem_closure hpClosure]
      exact hsp.closure_eq
    exact hTnonspanning
      ((matroid_spanning_image_inl_iff U A hUE hA _).mp hspOldImage)
  have hLS : L ⊆ S := hLmin.2 hSnonspanning hSL
  apply Set.Subset.antisymm
  · intro x hxK
    have hxL : Sum.inl x ∈ L := by
      rw [← hshape]
      exact ⟨x, hxK, rfl⟩
    have hxS := hLS hxL
    simpa [S] using hxS
  · exact hTK

/-- A cocircuit meeting the principal set acquires the new point as an
extended cocircuit support. -/
theorem matroid_isCocircuit_insert_new_image_inl_of_nonempty_inter [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {K : Set α} (hK : U.IsCocircuit K) (hKA : (K ∩ A).Nonempty) :
    (matroid U A hUE hA).IsCocircuit
      (insert (new α) (Sum.inl '' K)) := by
  classical
  let U' := matroid U A hUE hA
  let H : Set α := U.E \ K
  have hKmin := Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hK
  obtain ⟨a, haK, haA⟩ := hKA
  have haE : a ∈ U.E := hK.subset_ground haK
  have hHinsert : U.Spanning (insert a H) := by
    by_contra hnon
    have hsmall : K \ {a} ⊆ K := sdiff_subset
    have hlarge : K ⊆ K \ {a} := by
      apply hKmin.2
      · have heq : U.E \ (K \ {a}) = insert a H := by
          ext x
          by_cases hxa : x = a
          · subst x
            simp [H, haE, haK]
          · simp [H, hxa]
        simpa only [heq] using hnon
      · exact hsmall
    exact (hlarge haK).2 rfl
  have haClosure : a ∉ U.closure H := by
    intro ha
    apply hKmin.1
    refine ⟨?_, sdiff_subset⟩
    rw [← U.closure_insert_eq_of_mem_closure ha]
    exact hHinsert.closure_eq
  have hAnotClosure : ¬ A ⊆ U.closure H := by
    intro h
    exact haClosure (h haA)
  have hpNotClosure : new α ∉ U'.closure (Sum.inl '' H) := by
    exact fun hp ↦ hAnotClosure
      ((new_mem_matroid_closure_image_inl_iff U A hUE hA H).mp hp)
  have hInsertSpanning : U'.Spanning (insert (new α) (Sum.inl '' H)) := by
    obtain ⟨I, hIH⟩ := U.exists_isBasis H sdiff_subset
    have hAI : ¬ A ⊆ U.closure I := by
      rwa [hIH.closure_eq_closure]
    have hJindep : U'.Indep (insert (new α) (Sum.inl '' I)) :=
      (matroid_indep_insert_new_image_inl_iff U A hUE hA).mpr
        ⟨hIH.indep, hAI⟩
    have haClosureI : a ∉ U.closure I := by
      rwa [hIH.closure_eq_closure]
    have hIaIndep : U.Indep (insert a I) :=
      (hIH.indep.notMem_closure_iff haE).mp haClosureI |>.1
    have hIaSpanning : U.Spanning (insert a I) := by
      refine ⟨?_, insert_subset haE hIH.left_subset_ground⟩
      rw [U.closure_insert_congr_right hIH.closure_eq_closure]
      exact hHinsert.closure_eq
    have hIaBase : U.IsBase (insert a I) :=
      hIaIndep.isBase_of_spanning hIaSpanning
    have hOldBase : U'.IsBase (Sum.inl '' insert a I) :=
      (matroid_isBase_image_inl_iff U A hUE hA).mpr hIaBase
    obtain ⟨B', hB', hJB'⟩ := hJindep.exists_isBase_superset
    have haI : a ∉ I := fun haI ↦ haClosureI
      (U.subset_closure _ hIH.indep.subset_ground haI)
    have hpImageI : new α ∉ (Sum.inl : α → α ⊕ Unit) '' I := by
      simp [new]
    have hcardJ : (insert (new α) (Sum.inl '' I)).ncard =
        ((Sum.inl : α → α ⊕ Unit) '' insert a I).ncard := by
      rw [Set.ncard_insert_of_notMem hpImageI (Set.toFinite _),
        Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_insert_of_notMem haI (Set.toFinite _)]
    have hcardB' : B'.ncard = (Sum.inl '' insert a I).ncard :=
      hB'.ncard_eq_ncard_of_isBase hOldBase
    have hJB'eq : insert (new α) (Sum.inl '' I) = B' :=
      Set.eq_of_subset_of_ncard_le hJB' (by omega) (Set.toFinite _)
    have hJbase : U'.IsBase (insert (new α) (Sum.inl '' I)) := by
      rwa [hJB'eq]
    apply hJbase.spanning.superset
    intro z hz
    rcases hz with rfl | ⟨x, hxI, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨x, hIH.subset hxI, rfl⟩
  rw [Matroid.isCocircuit_iff_minimal_compl_nonspanning,
    minimal_subset_iff]
  have hcompl : U'.E \
      insert (new α) ((Sum.inl : α → α ⊕ Unit) '' K) =
      Sum.inl '' H := by
    ext z
    rcases z with x | u
    · simp [U', H, hUE, new]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [U', new]
  have hnonspanning : ¬ U'.Spanning
      (U'.E \ insert (new α) ((Sum.inl : α → α ⊕ Unit) '' K)) := by
    rw [hcompl]
    intro hsp
    exact hKmin.1 ((matroid_spanning_image_inl_iff U A hUE hA H).mp hsp)
  refine ⟨hnonspanning, ?_⟩
  intro T hTnonspanning hTsub
  let K₀ : Set α := oldPart T
  have hK₀K : K₀ ⊆ K := by
    intro x hx
    rcases hTsub hx with hnew | hxK
    · simp [new] at hnew
    · simpa using hxK
  have hK₀nonspanning : ¬ U.Spanning (U.E \ K₀) := by
    intro hspOld
    have hspImage : U'.Spanning (Sum.inl '' (U.E \ K₀)) :=
      (matroid_spanning_image_inl_iff U A hUE hA _).mpr hspOld
    apply hTnonspanning
    apply hspImage.superset
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨by simp, fun hxT ↦ hx.2 hxT⟩
  have hKK₀ : K = K₀ :=
    Set.Subset.antisymm (hKmin.2 hK₀nonspanning hK₀K) hK₀K
  have hpT : new α ∈ T := by
    by_contra hpT
    have hTshape : Sum.inl '' K₀ = T :=
      image_oldPart_eq_of_notMem T hpT
    apply hTnonspanning
    have : U'.E \ T = insert (new α) (Sum.inl '' H) := by
      rw [← hTshape, ← hKK₀]
      ext z
      rcases z with x | u
      · simp [U', H, hUE, new]
      · obtain rfl : u = () := Subsingleton.elim _ _
        simp [U', new]
    rw [this]
    exact hInsertSpanning
  calc
    insert (new α) (Sum.inl '' K) =
        Sum.inl '' oldPart T ∪ {new α} := by
          rw [hKK₀]
          change insert (new α) (Sum.inl '' K₀) =
            Sum.inl '' K₀ ∪ {new α}
          rw [Set.union_singleton]
    _ = T := image_oldPart_union_new_of_mem T hpT

/-- Every cocircuit support of the principal extension containing the new
point restricts to an old cocircuit that meets the principal set. -/
theorem isCocircuit_oldPart_and_nonempty_inter_of_new_mem [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {L : Set (α ⊕ Unit)}
    (hL : (matroid U A hUE hA).IsCocircuit L) (hpL : new α ∈ L) :
    U.IsCocircuit (oldPart L) ∧ ((oldPart L) ∩ A).Nonempty := by
  classical
  let U' := matroid U A hUE hA
  let K : Set α := oldPart L
  let H : Set α := U.E \ K
  have hshape : Sum.inl '' K ∪ {new α} = L :=
    image_oldPart_union_new_of_mem L hpL
  have hLmin := Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hL
  have hcompl : U'.E \ L = Sum.inl '' H := by
    rw [← hshape]
    ext z
    rcases z with x | u
    · simp [U', H, hUE, new]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [U', new]
  have hKnonspanning : ¬ U.Spanning (U.E \ K) := by
    intro hsp
    apply hLmin.1
    rw [hcompl]
    exact (matroid_spanning_image_inl_iff U A hUE hA H).mpr hsp
  have hKcocircuit : U.IsCocircuit K := by
    rw [Matroid.isCocircuit_iff_minimal_compl_nonspanning,
      minimal_subset_iff]
    refine ⟨hKnonspanning, ?_⟩
    intro T hTnonspanning hTK
    let S : Set (α ⊕ Unit) := insert (new α) (Sum.inl '' T)
    have hSL : S ⊆ L := by
      rw [← hshape, Set.union_singleton]
      exact Set.insert_subset_insert (Set.image_mono hTK)
    have hSnonspanning : ¬ U'.Spanning (U'.E \ S) := by
      have hScompl : U'.E \ S = Sum.inl '' (U.E \ T) := by
        ext z
        rcases z with x | u
        · simp [S, U', hUE, new]
        · obtain rfl : u = () := Subsingleton.elim _ _
          simp [S, U', new]
      rw [hScompl]
      exact fun hsp ↦ hTnonspanning
        ((matroid_spanning_image_inl_iff U A hUE hA _).mp hsp)
    have hLS : L ⊆ S := hLmin.2 hSnonspanning hSL
    apply Set.Subset.antisymm
    · intro x hxK
      have hxL : Sum.inl x ∈ L := by
        rw [← hshape]
        exact Or.inl ⟨x, hxK, rfl⟩
      rcases hLS hxL with hnew | hxT
      · simp [new] at hnew
      · simpa [S] using hxT
    · exact hTK
  have hKmeetA : (K ∩ A).Nonempty := by
    by_contra hnot
    have hKA : Disjoint K A := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hnot
    have hAclosure : A ⊆ U.closure H := by
      intro a haA
      apply U.subset_closure _ sdiff_subset
      exact ⟨by simp [hUE], fun haK ↦ Set.disjoint_left.1 hKA haK haA⟩
    have hpClosure : new α ∈ U'.closure (Sum.inl '' H) :=
      (new_mem_matroid_closure_image_inl_iff U A hUE hA H).mpr hAclosure
    have hImageSub : Sum.inl '' K ⊆ L := by
      rw [← hshape]
      exact subset_union_left
    have hRemoveSpanning : U'.Spanning (U'.E \ (Sum.inl '' K)) := by
      by_contra hnon
      have hLsub : L ⊆ Sum.inl '' K := hLmin.2 hnon hImageSub
      have : new α ∈ (Sum.inl : α → α ⊕ Unit) '' K := hLsub hpL
      simp [new] at this
    have hRemoveShape : U'.E \ (Sum.inl '' K) =
        insert (new α) (Sum.inl '' H) := by
      ext z
      rcases z with x | u
      · simp [U', H, hUE, new]
      · obtain rfl : u = () := Subsingleton.elim _ _
        simp [U', new]
    have hOldSpanning : U'.Spanning (Sum.inl '' H) := by
      refine ⟨?_, by simp [U']⟩
      rw [← U'.closure_insert_eq_of_mem_closure hpClosure]
      rw [← hRemoveShape]
      exact hRemoveSpanning.closure_eq
    exact hKnonspanning
      ((matroid_spanning_image_inl_iff U A hUE hA H).mp hOldSpanning)
  exact ⟨by simpa [K] using hKcocircuit, by simpa [K] using hKmeetA⟩

/-- Exact characterization of the principal-extension cocircuit supports that
contain the new point. -/
theorem matroid_isCocircuit_insert_new_image_inl_iff [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {K : Set α} :
    (matroid U A hUE hA).IsCocircuit
        (insert (new α) (Sum.inl '' K)) ↔
      U.IsCocircuit K ∧ (K ∩ A).Nonempty := by
  constructor
  · intro hKext
    have hp : new α ∈ insert (new α) (Sum.inl '' K) := Set.mem_insert _ _
    have h := isCocircuit_oldPart_and_nonempty_inter_of_new_mem
      U A hUE hA hKext hp
    have hpre : oldPart (insert (new α) (Sum.inl '' K)) = K := by
      ext x
      simp [oldPart, new]
    rwa [hpre] at h
  · rintro ⟨hK, hKA⟩
    exact matroid_isCocircuit_insert_new_image_inl_of_nonempty_inter
      U A hUE hA hK hKA

end PrincipalExtension
end BeyondSperner
