import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
# Finite matroids from circuit axioms

This module supplies the finite circuit cryptomorphism that is not yet exposed by the pinned
mathlib version.  The augmentation argument is adapted from Andrew Nelson's experimental
`Matroid/Axioms/Circuit.lean` (Apache-2.0), with names and imports adjusted to this project.
-/

namespace BeyondSperner

open Set

variable {α : Type*} {I J C : Set α}

/-- A finite circuit system on a ground set, using the ordinary circuit elimination axiom. -/
structure FiniteCircuitSystem (α : Type*) where
  ground : Set α
  IsCircuit : Set α → Prop
  empty_not_isCircuit : ¬ IsCircuit ∅
  circuit_antichain : IsAntichain (· ⊆ ·) {C | IsCircuit C}
  circuit_elimination : ∀ ⦃C₁ C₂ e⦄,
    IsCircuit C₁ → IsCircuit C₂ → C₁ ≠ C₂ → e ∈ C₁ → e ∈ C₂ →
      ∃ C, IsCircuit C ∧ e ∉ C ∧ C ⊆ C₁ ∪ C₂
  circuit_finite : ∀ ⦃C⦄, IsCircuit C → C.Finite
  circuit_subset_ground : ∀ ⦃C⦄, IsCircuit C → C ⊆ ground

namespace FiniteCircuitSystem

variable {S : FiniteCircuitSystem α}

/-- Circuit-free subsets of the ground set. -/
protected structure Indep (S : FiniteCircuitSystem α) (I : Set α) : Prop where
  subset_ground : I ⊆ S.ground
  not_isCircuit_of_subset : ∀ ⦃C⦄, C ⊆ I → ¬ S.IsCircuit C

theorem indep_iff (S : FiniteCircuitSystem α) (I : Set α) :
    S.Indep I ↔ I ⊆ S.ground ∧ ∀ ⦃C⦄, C ⊆ I → ¬ S.IsCircuit C := by
  constructor
  · intro h
    exact ⟨h.subset_ground, h.not_isCircuit_of_subset⟩
  · rintro ⟨hground, hcircuit⟩
    exact ⟨hground, hcircuit⟩

protected theorem Indep.subset (hJ : S.Indep J) (hIJ : I ⊆ J) : S.Indep I :=
  ⟨hIJ.trans hJ.subset_ground,
    fun _ hCI hC ↦ hJ.not_isCircuit_of_subset (hCI.trans hIJ) hC⟩

/-- Finite cardinal augmentation, derived from ordinary circuit elimination. -/
protected theorem Indep.augment {J : Set α} (hI : S.Indep I) (hIfin : I.Finite)
    (hJ : S.Indep J) (hJfin : J.Finite) (hIJ : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ S.Indep (insert e I) := by
  by_cases hss : I ⊆ J
  · obtain ⟨e, he⟩ := exists_of_ssubset <| hss.ssubset_of_ne <| by
      rintro rfl
      simp at hIJ
    exact ⟨e, he.1, he.2, hJ.subset <| insert_subset he.1 hss⟩
  obtain ⟨x, hxI, hxJ⟩ := not_subset.1 hss
  by_contra! hcon
  have h_ex : ∀ y ∈ J \ I,
      ∃ C, S.IsCircuit C ∧ x ∈ C ∧ y ∉ C ∧ C \ {x} ⊆ J := by
    intro y hy
    by_cases hJ' : S.Indep (insert x (J \ {y}))
    · have hlt : ((insert x (J \ {y})) \ I).ncard < (J \ I).ncard := by
        rw [insert_sdiff_of_mem _ hxI, sdiff_sdiff_comm]
        exact ncard_sdiff_singleton_lt_of_mem hy hJfin.sdiff
      have hcard : I.ncard < (insert x (J \ {y})).ncard :=
        hIJ.trans_eq <| (ncard_exchange hxJ hy.1).symm
      obtain ⟨e, rfl | heJ, heI, hi⟩ :=
        Indep.augment hI hIfin hJ' (hJfin.sdiff.insert _) hcard
      · exact (heI hxI).elim
      exact False.elim <| hcon e heJ.1 heI hi
    obtain ⟨C, hCss, hC⟩ : ∃ C ⊆ insert x (J \ {y}), S.IsCircuit C := by
      simpa [indep_iff, insert_subset (hI.subset_ground hxI)
        (sdiff_subset.trans hJ.subset_ground)] using hJ'
    rw [subset_insert_iff,
      or_iff_right (fun h ↦ (hJ.subset sdiff_subset).not_isCircuit_of_subset h hC)] at hCss
    refine ⟨C, hC, hCss.1, fun hyC ↦ (hCss.2 ⟨hyC, ?_⟩).2 rfl,
      hCss.2.trans sdiff_subset⟩
    rintro rfl
    exact hy.2 hxI
  obtain ⟨a, haJ, haI⟩ : ∃ a ∈ J, a ∉ I :=
    not_subset.1 <| fun h ↦ hIJ.not_ge (ncard_le_ncard h hIfin)
  obtain ⟨Ca, hCa, hxCa, haCa, hCaJ⟩ := h_ex a ⟨haJ, haI⟩
  obtain ⟨b, hbCa, hbI⟩ : ∃ b ∈ Ca, b ∉ I :=
    not_subset.1 fun h ↦ hI.not_isCircuit_of_subset h hCa
  obtain ⟨Cb, hCb, hxCb, hbCb, hCbJ⟩ :=
    h_ex b ⟨hCaJ (mem_sdiff_singleton.2 ⟨hbCa, fun hbx ↦ hbI <| hbx ▸ hxI⟩), hbI⟩
  obtain ⟨C, hC, hxC, hC'⟩ :=
    S.circuit_elimination hCa hCb (by rintro rfl; contradiction) hxCa hxCb
  refine hJ.not_isCircuit_of_subset ?_ hC
  rw [← sdiff_singleton_eq_self hxC]
  refine (sdiff_subset_sdiff_left hC').trans ?_
  rw [union_sdiff_distrib]
  exact union_subset hCaJ hCbJ
termination_by (J \ I).ncard

/-- The mathlib matroid canonically constructed from a finite circuit system. -/
noncomputable def matroid (S : FiniteCircuitSystem α) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.ofFinitaryCardAugment
    (E := S.ground)
    (Indep := S.Indep)
    (⟨by simp, fun C hC hss ↦
      S.empty_not_isCircuit (by rwa [← subset_empty_iff.1 hC])⟩)
    (fun _ _ ↦ Indep.subset)
    (fun _ _ ↦ Indep.augment)
    (fun I h ↦
      ⟨fun e heI ↦ by simpa using (h {e} (by simpa) (by simp)).subset_ground,
        fun C hCI hC ↦
          (h C hCI (S.circuit_finite hC)).not_isCircuit_of_subset rfl.subset hC⟩)
    (fun _ ↦ Indep.subset_ground)

@[simp]
theorem matroid_ground (S : FiniteCircuitSystem α) : S.matroid.E = S.ground := rfl

@[simp]
theorem matroid_indep_iff (S : FiniteCircuitSystem α) :
    S.matroid.Indep I ↔
      I ⊆ S.ground ∧ ∀ ⦃C⦄, C ⊆ I → ¬ S.IsCircuit C := by
  simp [matroid, indep_iff]

/-- The constructed matroid has exactly the specified circuits. -/
theorem matroid_isCircuit (S : FiniteCircuitSystem α) :
    S.matroid.IsCircuit = S.IsCircuit := by
  ext C
  by_cases hCE : C ⊆ S.ground
  · simp only [Matroid.isCircuit_iff_forall_ssubset, S.matroid_indep_iff, hCE,
      true_and, ← Matroid.not_indep_iff
        (show C ⊆ S.matroid.E by simpa using hCE),
      not_forall, not_not, exists_prop]
    refine ⟨fun ⟨⟨C', hC', hC'ss⟩, hmin⟩ ↦ ?_,
      fun h ↦ ⟨⟨C, rfl.subset, h⟩, fun I hIC ↦ ?_⟩⟩
    · obtain rfl | hssu := hC'.eq_or_ssubset
      · exact hC'ss
      exact False.elim <| (hmin hssu).2 rfl.subset hC'ss
    refine ⟨hIC.subset.trans hCE, fun C' hC'I hC' ↦ ?_⟩
    exact S.circuit_antichain hC' h (hC'I.trans_ssubset hIC).ne
      (hC'I.trans hIC.subset)
  · exact iff_of_false
      (mt Matroid.IsCircuit.subset_ground (by simpa using hCE))
      (fun hC ↦ hCE (S.circuit_subset_ground hC))

end FiniteCircuitSystem

end BeyondSperner
