import BeyondSperner.OrientedMatroid.Farkas

/-!
# Cocircuit elimination

The finite four-painting argument supplies strong elimination for the
support-minimal covectors of a signed-circuit oriented matroid.  This is the
nontrivial ingredient needed to construct the oriented dual without assuming
cocircuit elimination in advance.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid
namespace Data

variable {α : Type*} (M : Data α)

/-- Strong cocircuit elimination when the surviving coordinate is positive in
the first cocircuit. -/
private theorem exists_isCocircuit_strongElimination_positive
    [Fintype α] {D E : SignedSubset α}
    (hD : M.IsCocircuit D) (hE : M.IsCocircuit E)
    {u v : α} (hu : D.OppositeAt E u)
    (hv : v ∈ D.positive \ E.negative) :
    ∃ Z : SignedSubset α,
      M.IsCocircuit Z ∧ EliminatesAt Z D E u ∧ v ∈ Z.support := by
  classical
  let S : Set α := D.separation E
  let B : Set α := insert u ((D.support ∪ E.support)ᶜ)
  let W : Set α := S \ {u}
  let R : Set α := (D.positive ∪ E.positive) \ S
  let G : Set α := (D.negative ∪ E.negative) \ S
  have huS : u ∈ S := hu
  have hRG : Disjoint R G := by
    rw [Set.disjoint_left]
    rintro x ⟨hxPos, hxNotS⟩ ⟨hxNeg, _⟩
    rcases hxPos with hxDpos | hxEpos <;>
      rcases hxNeg with hxDneg | hxEneg
    · exact Set.disjoint_left.1 D.disjoint hxDpos hxDneg
    · exact hxNotS (Or.inl ⟨hxDpos, hxEneg⟩)
    · exact hxNotS (Or.inr ⟨hxDneg, hxEpos⟩)
    · exact Set.disjoint_left.1 E.disjoint hxEpos hxEneg
  have hRB : Disjoint R B := by
    rw [Set.disjoint_left]
    rintro x hxR (hxu | hxOutside)
    · subst x
      exact hxR.2 huS
    · exact hxOutside (by
        rcases hxR.1 with hxD | hxE
        · exact Or.inl (Or.inl hxD)
        · exact Or.inr (Or.inl hxE))
  have hRW : Disjoint R W := by
    rw [Set.disjoint_left]
    exact fun _ hxR hxW ↦ hxR.2 hxW.1
  have hBW : Disjoint B W := by
    rw [Set.disjoint_left]
    rintro x (hxu | hxOutside) hxW
    · exact hxW.2 (by simp [hxu])
    · exact hxOutside (by
        rcases hxW.1 with hx | hx
        · exact Or.inl (Or.inl hx.1)
        · exact Or.inl (Or.inr hx.1))
  have hcover : M.underlying.E ⊆ R ∪ G ∪ B ∪ W := by
    intro x _
    by_cases hxB : x ∈ B
    · exact Or.inl (Or.inr hxB)
    have hxu : x ≠ u := fun h ↦ hxB (Or.inl h)
    have hxSupport : x ∈ D.support ∪ E.support := by
      by_contra hx
      exact hxB (Or.inr hx)
    by_cases hxS : x ∈ S
    · exact Or.inr ⟨hxS, by simpa using hxu⟩
    · rcases hxSupport with (hxDpos | hxDneg) | (hxEpos | hxEneg)
      · exact Or.inl (Or.inl (Or.inl ⟨Or.inl hxDpos, hxS⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨Or.inl hxDneg, hxS⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨Or.inr hxEpos, hxS⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨Or.inr hxEneg, hxS⟩))
  have hvS : v ∉ S := by
    rintro (h | h)
    · exact hv.2 h.2
    · exact Set.disjoint_left.1 D.disjoint hv.1 h.1
  have hvR : v ∈ R := ⟨Or.inl hv.1, hvS⟩
  have hvGround : v ∈ M.underlying.E :=
    (M.isCocircuit_support hD).subset_ground (Or.inl hv.1)
  let P := M.orthogonalPair
  rcases P.fourPainting hvGround hvR hRG hRB hRW hBW hcover with
      hCircuit | hCocircuit
  · rcases hCircuit with
      ⟨C, hC, hCpos, hCneg, hCW, hvCpos⟩
    have oppositeD_eq_u {x : α} (hx : C.OppositeAt D x) : x = u := by
      rcases hx with hx | hx
      · rcases hCpos hx.1 with hxR | hxB
        · rcases hxR.1 with hxDpos | hxEpos
          · exact (Set.disjoint_left.1 D.disjoint hxDpos hx.2).elim
          · exact (hxR.2 (Or.inr ⟨hx.2, hxEpos⟩)).elim
        · rcases hxB with hxu | hxOutside
          · exact hxu
          · exact (hxOutside (Or.inl (Or.inr hx.2))).elim
      · rcases hCneg hx.1 with hxG | hxB
        · rcases hxG.1 with hxDneg | hxEneg
          · exact (Set.disjoint_left.1 D.disjoint hx.2 hxDneg).elim
          · exact (hxG.2 (Or.inl ⟨hx.2, hxEneg⟩)).elim
        · rcases hxB with hxu | hxOutside
          · exact hxu
          · exact (hxOutside (Or.inl (Or.inl hx.2))).elim
    have oppositeE_eq_u {x : α} (hx : C.OppositeAt E x) : x = u := by
      rcases hx with hx | hx
      · rcases hCpos hx.1 with hxR | hxB
        · rcases hxR.1 with hxDpos | hxEpos
          · exact (hxR.2 (Or.inl ⟨hxDpos, hx.2⟩)).elim
          · exact (Set.disjoint_left.1 E.disjoint hxEpos hx.2).elim
        · rcases hxB with hxu | hxOutside
          · exact hxu
          · exact (hxOutside (Or.inr (Or.inr hx.2))).elim
      · rcases hCneg hx.1 with hxG | hxB
        · rcases hxG.1 with hxDneg | hxEneg
          · exact (hxG.2 (Or.inr ⟨hxDneg, hx.2⟩)).elim
          · exact (Set.disjoint_left.1 E.disjoint hx.2 hxEneg).elim
        · rcases hxB with hxu | hxOutside
          · exact hxu
          · exact (hxOutside (Or.inr (Or.inl hx.2))).elim
    have hCDopp : C.OppositeAt D u := by
      rcases (M.orthogonalPair.orthogonal hC hD) with
        hdisjoint | ⟨_, _, x, _, _, hxopp⟩
      · exact (Set.disjoint_left.1 hdisjoint (Or.inl hvCpos)
          (Or.inl hv.1)).elim
      · simpa [oppositeD_eq_u hxopp] using hxopp
    have hCEsame : C.SameSignAt E u :=
      hCDopp.sameSignAt_of_oppositeAt
        (SignedSubset.oppositeAt_comm.mp hu)
    rcases (M.orthogonalPair.orthogonal hC hE) with
      hdisjoint | ⟨_, _, x, _, _, hxopp⟩
    · rcases hCEsame with h | h
      · exact (Set.disjoint_left.1 hdisjoint (Or.inl h.1) (Or.inl h.2)).elim
      · exact (Set.disjoint_left.1 hdisjoint (Or.inr h.1) (Or.inr h.2)).elim
    · have hxu : x = u := oppositeE_eq_u hxopp
      subst x
      exact (hCEsame.not_oppositeAt hxopp).elim
  · rcases hCocircuit with
      ⟨Z, hZ, hZpos, hZneg, hZB, hvZpos⟩
    have hZnotU : u ∉ Z.support := fun huZ ↦
      Set.disjoint_left.1 hZB huZ (Or.inl rfl)
    refine ⟨Z, hZ, ?_, Or.inl hvZpos⟩
    constructor
    · intro x hxZ
      refine ⟨?_, fun hxu ↦ hZnotU (hxu ▸ Or.inl hxZ)⟩
      rcases hZpos hxZ with hxR | hxW
      · exact hxR.1
      · rcases hxW.1 with hx | hx
        · exact Or.inl hx.1
        · exact Or.inr hx.2
    · intro x hxZ
      refine ⟨?_, fun hxu ↦ hZnotU (hxu ▸ Or.inr hxZ)⟩
      rcases hZneg hxZ with hxG | hxW
      · exact hxG.1
      · rcases hxW.1 with hx | hx
        · exact Or.inr hx.2
        · exact Or.inl hx.1

/-- The signed cocircuits satisfy strong elimination. -/
theorem exists_isCocircuit_strongElimination
    [Fintype α] {D E : SignedSubset α}
    (hD : M.IsCocircuit D) (hE : M.IsCocircuit E)
    {u v : α} (hu : D.OppositeAt E u) (hv : SurvivesFrom D E v) :
    ∃ Z : SignedSubset α,
      M.IsCocircuit Z ∧ EliminatesAt Z D E u ∧ v ∈ Z.support := by
  rcases hv with hv | hv
  · exact M.exists_isCocircuit_strongElimination_positive hD hE hu hv
  · obtain ⟨Z, hZ, hElim, hvZ⟩ :=
      M.exists_isCocircuit_strongElimination_positive
        (M.neg_isCocircuit hD) (M.neg_isCocircuit hE)
        (by
          rcases hu with hu | hu
          · exact Or.inr hu
          · exact Or.inl hu)
        (by simpa using hv)
    refine ⟨-Z, M.neg_isCocircuit hZ, ?_, by simpa using hvZ⟩
    constructor
    · simpa using hElim.2
    · simpa using hElim.1

/-- The signed cocircuits satisfy weak elimination. -/
theorem exists_isCocircuit_weakElimination
    [Fintype α] {D E : SignedSubset α}
    (hD : M.IsCocircuit D) (hE : M.IsCocircuit E) (hne : D ≠ -E)
    {u : α} (hu : D.OppositeAt E u) :
    ∃ Z : SignedSubset α, M.IsCocircuit Z ∧ EliminatesAt Z D E u := by
  have hsurvivor : ∃ v, SurvivesFrom D E v := by
    by_contra hnone
    push Not at hnone
    have hsub : D.support ⊆ E.support := by
      intro x hxD
      rcases hxD with hxD | hxD
      · have hxE : x ∈ E.negative := by
          by_contra hxE
          exact hnone x (Or.inl ⟨hxD, hxE⟩)
        exact Or.inr hxE
      · have hxE : x ∈ E.positive := by
          by_contra hxE
          exact hnone x (Or.inr ⟨hxD, hxE⟩)
        exact Or.inl hxE
    have hsub' : E.support ⊆ D.support :=
      hE.2.2 hD.1 hD.2.1 hsub
    have hsupport : D.support = E.support := Set.Subset.antisymm hsub hsub'
    rcases M.eq_or_eq_neg_of_isCocircuit_support_eq hD hE hsupport with h | h
    · subst E
      exact SignedSubset.not_oppositeAt_self D u hu
    · exact hne h
  obtain ⟨v, hv⟩ := hsurvivor
  obtain ⟨Z, hZ, hElim, _⟩ :=
    M.exists_isCocircuit_strongElimination hD hE hu hv
  exact ⟨Z, hZ, hElim⟩

/-- The oriented dual: its signed circuits are exactly the support-minimal
covectors of `M`. -/
noncomputable def dual [Fintype α] : Data α where
  circuits := {D | M.IsCocircuit D}
  support_nonempty := fun hD ↦ hD.1
  neg_mem := fun hD ↦ M.neg_isCocircuit hD
  eq_or_eq_neg_of_support_subset := by
    intro D E hD hE hsub
    have hsub' : E.support ⊆ D.support :=
      hE.2.2 hD.1 hD.2.1 hsub
    exact M.eq_or_eq_neg_of_isCocircuit_support_eq hD hE
      (Set.Subset.antisymm hsub hsub')
  weakElimination := by
    intro D E hD hE hne u hu
    exact M.exists_isCocircuit_weakElimination hD hE hne hu

/-- The underlying ordinary matroid of the oriented dual is the ordinary
matroid dual. -/
theorem dual_underlying [Fintype α] :
    M.dual.underlying = M.underlying✶ := by
  apply Matroid.ext_isCircuit
  · rw [M.dual.underlying_spec.1, Matroid.dual_ground,
      M.underlying_spec.1]
  · intro K _
    rw [M.dual.underlying_spec.2]
    constructor
    · rintro ⟨D, hD, rfl⟩
      exact M.isCocircuit_support hD
    · intro hK
      obtain ⟨D, hD, hDsupport⟩ :=
        M.exists_isCocircuit_support_eq (show M.underlying.IsCocircuit K from hK)
      exact ⟨D, hD, hDsupport⟩

/-- Every signed circuit of `M` is a signed cocircuit of its oriented dual. -/
theorem isCircuit_isCocircuit_dual [Fintype α]
    {C : SignedSubset α} (hC : M.IsCircuit C) :
    M.dual.IsCocircuit C := by
  have hCunder : M.underlying.IsCircuit C.support :=
    (M.underlying_spec.2 C.support).mpr ⟨C, hC, rfl⟩
  refine ⟨M.circuit_support_nonempty hC, ?_, ?_⟩
  · intro D hD
    exact SignedSubset.orthogonal_comm.mpr (hD.2.1 hC)
  · intro E hEnonempty hEcovector hEC
    obtain ⟨e, heE⟩ := hEnonempty
    obtain ⟨K, hKdual, _, hKE⟩ :=
      hEcovector.exists_underlying_isCocircuit_subset_support M.dual heE
    have hK : M.underlying.IsCircuit K := by
      rw [M.dual_underlying] at hKdual
      simpa using hKdual
    have hKC : K ⊆ C.support := hKE.trans hEC
    have hEq : K = C.support := hK.eq_of_subset_isCircuit hCunder hKC
    simpa [← hEq] using hKE

/-- The signed cocircuits of the oriented dual are exactly the signed circuits
of the original oriented matroid. -/
theorem isCocircuit_dual_iff_isCircuit [Fintype α]
    {C : SignedSubset α} : M.dual.IsCocircuit C ↔ M.IsCircuit C := by
  constructor
  · intro hC
    have hSupport : M.underlying.IsCircuit C.support := by
      have h := M.dual.isCocircuit_support hC
      rw [M.dual_underlying] at h
      simpa using h
    obtain ⟨D, hD, hDsupport⟩ :=
      (M.underlying_spec.2 C.support).mp hSupport
    have hDdual : M.dual.IsCocircuit D :=
      M.isCircuit_isCocircuit_dual hD
    rcases M.dual.eq_or_eq_neg_of_isCocircuit_support_eq hC hDdual
        hDsupport.symm with h | h
    · simpa [h] using hD
    · simpa [h] using M.neg_isCircuit hD
  · exact M.isCircuit_isCocircuit_dual

/-- Oriented duality is involutive. -/
@[simp]
theorem dual_dual [Fintype α] : M.dual.dual = M := by
  apply Data.ext_circuits
  ext C
  exact M.isCocircuit_dual_iff_isCircuit

end Data
end OrientedMatroid
end BeyondSperner
