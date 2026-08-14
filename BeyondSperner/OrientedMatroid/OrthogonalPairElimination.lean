import BeyondSperner.OrientedMatroid.Farkas

/-!
# Elimination from an orthogonal signing

For a finite ordinary matroid, exact signed orientations of all circuits and
cocircuits that are closed under negation and mutually orthogonal already force
strong elimination.  No elimination axiom is assumed in `OrthogonalPair`.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid
namespace OrthogonalPair

variable {α : Type*} {U : Matroid α} (P : OrthogonalPair U)

/-- Strong elimination on the cocircuit side when the survivor is positive in
the first input. -/
private theorem strongElimination_cocircuits_positive
    [Fintype α] {D E : SignedSubset α}
    (hD : D ∈ P.cocircuits) (hE : E ∈ P.cocircuits)
    {u v : α} (hu : D.OppositeAt E u)
    (hv : v ∈ D.positive \ E.negative) :
    ∃ Z : SignedSubset α,
      Z ∈ P.cocircuits ∧ EliminatesAt Z D E u ∧ v ∈ Z.support := by
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
  have hcover : U.E ⊆ R ∪ G ∪ B ∪ W := by
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
  have hvGround : v ∈ U.E :=
    (P.cocircuit_support hD).subset_ground (Or.inl hv.1)
  rcases P.fourPainting hvGround hvR hRG hRB hRW hBW hcover with
      hCircuit | hCocircuit
  · rcases hCircuit with
      ⟨C, hC, hCpos, hCneg, _, hvCpos⟩
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
      rcases P.orthogonal hC hD with
        hdisjoint | ⟨_, _, x, _, _, hxopp⟩
      · exact (Set.disjoint_left.1 hdisjoint (Or.inl hvCpos)
          (Or.inl hv.1)).elim
      · simpa [oppositeD_eq_u hxopp] using hxopp
    have hCEsame : C.SameSignAt E u :=
      hCDopp.sameSignAt_of_oppositeAt
        (SignedSubset.oppositeAt_comm.mp hu)
    rcases P.orthogonal hC hE with
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

/-- Strong elimination for the cocircuit signing of an orthogonal pair. -/
theorem strongElimination_cocircuits
    [Fintype α] {D E : SignedSubset α}
    (hD : D ∈ P.cocircuits) (hE : E ∈ P.cocircuits)
    {u v : α} (hu : D.OppositeAt E u) (hv : SurvivesFrom D E v) :
    ∃ Z : SignedSubset α,
      Z ∈ P.cocircuits ∧ EliminatesAt Z D E u ∧ v ∈ Z.support := by
  rcases hv with hv | hv
  · exact P.strongElimination_cocircuits_positive hD hE hu hv
  · obtain ⟨Z, hZ, hElim, hvZ⟩ :=
      P.strongElimination_cocircuits_positive
        (P.neg_cocircuit hD) (P.neg_cocircuit hE)
        (by
          rcases hu with hu | hu
          · exact Or.inr hu
          · exact Or.inl hu)
        (by simpa using hv)
    refine ⟨-Z, P.neg_cocircuit hZ, ?_, by simpa using hvZ⟩
    exact ⟨by simpa using hElim.2, by simpa using hElim.1⟩

/-- Strong elimination for the circuit signing of an orthogonal pair. -/
theorem strongElimination_circuits
    [Fintype α] {C D : SignedSubset α}
    (hC : C ∈ P.circuits) (hD : D ∈ P.circuits)
    {u v : α} (hu : C.OppositeAt D u) (hv : SurvivesFrom C D v) :
    ∃ Z : SignedSubset α,
      Z ∈ P.circuits ∧ EliminatesAt Z C D u ∧ v ∈ Z.support := by
  exact P.swap.strongElimination_cocircuits hC hD hu hv

/-- On a fixed ordinary circuit support, agreement at one coordinate forces
equality of the two circuit signatures. -/
theorem eq_of_circuits_of_support_eq_of_sameSignAt
    [Fintype α] {C D : SignedSubset α}
    (hC : C ∈ P.circuits) (hD : D ∈ P.circuits)
    (hsupport : C.support = D.support) {e : α}
    (_heC : e ∈ C.support) (hsame : C.SameSignAt D e) : C = D := by
  by_contra hne
  have hopposite : ∃ x ∈ C.support, C.OppositeAt D x := by
    by_contra hnone
    push Not at hnone
    apply hne
    apply SignedSubset.eq_of_support_eq_of_forall_sameSignAt hsupport
    intro x hxC
    rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem
        ⟨hxC, hsupport ▸ hxC⟩ with hsame' | hopp
    · exact hsame'
    · exact (hnone x hxC hopp).elim
  obtain ⟨x, hxC, hxopp⟩ := hopposite
  have hesurvives : SurvivesFrom C D e := by
    rcases hsame with hsame | hsame
    · exact Or.inl ⟨hsame.1, fun heDneg ↦
        Set.disjoint_left.1 D.disjoint hsame.2 heDneg⟩
    · exact Or.inr ⟨hsame.1, fun heDpos ↦
        Set.disjoint_left.1 D.disjoint heDpos hsame.2⟩
  obtain ⟨Z, hZ, hElim, _⟩ :=
    P.strongElimination_circuits hC hD hxopp hesurvives
  have hZsubDiff : Z.support ⊆ C.support \ {x} := by
    have h := hElim.support_subset
    rw [← hsupport, Set.union_self] at h
    exact h
  have hZsub : Z.support ⊆ C.support :=
    hZsubDiff.trans Set.sdiff_subset
  have hZsupport : Z.support = C.support :=
    (P.circuit_support hZ).eq_of_subset_isCircuit
      (P.circuit_support hC) hZsub
  have hxZ : x ∈ Z.support := hZsupport.symm ▸ hxC
  exact (hZsubDiff hxZ).2 rfl

/-- Circuit signatures on nested supports agree up to global sign. -/
theorem eq_or_eq_neg_of_circuit_support_subset
    [Fintype α] {C D : SignedSubset α}
    (hC : C ∈ P.circuits) (hD : D ∈ P.circuits)
    (hsub : C.support ⊆ D.support) : C = D ∨ C = -D := by
  have hsupport : C.support = D.support :=
    (P.circuit_support hC).eq_of_subset_isCircuit
      (P.circuit_support hD) hsub
  obtain ⟨e, heC⟩ := (P.circuit_support hC).nonempty
  have heD : e ∈ D.support := hsupport ▸ heC
  rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem
      ⟨heC, heD⟩ with hsame | hopp
  · exact Or.inl
      (P.eq_of_circuits_of_support_eq_of_sameSignAt
        hC hD hsupport heC hsame)
  · right
    apply P.eq_of_circuits_of_support_eq_of_sameSignAt
      hC (P.neg_circuit hD) (by simpa using hsupport) heC
    simpa using hopp

/-- Weak circuit elimination follows from strong elimination and ordinary
circuit-support minimality. -/
theorem weakElimination_circuits
    [Fintype α] {C D : SignedSubset α}
    (hC : C ∈ P.circuits) (hD : D ∈ P.circuits) (hne : C ≠ -D)
    {u : α} (hu : C.OppositeAt D u) :
    ∃ Z : SignedSubset α, Z ∈ P.circuits ∧ EliminatesAt Z C D u := by
  have hsurvivor : ∃ v, SurvivesFrom C D v := by
    by_contra hnone
    push Not at hnone
    have hsub : C.support ⊆ D.support := by
      intro x hxC
      rcases hxC with hxC | hxC
      · have hxD : x ∈ D.negative := by
          by_contra hxD
          exact hnone x (Or.inl ⟨hxC, hxD⟩)
        exact Or.inr hxD
      · have hxD : x ∈ D.positive := by
          by_contra hxD
          exact hnone x (Or.inr ⟨hxC, hxD⟩)
        exact Or.inl hxD
    have hsupport : C.support = D.support :=
      (P.circuit_support hC).eq_of_subset_isCircuit
        (P.circuit_support hD) hsub
    apply hne
    apply SignedSubset.eq_of_support_eq_of_forall_sameSignAt
      (by simpa using hsupport)
    intro x hxC
    rcases hxC with hxC | hxC
    · have hxD : x ∈ D.negative := by
        by_contra hxD
        exact hnone x (Or.inl ⟨hxC, hxD⟩)
      exact Or.inl ⟨hxC, by simpa using hxD⟩
    · have hxD : x ∈ D.positive := by
        by_contra hxD
        exact hnone x (Or.inr ⟨hxC, hxD⟩)
      exact Or.inr ⟨hxC, by simpa using hxD⟩
  obtain ⟨v, hv⟩ := hsurvivor
  obtain ⟨Z, hZ, hElim, _⟩ :=
    P.strongElimination_circuits hC hD hu hv
  exact ⟨Z, hZ, hElim⟩

/-- An exact orthogonal signing of the circuits and cocircuits of a finite
ordinary matroid canonically defines an oriented matroid. -/
noncomputable def toData [Fintype α] : Data α where
  circuits := P.circuits
  support_nonempty := fun hC ↦ (P.circuit_support hC).nonempty
  neg_mem := fun hC ↦ P.neg_circuit hC
  eq_or_eq_neg_of_support_subset := by
    intro C D hC hD hsub
    exact P.eq_or_eq_neg_of_circuit_support_subset hC hD hsub
  weakElimination := by
    intro C D hC hD hne u hu
    exact P.weakElimination_circuits hC hD hne hu

@[simp]
theorem toData_circuits [Fintype α] : P.toData.circuits = P.circuits := rfl

end OrthogonalPair
end OrientedMatroid
end BeyondSperner
