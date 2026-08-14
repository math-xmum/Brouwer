import BeyondSperner.OrientedMatroid.Elimination

/-!
# Todd's theorem

The theorem is stated exactly at the signed-circuit level used in Section 6 and Appendix A.1.
-/

namespace BeyondSperner

namespace OrientedMatroid

open Set

variable {α : Type*} (M : Data α)

/-- The four signed conclusions in Todd's circuit theorem. -/
def ToddConclusion (Z C D : SignedSubset α) (w : α) : Prop :=
  Z.positive ⊆ (C.positive ∪ D.positive) \ C.negative ∧
    Z.negative ⊆ (C.negative ∪ D.negative) \ C.positive ∧
      w ∈ Z.support ∧ Z.SameSignAt D w

/-- A Todd circuit uses no element outside the two input supports. -/
private theorem ToddConclusion.support_subset
    {Z C D : SignedSubset α} {w : α} (hZ : ToddConclusion Z C D w) :
    Z.support ⊆ C.support ∪ D.support := by
  intro x hx
  rcases hx with hx | hx
  · rcases (hZ.1 hx).1 with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
  · rcases (hZ.2.1 hx).1 with hx | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)

/-- On their common support, a Todd circuit has the same sign as the first input circuit. -/
private theorem ToddConclusion.sameSignAt_left
    {Z C D : SignedSubset α} {w x : α} (hZ : ToddConclusion Z C D w)
    (hxZ : x ∈ Z.support) (hxC : x ∈ C.support) :
    Z.SameSignAt C x := by
  rcases hxZ with hxZ | hxZ <;> rcases hxC with hxC | hxC
  · exact Or.inl ⟨hxZ, hxC⟩
  · exact ((hZ.1 hxZ).2 hxC).elim
  · exact ((hZ.2.1 hxZ).2 hxC).elim
  · exact Or.inr ⟨hxZ, hxC⟩

/-- Todd's theorem, existence part. -/
theorem todd
    [Finite α] {C D : SignedSubset α} (hC : M.IsCircuit C) (hD : M.IsCircuit D)
    {w : α} (hw : w ∈ D.support \ C.support)
    (hopposite : ∃ e ∈ C.support ∩ D.support, C.OppositeAt D e) :
    ∃ Z : SignedSubset α, M.IsCircuit Z ∧ ToddConclusion Z C D w := by
  classical
  let rec go (C D : SignedSubset α)
      (hC : M.IsCircuit C) (hD : M.IsCircuit D)
      {w : α} (hw : w ∈ D.support \ C.support)
      (hopposite : ∃ e ∈ C.support ∩ D.support, C.OppositeAt D e) :
      ∃ Z : SignedSubset α, M.IsCircuit Z ∧ ToddConclusion Z C D w := by
    obtain ⟨e, he, heopp⟩ := hopposite
    have hwSurvives : SurvivesFrom D C w := by
      rcases hw.1 with hwD | hwD
      · exact Or.inl ⟨hwD, fun hwC ↦ hw.2 (Or.inr hwC)⟩
      · exact Or.inr ⟨hwD, fun hwC ↦ hw.2 (Or.inl hwC)⟩
    obtain ⟨Ω, hΩ, hΩelim, hwΩ⟩ :=
      strongElimination M hD hC (SignedSubset.oppositeAt_comm.mp heopp) hwSurvives
    have hΩsameD : Ω.SameSignAt D w := by
      rcases hwΩ with hwΩ | hwΩ
      · rcases (hΩelim.1 hwΩ).1 with hwD | hwC
        · exact Or.inl ⟨hwΩ, hwD⟩
        · exact (hw.2 (Or.inl hwC)).elim
      · rcases (hΩelim.2 hwΩ).1 with hwD | hwC
        · exact Or.inr ⟨hwΩ, hwD⟩
        · exact (hw.2 (Or.inr hwC)).elim
    by_cases hCOppΩ : ∃ f ∈ C.support ∩ Ω.support, C.OppositeAt Ω f
    · have hSepSub : C.separation Ω ⊆ C.separation D := by
        intro x hx
        rcases hx with hx | hx
        · rcases (hΩelim.2 hx.2).1 with hxD | hxC
          · exact Or.inl ⟨hx.1, hxD⟩
          · exact (Set.disjoint_left.1 C.disjoint hx.1 hxC).elim
        · rcases (hΩelim.1 hx.2).1 with hxD | hxC
          · exact Or.inr ⟨hx.1, hxD⟩
          · exact (Set.disjoint_left.1 C.disjoint hxC hx.1).elim
      have heSepCD : e ∈ C.separation D := heopp
      have heNotSepCΩ : e ∉ C.separation Ω := by
        intro heSep
        rcases heSep with heSep | heSep
        · exact (hΩelim.2 heSep.2).2 (by simp)
        · exact (hΩelim.1 heSep.2).2 (by simp)
      have hlt : (C.separation Ω).ncard < (C.separation D).ncard :=
        Set.ncard_lt_ncard
          (hSepSub.ssubset_of_mem_notMem heSepCD heNotSepCΩ)
      have hwΩC : w ∈ Ω.support \ C.support := ⟨hwΩ, hw.2⟩
      obtain ⟨Z, hZ, hZcon⟩ := go C Ω hC hΩ hwΩC hCOppΩ
      refine ⟨Z, hZ, ?_⟩
      refine ⟨?_, ?_, hZcon.2.2.1, hZcon.2.2.2.trans hΩsameD⟩
      · intro x hx
        have hx' := hZcon.1 hx
        refine ⟨?_, hx'.2⟩
        rcases hx'.1 with hxC | hxΩ
        · exact Or.inl hxC
        · rcases (hΩelim.1 hxΩ).1 with hxD | hxC
          · exact Or.inr hxD
          · exact Or.inl hxC
      · intro x hx
        have hx' := hZcon.2.1 hx
        refine ⟨?_, hx'.2⟩
        rcases hx'.1 with hxC | hxΩ
        · exact Or.inl hxC
        · rcases (hΩelim.2 hxΩ).1 with hxD | hxC
          · exact Or.inr hxD
          · exact Or.inl hxC
    · refine ⟨Ω, hΩ, ?_⟩
      refine ⟨?_, ?_, hwΩ, hΩsameD⟩
      · intro x hx
        refine ⟨?_, ?_⟩
        · rcases (hΩelim.1 hx).1 with hxD | hxC
          · exact Or.inr hxD
          · exact Or.inl hxC
        · intro hxCneg
          exact hCOppΩ ⟨x, ⟨Or.inr hxCneg, Or.inl hx⟩,
            Or.inr ⟨hxCneg, hx⟩⟩
      · intro x hx
        refine ⟨?_, ?_⟩
        · rcases (hΩelim.2 hx).1 with hxD | hxC
          · exact Or.inr hxD
          · exact Or.inl hxC
        · intro hxCpos
          exact hCOppΩ ⟨x, ⟨Or.inl hxCpos, Or.inr hx⟩,
            Or.inl ⟨hxCpos, hx⟩⟩
  termination_by (C.separation D).ncard
  decreasing_by exact hlt
  exact go C D hC hD hw hopposite

/--
Todd's uniqueness clause: if `supp D ⊆ supp C ∪ {w}`, the Todd circuit is unique and contains
`supp C \ supp D`.
-/
theorem todd_unique
    [Finite α] {C D : SignedSubset α} (hC : M.IsCircuit C) (hD : M.IsCircuit D)
    {w : α} (hw : w ∈ D.support \ C.support)
    (hopposite : ∃ e ∈ C.support ∩ D.support, C.OppositeAt D e)
    (hsub : D.support ⊆ C.support ∪ {w}) :
    ∃ Z : SignedSubset α,
      M.IsCircuit Z ∧ ToddConclusion Z C D w ∧
        (∀ W : SignedSubset α,
          M.IsCircuit W → ToddConclusion W C D w → W = Z) ∧
        C.support \ D.support ⊆ Z.support := by
  obtain ⟨Z, hZ, hZcon⟩ := todd M hC hD hw hopposite
  have hDToC : D.support \ {w} ⊆ C.support := by
    intro x hx
    rcases hsub hx.1 with hxC | hxw
    · exact hxC
    · exact (hx.2 (by simpa using hxw)).elim
  have hToddToC : ∀ {T : SignedSubset α}, ToddConclusion T C D w →
      T.support \ {w} ⊆ C.support := by
    intro T hT x hx
    rcases hT.support_subset hx.1 with hxC | hxD
    · exact hxC
    · exact hDToC ⟨hxD, hx.2⟩
  have hDoppNegZ : D.OppositeAt (-Z) w := by
    rcases hZcon.2.2.2 with hsame | hsame
    · exact Or.inl ⟨hsame.2, by simpa using hsame.1⟩
    · exact Or.inr ⟨hsame.2, by simpa using hsame.1⟩
  have hDneZ : D ≠ Z := by
    intro hDZ
    obtain ⟨e, he, heopp⟩ := hopposite
    have heZ : e ∈ Z.support := by simpa [hDZ] using he.2
    have hZsameC := hZcon.sameSignAt_left heZ he.1
    have hZoppC : Z.OppositeAt C e := by
      rw [← SignedSubset.oppositeAt_comm]
      simpa [hDZ] using heopp
    exact hZsameC.not_oppositeAt hZoppC
  obtain ⟨R, hR, hRelim⟩ :=
    M.weakElimination hD (M.neg_isCircuit hZ) (by simpa using hDneZ) hDoppNegZ
  have hRsubC : R.support ⊆ C.support := by
    intro x hxR
    have hx := hRelim.support_subset hxR
    rcases hx.1 with hxD | hxNegZ
    · exact hDToC ⟨hxD, hx.2⟩
    · have hxZ : x ∈ Z.support := by simpa using hxNegZ
      exact hToddToC hZcon ⟨hxZ, hx.2⟩
  have hRC : R = C ∨ R = -C :=
    M.eq_or_eq_neg_of_support_subset hR hC hRsubC
  have hCdiffDsubZ : C.support \ D.support ⊆ Z.support := by
    intro x hx
    have hxR : x ∈ R.support := by
      rcases hRC with hRC | hRC
      · simpa [hRC] using hx.1
      · simpa [hRC] using hx.1
    rcases (hRelim.support_subset hxR).1 with hxD | hxNegZ
    · exact (hx.2 hxD).elim
    · simpa using hxNegZ
  refine ⟨Z, hZ, hZcon, ?_, hCdiffDsubZ⟩
  intro W hW hWcon
  by_contra hWZ
  have hZsameW : Z.SameSignAt W w :=
    hZcon.2.2.2.trans (SignedSubset.sameSignAt_comm.mp hWcon.2.2.2)
  have hZoppNegW : Z.OppositeAt (-W) w := by
    rcases hZsameW with hsame | hsame
    · exact Or.inl ⟨hsame.1, by simpa using hsame.2⟩
    · exact Or.inr ⟨hsame.1, by simpa using hsame.2⟩
  have hZneW : Z ≠ W := fun h ↦ hWZ h.symm
  obtain ⟨Q, hQ, hQelim⟩ :=
    M.weakElimination hZ (M.neg_isCircuit hW) (by simpa using hZneW) hZoppNegW
  have hQsubC : Q.support ⊆ C.support := by
    intro x hxQ
    have hx := hQelim.support_subset hxQ
    rcases hx.1 with hxZ | hxNegW
    · exact hToddToC hZcon ⟨hxZ, hx.2⟩
    · have hxW : x ∈ W.support := by simpa using hxNegW
      exact hToddToC hWcon ⟨hxW, hx.2⟩
  have hQC : Q = C ∨ Q = -C :=
    M.eq_or_eq_neg_of_support_subset hQ hC hQsubC
  have hZnotSubW : ¬ Z.support ⊆ W.support := by
    intro hsubZW
    rcases M.eq_or_eq_neg_of_support_subset hZ hW hsubZW with hEq | hNeg
    · exact hWZ hEq.symm
    · have hWNegZ : W = -Z := by
        have h := congrArg Neg.neg hNeg
        simpa using h.symm
      have hOpp : Z.OppositeAt W w := by
        rw [hWNegZ]
        exact SignedSubset.oppositeAt_neg_self hZcon.2.2.1
      exact hZsameW.not_oppositeAt hOpp
  have hWnotSubZ : ¬ W.support ⊆ Z.support := by
    intro hsubWZ
    rcases M.eq_or_eq_neg_of_support_subset hW hZ hsubWZ with hEq | hNeg
    · exact hWZ hEq
    · have hWOppZ : W.OppositeAt Z w := by
        rw [hNeg]
        exact SignedSubset.oppositeAt_comm.mp
          (SignedSubset.oppositeAt_neg_self hZcon.2.2.1)
      exact (SignedSubset.sameSignAt_comm.mp hZsameW).not_oppositeAt hWOppZ
  obtain ⟨x, hxZ, hxW⟩ := Set.not_subset.1 hZnotSubW
  obtain ⟨y, hyW, hyZ⟩ := Set.not_subset.1 hWnotSubZ
  have hxne : x ≠ w := by
    intro hxw
    exact hxW (hxw ▸ hWcon.2.2.1)
  have hyne : y ≠ w := by
    intro hyw
    exact hyZ (hyw ▸ hZcon.2.2.1)
  have hxC : x ∈ C.support := hToddToC hZcon ⟨hxZ, by simpa using hxne⟩
  have hyC : y ∈ C.support := hToddToC hWcon ⟨hyW, by simpa using hyne⟩
  have hQsupport : Q.support = C.support := by
    rcases hQC with hQC | hQC
    · simp [hQC]
    · simp [hQC]
  have hxQ : x ∈ Q.support := hQsupport.symm ▸ hxC
  have hyQ : y ∈ Q.support := hQsupport.symm ▸ hyC
  have hQsameZ : Q.SameSignAt Z x := by
    rcases hxQ with hxQ | hxQ
    · rcases (hQelim.1 hxQ).1 with hxZ' | hxNegW
      · exact Or.inl ⟨hxQ, hxZ'⟩
      · exact (hxW (Or.inr (by simpa using hxNegW))).elim
    · rcases (hQelim.2 hxQ).1 with hxZ' | hxNegW
      · exact Or.inr ⟨hxQ, hxZ'⟩
      · exact (hxW (Or.inl (by simpa using hxNegW))).elim
  have hQsameC : Q.SameSignAt C x :=
    hQsameZ.trans (hZcon.sameSignAt_left hxZ hxC)
  have hQeqC : Q = C := by
    rcases hQC with hQC | hQC
    · exact hQC
    · exfalso
      have hQoppC : Q.OppositeAt C x := by
        rw [hQC]
        exact SignedSubset.oppositeAt_comm.mp
          (SignedSubset.oppositeAt_neg_self hxC)
      exact hQsameC.not_oppositeAt hQoppC
  have hQoppC : Q.OppositeAt C y := by
    have hWsameC := hWcon.sameSignAt_left hyW hyC
    rcases hyQ with hyQ | hyQ
    · rcases (hQelim.1 hyQ).1 with hyZ' | hyNegW
      · exact (hyZ (Or.inl hyZ')).elim
      · have hyWneg : y ∈ W.negative := by simpa using hyNegW
        rcases hWsameC with hsame | hsame
        · exact (Set.disjoint_left.1 W.disjoint hsame.1 hyWneg).elim
        · exact Or.inl ⟨hyQ, hsame.2⟩
    · rcases (hQelim.2 hyQ).1 with hyZ' | hyNegW
      · exact (hyZ (Or.inr hyZ')).elim
      · have hyWpos : y ∈ W.positive := by simpa using hyNegW
        rcases hWsameC with hsame | hsame
        · exact Or.inr ⟨hyQ, hsame.2⟩
        · exact (Set.disjoint_left.1 W.disjoint hyWpos hsame.1).elim
  rw [hQeqC] at hQoppC
  exact SignedSubset.not_oppositeAt_self C y hQoppC

end OrientedMatroid

end BeyondSperner
