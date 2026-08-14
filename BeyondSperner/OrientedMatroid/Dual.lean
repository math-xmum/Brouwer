import BeyondSperner.OrientedMatroid.Basic

/-!
# Signed cocircuits and oriented-matroid duality

This file develops the duality layer needed for the construction of lexicographic
single-element extensions.  The first step relates the support-minimal covector
definition of a signed cocircuit to ordinary cocircuits of the underlying matroid.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid
namespace Data

variable {α : Type*} (M : Data α)

/-- Every nonzero coordinate of a covector lies in an ordinary cocircuit whose
support is contained in that covector's support.  This is the unsigned
"coscrawl" property, derived here from circuit--covector orthogonality. -/
theorem IsCovector.exists_underlying_isCocircuit_subset_support
    [Fintype α] {D : SignedSubset α} (hD : M.IsCovector D)
    {e : α} (heD : e ∈ D.support) :
    ∃ K : Set α, M.underlying.IsCocircuit K ∧ e ∈ K ∧ K ⊆ D.support := by
  let U : Matroid α := M.underlying
  let N : Matroid α := U✶
  have heGroundU : e ∈ U.E := by
    rw [M.underlying_spec.1]
    trivial
  have heGroundN : e ∈ N.E := by simpa [N, U] using heGroundU
  have heNotDiff : e ∉ D.support \ {e} := by simp
  by_cases heClosure : e ∈ N.closure (D.support \ {e})
  · obtain ⟨K, hKsub, hKcircuit, heK⟩ :=
      (N.mem_closure_iff_exists_isCircuit heNotDiff).mp heClosure
    refine ⟨K, ?_, heK, ?_⟩
    · simpa [N, U] using hKcircuit
    · have hInsert : insert e (D.support \ {e}) = D.support := by
        rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem heD]
      simpa [hInsert] using hKsub
  · obtain ⟨I, hI⟩ := N.exists_isBasis' (D.support \ {e})
    have heNotClosureI : e ∉ N.closure I := by
      rwa [hI.closure_eq_closure]
    have hInsertIndep : N.Indep (insert e I) := by
      rw [hI.indep.insert_indep_iff]
      exact Or.inl ⟨heGroundN, heNotClosureI⟩
    obtain ⟨B, hBbase, hInsertB⟩ := hInsertIndep.exists_isBase_superset
    let C : Set α := N.E \ N.closure (B \ {e})
    have hCcocircuitN : N.IsCocircuit C := by
      simpa [C] using hBbase.compl_closure_sdiff_singleton_isCocircuit
        (hInsertB (by simp))
    have hCcircuitU : U.IsCircuit C := by
      simpa [N, U] using hCcocircuitN
    have heC : e ∈ C := by
      refine ⟨heGroundN, ?_⟩
      exact hBbase.indep.notMem_closure_sdiff_of_mem (hInsertB (by simp))
    have hDiffClosure : D.support \ {e} ⊆ N.closure (B \ {e}) := by
      intro x hx
      have hxClosureI : x ∈ N.closure I := by
        rw [hI.closure_eq_closure]
        exact N.subset_closure (D.support \ {e}) (by
          intro y _
          simp [N, U, M.underlying_spec.1]) hx
      apply N.closure_mono ?_ hxClosureI
      intro y hyI
      exact ⟨hInsertB (by exact Or.inr hyI), by
        intro hye
        subst y
        exact heNotClosureI
          (N.subset_closure I hI.indep.subset_ground hyI)⟩
    have hinter : C ∩ D.support = {e} := by
      apply Set.Subset.antisymm
      · intro x hx
        by_cases hxe : x = e
        · simp [hxe]
        · have hxDiff : x ∈ D.support \ {e} := ⟨hx.2, by simpa using hxe⟩
          exact (hx.1.2 (hDiffClosure hxDiff)).elim
      · exact Set.singleton_subset_iff.mpr ⟨heC, heD⟩
    obtain ⟨Csign, hCsign, hCsignSupport⟩ :=
      (M.underlying_spec.2 C).mp hCcircuitU
    have hsignInter : Csign.support ∩ D.support = {e} := by
      rwa [hCsignSupport]
    exact (SignedSubset.not_orthogonal_of_support_inter_eq_singleton hsignInter
      (hD hCsign)).elim

/-- Every ordinary cocircuit is a fundamental cocircuit for a suitable basis and any
prescribed element of its support. -/
theorem underlying_exists_isBase_fundCocircuit_eq
    [Finite α] {K : Set α} (hK : M.underlying.IsCocircuit K)
    {e : α} (heK : e ∈ K) :
    ∃ B : Set α, M.underlying.IsBase B ∧ e ∈ B ∧
      M.underlying.fundCocircuit e B = K := by
  let U : Matroid α := M.underlying
  have hKdual : U✶.IsCircuit K := hK
  have hI : U✶.Indep (K \ {e}) := hKdual.sdiff_singleton_indep heK
  obtain ⟨Bdual, hBdual, hKBdual⟩ := hI.exists_isBase_superset
  have heBdual : e ∉ Bdual := by
    intro he
    have hKsub : K ⊆ Bdual := by
      intro x hx
      by_cases hxe : x = e
      · simpa [hxe] using he
      · exact hKBdual ⟨hx, by simpa using hxe⟩
    exact hKdual.not_indep (hBdual.indep.subset hKsub)
  let B : Set α := U.E \ Bdual
  have hB : U.IsBase B := by
    simpa [B] using hBdual.compl_isBase_of_dual
  have heGround : e ∈ U.E := hKdual.subset_ground heK
  have heB : e ∈ B := ⟨heGround, heBdual⟩
  have hKsub : K ⊆ insert e Bdual := by
    intro x hx
    by_cases hxe : x = e
    · exact Or.inl hxe
    · exact Or.inr (hKBdual ⟨hx, by simpa using hxe⟩)
  have hfundDual : K = U✶.fundCircuit e Bdual :=
    hKdual.eq_fundCircuit_of_subset hBdual.indep hKsub
  refine ⟨B, hB, heB, ?_⟩
  rw [Matroid.fundCocircuit]
  have hBdualGround : Bdual ⊆ U.E := by
    simpa using hBdual.subset_ground
  have hdiff : U✶.E \ B = Bdual := by
    rw [Matroid.dual_ground]
    ext x
    simp only [B, Set.mem_sdiff]
    constructor
    · rintro ⟨hxE, hxnot⟩
      by_contra hxBdual
      exact hxnot ⟨hxE, hxBdual⟩
    · intro hx
      exact ⟨hBdualGround hx, fun h ↦ h.2 hx⟩
  rw [hdiff, ← hfundDual]

/-- Every ordinary cocircuit support admits a signed cocircuit orientation. -/
theorem exists_isCocircuit_support_eq
    [Fintype α] {K : Set α} (hK : M.underlying.IsCocircuit K) :
    ∃ D : SignedSubset α, M.IsCocircuit D ∧ D.support = K := by
  obtain ⟨e, heK⟩ := hK.nonempty
  obtain ⟨B, hBbase, heB, hfund⟩ :=
    M.underlying_exists_isBase_fundCocircuit_eq hK heK
  have hB : M.IsBasis B := M.isBasis_iff_underlying_isBase.mpr hBbase
  let D : SignedSubset α := M.fundamentalCocircuit B hB e
  refine ⟨D, M.fundamentalCocircuit_isCocircuit hB heB, ?_⟩
  rw [M.fundamentalCocircuit_support hB heB, hfund]

/-- A covector whose support is already an ordinary cocircuit is a signed
cocircuit.  This lets later constructions prove signed cocircuit status by
separating orthogonality from the unsigned support calculation. -/
theorem isCocircuit_of_isCovector_of_underlying_isCocircuit_support
    [Fintype α] {D : SignedSubset α} (hD : M.IsCovector D)
    (hSupport : M.underlying.IsCocircuit D.support) :
    M.IsCocircuit D := by
  refine ⟨hSupport.nonempty, hD, ?_⟩
  intro E hEnonempty hEcovector hED
  obtain ⟨e, heE⟩ := hEnonempty
  obtain ⟨K, hK, _heK, hKE⟩ :=
    hEcovector.exists_underlying_isCocircuit_subset_support M heE
  have hKD : K ⊆ D.support := hKE.trans hED
  have hEq : K = D.support := hK.eq_of_subset_isCircuit hSupport hKD
  exact hEq ▸ hKE

/-- The support of every signed cocircuit is an ordinary cocircuit of the
underlying matroid. -/
theorem isCocircuit_support
    [Fintype α] {D : SignedSubset α} (hD : M.IsCocircuit D) :
    M.underlying.IsCocircuit D.support := by
  rw [Matroid.isCocircuit_iff_minimal]
  refine ⟨?_, ?_⟩
  · intro B hB
    exact IsCovector.support_inter_isBasis_nonempty M hD.2.1 hD.1
      (M.isBasis_iff_underlying_isBase.mpr hB)
  · intro X hXhit hXD
    have hXground : X ⊆ M.underlying.E := by
      rw [M.underlying_spec.1]
      exact Set.subset_univ _
    have hXdepDual : M.underlying✶.Dep X :=
      Matroid.dual_dep_iff_forall.mpr ⟨hXhit, hXground⟩
    obtain ⟨K, hKX, hKdual⟩ := hXdepDual.exists_isCircuit_subset
    have hK : M.underlying.IsCocircuit K := hKdual
    obtain ⟨E, hE, hEsupport⟩ := M.exists_isCocircuit_support_eq hK
    have hED : E.support ⊆ D.support := by
      rw [hEsupport]
      exact hKX.trans hXD
    have hDE : D.support ⊆ E.support :=
      hD.2.2 hE.1 hE.2.1 hED
    exact hDE.trans (hEsupport.trans_subset hKX)

/-- Two signed cocircuits with the same support and the same sign at one support
element are equal. -/
theorem eq_of_isCocircuit_of_support_eq_of_sameSignAt
    [Fintype α] {D E : SignedSubset α}
    (hD : M.IsCocircuit D) (hE : M.IsCocircuit E)
    (hsupport : D.support = E.support) {e : α} (heD : e ∈ D.support)
    (hsame : D.SameSignAt E e) : D = E := by
  have hK : M.underlying.IsCocircuit D.support := M.isCocircuit_support hD
  obtain ⟨B, hBbase, heB, hfund⟩ :=
    M.underlying_exists_isBase_fundCocircuit_eq hK heD
  have hB : M.IsBasis B := M.isBasis_iff_underlying_isBase.mpr hBbase
  apply SignedSubset.eq_of_support_eq_of_forall_sameSignAt hsupport
  intro x hxD
  by_cases hxe : x = e
  · simpa [hxe] using hsame
  have hxFundCocircuit : x ∈ M.underlying.fundCocircuit e B := by
    rw [hfund]
    exact hxD
  have hxB : x ∉ B := by
    intro hxB
    have hxInter : x ∈ M.underlying.fundCocircuit e B ∩ B :=
      ⟨hxFundCocircuit, hxB⟩
    have : x = e := by
      rw [M.underlying.fundCocircuit_inter_eq heB] at hxInter
      simpa using hxInter
    exact hxe this
  let C : SignedSubset α := M.signedFundCircuit B hB x
  have hC : M.IsCircuit C := M.signedFundCircuit_isCircuit hB hxB
  have hCsupport : C.support = M.underlying.fundCircuit x B := by
    simpa [C] using M.signedFundCircuit_support hB hxB
  have heFundCircuit : e ∈ M.underlying.fundCircuit x B :=
    (hBbase.mem_fundCocircuit_iff_mem_fundCircuit).mp hxFundCocircuit
  have hinterD : C.support ∩ D.support = {e, x} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyFund : y ∈ M.underlying.fundCircuit x B := hCsupport ▸ hy.1
      rcases M.underlying.fundCircuit_subset_insert x B hyFund with hyx | hyB
      · exact Or.inr hyx
      · have hyCocircuit : y ∈ M.underlying.fundCocircuit e B := by
          rw [hfund]
          exact hy.2
        have hyInter : y ∈ M.underlying.fundCocircuit e B ∩ B :=
          ⟨hyCocircuit, hyB⟩
        have hye : y = e := by
          rw [M.underlying.fundCocircuit_inter_eq heB] at hyInter
          simpa using hyInter
        exact Or.inl hye
    · intro y hy
      rcases hy with (rfl | hyx)
      · exact ⟨hCsupport.symm ▸ heFundCircuit, heD⟩
      · have hyx' : y = x := by simpa using hyx
        subst y
        exact ⟨hCsupport.symm ▸ M.underlying.mem_fundCircuit x B, hxD⟩
  have hinterE : C.support ∩ E.support = {e, x} := by
    rw [← hsupport]
    exact hinterD
  exact SignedSubset.sameSignAt_of_orthogonal_pair_of_sameSignAt
    (hD.2.1 hC) (hE.2.1 hC) hinterD hinterE hsame

/-- Signed cocircuit orientations on a fixed support are unique up to global sign. -/
theorem eq_or_eq_neg_of_isCocircuit_support_eq
    [Fintype α] {D E : SignedSubset α}
    (hD : M.IsCocircuit D) (hE : M.IsCocircuit E)
    (hsupport : D.support = E.support) : D = E ∨ D = -E := by
  obtain ⟨e, heD⟩ := hD.1
  have heE : e ∈ E.support := hsupport ▸ heD
  rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem
      (show e ∈ D.support ∩ E.support from ⟨heD, heE⟩) with hsame | hopp
  · exact Or.inl (M.eq_of_isCocircuit_of_support_eq_of_sameSignAt
      hD hE hsupport heD hsame)
  · right
    have hnegE : M.IsCocircuit (-E) := M.neg_isCocircuit hE
    have hsameNeg : D.SameSignAt (-E) e := by
      simpa [SignedSubset.SameSignAt, SignedSubset.OppositeAt] using hopp
    exact M.eq_of_isCocircuit_of_support_eq_of_sameSignAt hD hnegE
      (by simpa using hsupport) heD hsameNeg

end Data
end OrientedMatroid
end BeyondSperner
