import BeyondSperner.OrientedMatroid.LexicographicCircuit
import BeyondSperner.OrientedMatroid.OrthogonalPairElimination

/-!
# Assembly of a lexicographic single-element extension

The circuit signing and every cocircuit containing the new point have already
been constructed in `LexicographicCircuit`.  This file isolates the one
remaining rank-two localization obligation: orienting ordinary cocircuit
supports which avoid the new point.  Once those secondary signings are
available, the finite Farkas/elimination theorem assembles the complete
oriented matroid automatically.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid

variable {α : Type*}

/-- Cocircuit signings compatible with every previously constructed circuit
candidate. -/
def compatibleLexCocircuits [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α)) :
    Set (SignedSubset (α ⊕ Unit)) :=
  {D | (principalLexMatroid M order hindep).IsCocircuit D.support ∧
    ∀ C ∈ lexSignedCircuits M order, C.Orthogonal D}

/-- The sole remaining localization obligation: every ordinary cocircuit
support avoiding the new point admits a compatible signing. -/
def HasSecondaryCocircuitSignings [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α)) : Prop :=
  ∀ K : Set (α ⊕ Unit),
    (principalLexMatroid M order hindep).IsCocircuit K →
    canonicalNew α ∉ K →
      ∃ D : SignedSubset (α ⊕ Unit),
        D ∈ compatibleLexCocircuits M order hindep ∧ D.support = K

/-- The genuinely new secondary obligation, excluding supports whose old part
is already an old cocircuit. -/
def HasStrictSecondaryCocircuitSignings [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α)) : Prop :=
  ∀ K : Set (α ⊕ Unit),
    (principalLexMatroid M order hindep).IsCocircuit K →
    canonicalNew α ∉ K →
    ¬ M.underlying.IsCocircuit (PrincipalExtension.oldPart K) →
      ∃ D : SignedSubset (α ⊕ Unit),
        D ∈ compatibleLexCocircuits M order hindep ∧ D.support = K

/-- Every primary lift is already a compatible cocircuit signing. -/
theorem lexPrimaryCocircuit_mem_compatible
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    {D : SignedSubset (α ⊕ Unit)}
    (hD : D ∈ lexPrimaryCocircuits M order) :
    D ∈ compatibleLexCocircuits M order hindep := by
  refine ⟨lexPrimaryCocircuit_support_isCocircuit
    M order hindep hD, ?_⟩
  intro C hC
  obtain ⟨E, hE, rfl⟩ := hD
  exact lexSignedCircuit_orthogonal_lexLift M order hC hE

/-- The strict secondary obligation implies the full one: if the old part is
already an old cocircuit, ordinary support minimality forces it to miss the
ordered principal set, so its primary zero lift supplies the signing. -/
theorem HasStrictSecondaryCocircuitSignings.toHasSecondary
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hstrict : HasStrictSecondaryCocircuitSignings M order hindep) :
    HasSecondaryCocircuitSignings M order hindep := by
  intro K hK hpK
  by_cases hKold : M.underlying.IsCocircuit
      (PrincipalExtension.oldPart K)
  · have hshape : Sum.inl '' PrincipalExtension.oldPart K = K := by
      apply PrincipalExtension.image_oldPart_eq_of_notMem K
      simpa [canonicalNew, PrincipalExtension.new] using hpK
    have hdisjoint : Disjoint (PrincipalExtension.oldPart K)
        (order.toFinset : Set α) := by
      rw [Set.disjoint_left]
      intro x hxKold hxOrder
      have hmeet : ((PrincipalExtension.oldPart K) ∩
          (order.toFinset : Set α)).Nonempty :=
        ⟨x, hxKold, hxOrder⟩
      have hInsert : (principalLexMatroid M order hindep).IsCocircuit
          (insert (canonicalNew α)
            (Sum.inl '' PrincipalExtension.oldPart K)) := by
        unfold principalLexMatroid
        exact PrincipalExtension.matroid_isCocircuit_insert_new_image_inl_of_nonempty_inter
          M.underlying (order.toFinset : Set α) M.underlying_spec.1
            (M.isIndependent_iff_underlying_indep.mp hindep) hKold hmeet
      have hsub : K ⊆ insert (canonicalNew α)
          (Sum.inl '' PrincipalExtension.oldPart K) := by
        intro z hzK
        exact Or.inr (hshape.symm ▸ hzK)
      have hEq := hK.eq_of_subset_isCircuit hInsert hsub
      apply hpK
      rw [hEq]
      exact Set.mem_insert _ _
    obtain ⟨D, hD, hDsupport⟩ :=
      M.exists_isCocircuit_support_eq hKold
    refine ⟨lexLift order D, ?_, ?_⟩
    · apply lexPrimaryCocircuit_mem_compatible M order hindep
      exact ⟨D, hD, rfl⟩
    · rw [lexLift_support_of_disjoint order D (by
        simpa [hDsupport] using hdisjoint), hDsupport, hshape]
  · exact hstrict K hK hpK hKold

/-- Conditional exact orthogonal signing of all circuits and cocircuits of the
principal extension. -/
noncomputable def lexOrthogonalPair
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    OrthogonalPair (principalLexMatroid M order hindep) where
  circuits := lexSignedCircuits M order
  cocircuits := compatibleLexCocircuits M order hindep
  circuit_support := fun hC ↦
    lexSignedCircuits_support_isCircuit M order hindep hC
  cocircuit_support := fun hD ↦ hD.1
  exists_circuit := fun hK ↦ exists_lexSignedCircuit_support M order hindep hK
  exists_cocircuit := by
    intro K hK
    by_cases hpK : canonicalNew α ∈ K
    · obtain ⟨D, hDprimary, hDsupport⟩ :=
        exists_lexPrimaryCocircuit_support_of_new_mem
          M order hindep hK hpK
      exact ⟨D, lexPrimaryCocircuit_mem_compatible
        M order hindep hDprimary, hDsupport⟩
    · exact hsecondary K hK hpK
  neg_circuit := fun hC ↦ lexSignedCircuits_neg M order hC
  neg_cocircuit := by
    intro D hD
    constructor
    · simpa using hD.1
    · intro C hC
      exact SignedSubset.orthogonal_neg_right_iff.mpr (hD.2 C hC)
  orthogonal := fun hC hD ↦ hD.2 _ hC

@[simp]
theorem lexOrthogonalPair_circuits
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    (lexOrthogonalPair M order hindep hsecondary).circuits =
      lexSignedCircuits M order := rfl

@[simp]
theorem lexOrthogonalPair_cocircuits
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    (lexOrthogonalPair M order hindep hsecondary).cocircuits =
      compatibleLexCocircuits M order hindep := rfl

/-- The oriented matroid assembled from the exact orthogonal signing. -/
noncomputable def lexExtensionData
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    Data (α ⊕ Unit) :=
  (lexOrthogonalPair M order hindep hsecondary).toData

@[simp]
theorem lexExtensionData_circuits
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    (lexExtensionData M order hindep hsecondary).circuits =
      lexSignedCircuits M order := rfl

/-- The derived ordinary matroid of the assembled oriented matroid is exactly
the principal extension used to classify all supports. -/
theorem lexExtensionData_underlying_eq
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    (lexExtensionData M order hindep hsecondary).underlying =
      principalLexMatroid M order hindep := by
  apply Matroid.ext_isCircuit
  · rw [(lexExtensionData M order hindep hsecondary).underlying_spec.1]
    simp [principalLexMatroid]
  · intro K _
    rw [(lexExtensionData M order hindep hsecondary).underlying_spec.2 K]
    constructor
    · rintro ⟨C, hC, rfl⟩
      exact lexSignedCircuits_support_isCircuit M order hindep hC
    · intro hK
      obtain ⟨C, hC, hCsupport⟩ :=
        exists_lexSignedCircuit_support M order hindep hK
      exact ⟨C, hC, hCsupport⟩

/-- The cocircuits derived from `Data` are exactly the compatible cocircuit
signings used by the orthogonal pair. -/
theorem lexExtensionData_isCocircuit_iff_compatible
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep)
    {D : SignedSubset (α ⊕ Unit)} :
    (lexExtensionData M order hindep hsecondary).IsCocircuit D ↔
      D ∈ compatibleLexCocircuits M order hindep := by
  let N := lexExtensionData M order hindep hsecondary
  constructor
  · intro hD
    constructor
    · rw [← lexExtensionData_underlying_eq
        M order hindep hsecondary]
      exact N.isCocircuit_support hD
    · intro C hC
      apply hD.2.1
      change C ∈ (lexExtensionData M order hindep hsecondary).circuits
      rw [lexExtensionData_circuits]
      exact hC
  · intro hD
    apply N.isCocircuit_of_isCovector_of_underlying_isCocircuit_support
    · intro C hC
      apply hD.2 C
      change C ∈ (lexExtensionData M order hindep hsecondary).circuits at hC
      rwa [lexExtensionData_circuits] at hC
    · rw [lexExtensionData_underlying_eq M order hindep hsecondary]
      exact hD.1

/-- Embedded old signed sets are extension circuits exactly when they were old
circuits; the new circuit candidates cannot occur because all of them contain
the new point. -/
theorem map_mem_lexSignedCircuits_iff
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α) (C : SignedSubset α) :
    C.map (canonicalOld α) ∈ lexSignedCircuits M order ↔
      M.IsCircuit C := by
  constructor
  · rintro (⟨D, hD, hEq⟩ | ⟨B, hminimal, hEq | hEq⟩)
    · have hCD : C = D :=
        SignedSubset.map_injective (canonicalOld α) hEq
      rwa [hCD]
    · have hpMap : canonicalNew α ∉
          (C.map (canonicalOld α)).support := by
        rw [SignedSubset.support_map]
        rintro ⟨x, _, hx⟩
        simp [canonicalOld, canonicalNew] at hx
      have hpLex : canonicalNew α ∈
          (lexCircuit M order B hminimal.1).support :=
        Or.inl (lexCircuit_new_positive M order B hminimal.1)
      exact (hpMap (hEq.symm ▸ hpLex)).elim
    · have hpMap : canonicalNew α ∉
          (C.map (canonicalOld α)).support := by
        rw [SignedSubset.support_map]
        rintro ⟨x, _, hx⟩
        simp [canonicalOld, canonicalNew] at hx
      have hpLex : canonicalNew α ∈
          (-(lexCircuit M order B hminimal.1)).support := by
        simpa using
          (show canonicalNew α ∈
            (lexCircuit M order B hminimal.1).support from
              Or.inl (lexCircuit_new_positive M order B hminimal.1))
      exact (hpMap (hEq.symm ▸ hpLex)).elim
  · intro hC
    exact Or.inl ⟨C, hC, rfl⟩

end OrientedMatroid
end BeyondSperner
