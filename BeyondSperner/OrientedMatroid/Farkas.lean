import BeyondSperner.OrientedMatroid.Dual
import Mathlib.Combinatorics.Matroid.Minor.Contract

/-!
# The finite oriented-matroid Farkas alternative

This file isolates the self-dual finite argument used in the duality theorem.  An
`OrthogonalPair` is an orientation of the circuits and cocircuits of an ordinary
matroid, with only sign reversal and circuit--cocircuit orthogonality assumed.
The Farkas alternative is proved by deletion/contraction induction; no cocircuit
elimination axiom is assumed.
-/

namespace BeyondSperner

open Set
open scoped Matroid

namespace OrientedMatroid

variable {α : Type*}

/-- Signed circuit and cocircuit orientations of an ordinary matroid. -/
structure OrthogonalPair (U : Matroid α) where
  circuits : Set (SignedSubset α)
  cocircuits : Set (SignedSubset α)
  circuit_support : ∀ {C}, C ∈ circuits → U.IsCircuit C.support
  cocircuit_support : ∀ {D}, D ∈ cocircuits → U.IsCocircuit D.support
  exists_circuit : ∀ {K}, U.IsCircuit K →
    ∃ C, C ∈ circuits ∧ C.support = K
  exists_cocircuit : ∀ {K}, U.IsCocircuit K →
    ∃ D, D ∈ cocircuits ∧ D.support = K
  neg_circuit : ∀ {C}, C ∈ circuits → -C ∈ circuits
  neg_cocircuit : ∀ {D}, D ∈ cocircuits → -D ∈ cocircuits
  orthogonal : ∀ {C D}, C ∈ circuits → D ∈ cocircuits → C.Orthogonal D

namespace OrthogonalPair

variable {U : Matroid α} (P : OrthogonalPair U)

/-- Exchange circuits and cocircuits and pass to the ordinary dual. -/
noncomputable def swap : OrthogonalPair U✶ where
  circuits := P.cocircuits
  cocircuits := P.circuits
  circuit_support := fun hD ↦ P.cocircuit_support hD
  cocircuit_support := by
    intro C hC
    simpa using P.circuit_support hC
  exists_circuit := by
    intro K hK
    exact P.exists_cocircuit hK
  exists_cocircuit := by
    intro K hK
    apply P.exists_circuit
    simpa using hK
  neg_circuit := fun hD ↦ P.neg_cocircuit hD
  neg_cocircuit := fun hC ↦ P.neg_circuit hC
  orthogonal := by
    intro D C hD hC
    exact SignedSubset.orthogonal_comm.mpr (P.orthogonal hC hD)

/-- Orient a signed circuit positively at a prescribed support element. -/
theorem exists_circuit_positive {K : Set α} (hK : U.IsCircuit K)
    {e : α} (heK : e ∈ K) :
    ∃ C, C ∈ P.circuits ∧ C.support = K ∧ e ∈ C.positive := by
  obtain ⟨C, hC, hCsupport⟩ := P.exists_circuit hK
  have heC : e ∈ C.support := hCsupport.symm ▸ heK
  rcases heC with hepos | heneg
  · exact ⟨C, hC, hCsupport, hepos⟩
  · exact ⟨-C, P.neg_circuit hC, by simpa using hCsupport, by simpa using heneg⟩

/-- Orient a signed cocircuit positively at a prescribed support element. -/
theorem exists_cocircuit_positive {K : Set α} (hK : U.IsCocircuit K)
    {e : α} (heK : e ∈ K) :
    ∃ D, D ∈ P.cocircuits ∧ D.support = K ∧ e ∈ D.positive := by
  obtain ⟨D, hD, hDsupport⟩ := P.exists_cocircuit hK
  have heD : e ∈ D.support := hDsupport.symm ▸ heK
  rcases heD with hepos | heneg
  · exact ⟨D, hD, hDsupport, hepos⟩
  · exact ⟨-D, P.neg_cocircuit hD, by simpa using hDsupport, by simpa using heneg⟩

/-- A cocircuit of a deletion lifts to a cocircuit before deletion, changing
its support by at most the deleted set. -/
private theorem exists_isCocircuit_lift_delete {F K : Set α}
    (hK : (U ＼ F).IsCocircuit K) :
    ∃ K', U.IsCocircuit K' ∧ K ⊆ K' ∧ K' ⊆ K ∪ F := by
  have hdual : (U✶ ／ F).IsCircuit K := by
    rw [← Matroid.dual_delete]
    exact hK
  obtain ⟨K', hK', hKK', hK'sub⟩ := hdual.exists_subset_isCircuit_of_contract
  exact ⟨K', by simpa using hK', hKK', hK'sub⟩

/-- The pair induced on a one-element deletion. -/
noncomputable def delete (f : α) : OrthogonalPair (U ＼ {f}) where
  circuits := {X | ∃ C ∈ P.circuits, f ∉ C.support ∧ X = C}
  cocircuits := {Y | (U ＼ {f}).IsCocircuit Y.support ∧
    ∃ D ∈ P.cocircuits, Y = D.erase f}
  circuit_support := by
    rintro X ⟨C, hC, hfC, rfl⟩
    rw [Matroid.delete_isCircuit_iff]
    exact ⟨P.circuit_support hC, Set.disjoint_singleton_right.mpr hfC⟩
  cocircuit_support := fun hY ↦ hY.1
  exists_circuit := by
    intro K hK
    have hKU : U.IsCircuit K := hK.of_delete
    obtain ⟨C, hC, hCsupport⟩ := P.exists_circuit hKU
    have hfC : f ∉ C.support := by
      rw [hCsupport]
      exact Set.disjoint_singleton_right.mp
        (Matroid.delete_isCircuit_iff.mp hK).2
    exact ⟨C, ⟨C, hC, hfC, rfl⟩, hCsupport⟩
  exists_cocircuit := by
    intro K hK
    obtain ⟨K', hK'U, hKK', hK'sub⟩ :=
      exists_isCocircuit_lift_delete hK
    obtain ⟨D, hD, hDsupport⟩ := P.exists_cocircuit hK'U
    have hKf : f ∉ K := by
      intro hfK
      have hfGround := hK.subset_ground hfK
      rw [Matroid.delete_ground] at hfGround
      exact hfGround.2 (by simp)
    have hEraseSupport : (D.erase f).support = K := by
      rw [SignedSubset.support_erase, hDsupport]
      apply Set.Subset.antisymm
      · intro x hx
        rcases hK'sub hx.1 with hxK | hxf
        · exact hxK
        · exact (hx.2 (by simpa using hxf)).elim
      · intro x hxK
        exact ⟨hKK' hxK, by
          intro hxf
          subst x
          exact hKf hxK⟩
    refine ⟨D.erase f, ?_, hEraseSupport⟩
    exact ⟨by simpa [hEraseSupport] using hK, ⟨D, hD, rfl⟩⟩
  neg_circuit := by
    rintro X ⟨C, hC, hfC, hXC⟩
    refine ⟨-C, P.neg_circuit hC, by simpa using hfC, ?_⟩
    simp [hXC]
  neg_cocircuit := by
    rintro Y ⟨hYminor, D, hD, hYD⟩
    refine ⟨by simpa using hYminor, -D, P.neg_cocircuit hD, ?_⟩
    simp [hYD]
  orthogonal := by
    rintro X Y ⟨C, hC, hfC, rfl⟩ ⟨_, D, hD, rfl⟩
    exact SignedSubset.orthogonal_erase_right_of_not_mem_left
      (P.orthogonal hC hD) hfC

/-- The pair induced on a one-element contraction. -/
noncomputable def contract (f : α) : OrthogonalPair (U ／ {f}) where
  circuits := {X | (U ／ {f}).IsCircuit X.support ∧
    ∃ C ∈ P.circuits, X = C.erase f}
  cocircuits := {Y | ∃ D ∈ P.cocircuits, f ∉ D.support ∧ Y = D}
  circuit_support := fun hX ↦ hX.1
  cocircuit_support := by
    rintro Y ⟨D, hD, hfD, rfl⟩
    apply Matroid.contract_isCocircuit_iff.mpr
    exact ⟨P.cocircuit_support hD,
      Set.disjoint_singleton_right.mpr hfD⟩
  exists_circuit := by
    intro K hK
    obtain ⟨K', hK'U, hKK', hK'sub⟩ := hK.exists_subset_isCircuit_of_contract
    obtain ⟨C, hC, hCsupport⟩ := P.exists_circuit hK'U
    have hKf : f ∉ K := by
      intro hfK
      have hfGround := hK.subset_ground hfK
      rw [Matroid.contract_ground] at hfGround
      exact hfGround.2 (by simp)
    have hEraseSupport : (C.erase f).support = K := by
      rw [SignedSubset.support_erase, hCsupport]
      apply Set.Subset.antisymm
      · intro x hx
        rcases hK'sub hx.1 with hxK | hxf
        · exact hxK
        · exact (hx.2 (by simpa using hxf)).elim
      · intro x hxK
        exact ⟨hKK' hxK, by
          intro hxf
          subst x
          exact hKf hxK⟩
    refine ⟨C.erase f, ?_, hEraseSupport⟩
    exact ⟨by simpa [hEraseSupport] using hK, ⟨C, hC, rfl⟩⟩
  exists_cocircuit := by
    intro K hK
    have hKU : U.IsCocircuit K := hK.of_contract
    obtain ⟨D, hD, hDsupport⟩ := P.exists_cocircuit hKU
    have hfD : f ∉ D.support := by
      rw [hDsupport]
      have hground := hK.subset_ground
      rw [Matroid.contract_ground] at hground
      exact fun hf ↦ (hground hf).2 (by simp)
    exact ⟨D, ⟨D, hD, hfD, rfl⟩, hDsupport⟩
  neg_circuit := by
    rintro X ⟨hXminor, C, hC, hXC⟩
    refine ⟨by simpa using hXminor, -C, P.neg_circuit hC, ?_⟩
    simp [hXC]
  neg_cocircuit := by
    rintro Y ⟨D, hD, hfD, hYD⟩
    refine ⟨-D, P.neg_cocircuit hD, by simpa using hfD, ?_⟩
    simp [hYD]
  orthogonal := by
    rintro X Y ⟨_, C, hC, rfl⟩ ⟨D, hD, hfD, rfl⟩
    exact SignedSubset.orthogonal_erase_left_of_not_mem_right
      (P.orthogonal hC hD) hfD

/-- The pair induced on deletion of an arbitrary set. -/
noncomputable def deleteSet (F : Set α) : OrthogonalPair (U ＼ F) where
  circuits := {X | ∃ C ∈ P.circuits, Disjoint C.support F ∧ X = C}
  cocircuits := {Y | (U ＼ F).IsCocircuit Y.support ∧
    ∃ D ∈ P.cocircuits, Y = D.remove F}
  circuit_support := by
    rintro X ⟨C, hC, hCF, rfl⟩
    exact Matroid.delete_isCircuit_iff.mpr ⟨P.circuit_support hC, hCF⟩
  cocircuit_support := fun hY ↦ hY.1
  exists_circuit := by
    intro K hK
    obtain ⟨C, hC, hCsupport⟩ := P.exists_circuit hK.of_delete
    have hdisj : Disjoint C.support F := by
      rw [hCsupport]
      exact (Matroid.delete_isCircuit_iff.mp hK).2
    exact ⟨C, ⟨C, hC, hdisj, rfl⟩, hCsupport⟩
  exists_cocircuit := by
    intro K hK
    obtain ⟨K', hK'U, hKK', hK'sub⟩ :=
      exists_isCocircuit_lift_delete hK
    obtain ⟨D, hD, hDsupport⟩ := P.exists_cocircuit hK'U
    have hKF : Disjoint K F := by
      rw [Set.disjoint_left]
      intro x hxK hxF
      have hxGround := hK.subset_ground hxK
      rw [Matroid.delete_ground] at hxGround
      exact hxGround.2 hxF
    have hRemoveSupport : (D.remove F).support = K := by
      rw [SignedSubset.support_remove, hDsupport]
      apply Set.Subset.antisymm
      · intro x hx
        rcases hK'sub hx.1 with hxK | hxF
        · exact hxK
        · exact (hx.2 hxF).elim
      · intro x hxK
        exact ⟨hKK' hxK, fun hxF ↦ Set.disjoint_left.1 hKF hxK hxF⟩
    refine ⟨D.remove F, ?_, hRemoveSupport⟩
    exact ⟨by simpa [hRemoveSupport] using hK, ⟨D, hD, rfl⟩⟩
  neg_circuit := by
    rintro X ⟨C, hC, hCF, hXC⟩
    refine ⟨-C, P.neg_circuit hC, by simpa using hCF, ?_⟩
    simp [hXC]
  neg_cocircuit := by
    rintro Y ⟨hYminor, D, hD, hYD⟩
    refine ⟨by simpa using hYminor, -D, P.neg_cocircuit hD, ?_⟩
    simp [hYD]
  orthogonal := by
    rintro X Y ⟨C, hC, hCF, rfl⟩ ⟨_, D, hD, rfl⟩
    rcases P.orthogonal hC hD with hdisj | ⟨u, hu, v, hv, hs, ho⟩
    · left
      apply hdisj.mono_right
      rw [SignedSubset.support_remove]
      exact Set.sdiff_subset
    · right
      have huF : u ∉ F := fun huF ↦ Set.disjoint_left.1 hCF hu.1 huF
      have hvF : v ∉ F := fun hvF ↦ Set.disjoint_left.1 hCF hv.1 hvF
      refine ⟨u, ⟨hu.1, by simpa [huF] using hu.2⟩,
        v, ⟨hv.1, by simpa [hvF] using hv.2⟩, ?_, ?_⟩
      · rcases hs with hs | hs
        · exact Or.inl ⟨hs.1, by simpa [huF] using hs.2⟩
        · exact Or.inr ⟨hs.1, by simpa [huF] using hs.2⟩
      · rcases ho with ho | ho
        · exact Or.inl ⟨ho.1, by simpa [hvF] using ho.2⟩
        · exact Or.inr ⟨ho.1, by simpa [hvF] using ho.2⟩

/-- The pair induced on contraction of an arbitrary set. -/
noncomputable def contractSet (F : Set α) : OrthogonalPair (U ／ F) where
  circuits := {X | (U ／ F).IsCircuit X.support ∧
    ∃ C ∈ P.circuits, X = C.remove F}
  cocircuits := {Y | ∃ D ∈ P.cocircuits, Disjoint D.support F ∧ Y = D}
  circuit_support := fun hX ↦ hX.1
  cocircuit_support := by
    rintro Y ⟨D, hD, hDF, rfl⟩
    exact Matroid.contract_isCocircuit_iff.mpr ⟨P.cocircuit_support hD, hDF⟩
  exists_circuit := by
    intro K hK
    obtain ⟨K', hK'U, hKK', hK'sub⟩ := hK.exists_subset_isCircuit_of_contract
    obtain ⟨C, hC, hCsupport⟩ := P.exists_circuit hK'U
    have hKF : Disjoint K F := by
      rw [Set.disjoint_left]
      intro x hxK hxF
      have hxGround := hK.subset_ground hxK
      rw [Matroid.contract_ground] at hxGround
      exact hxGround.2 hxF
    have hRemoveSupport : (C.remove F).support = K := by
      rw [SignedSubset.support_remove, hCsupport]
      apply Set.Subset.antisymm
      · intro x hx
        rcases hK'sub hx.1 with hxK | hxF
        · exact hxK
        · exact (hx.2 hxF).elim
      · intro x hxK
        exact ⟨hKK' hxK, fun hxF ↦ Set.disjoint_left.1 hKF hxK hxF⟩
    refine ⟨C.remove F, ?_, hRemoveSupport⟩
    exact ⟨by simpa [hRemoveSupport] using hK, ⟨C, hC, rfl⟩⟩
  exists_cocircuit := by
    intro K hK
    have hKU : U.IsCocircuit K := hK.of_contract
    obtain ⟨D, hD, hDsupport⟩ := P.exists_cocircuit hKU
    have hKF : Disjoint K F := (Matroid.contract_isCocircuit_iff.mp hK).2
    exact ⟨D, ⟨D, hD, by simpa [hDsupport] using hKF, rfl⟩, hDsupport⟩
  neg_circuit := by
    rintro X ⟨hXminor, C, hC, hXC⟩
    refine ⟨by simpa using hXminor, -C, P.neg_circuit hC, ?_⟩
    simp [hXC]
  neg_cocircuit := by
    rintro Y ⟨D, hD, hDF, hYD⟩
    refine ⟨-D, P.neg_cocircuit hD, by simpa using hDF, ?_⟩
    simp [hYD]
  orthogonal := by
    rintro X Y ⟨_, C, hC, rfl⟩ ⟨D, hD, hDF, rfl⟩
    rcases P.orthogonal hC hD with hdisj | ⟨u, hu, v, hv, hs, ho⟩
    · left
      apply hdisj.mono_left
      rw [SignedSubset.support_remove]
      exact Set.sdiff_subset
    · right
      have huF : u ∉ F := fun huF ↦ Set.disjoint_left.1 hDF hu.2 huF
      have hvF : v ∉ F := fun hvF ↦ Set.disjoint_left.1 hDF hv.2 hvF
      refine ⟨u, ⟨by simpa [huF] using hu.1, hu.2⟩,
        v, ⟨by simpa [hvF] using hv.1, hv.2⟩, ?_, ?_⟩
      · rcases hs with hs | hs
        · exact Or.inl ⟨by simpa [huF] using hs.1, hs.2⟩
        · exact Or.inr ⟨by simpa [huF] using hs.1, hs.2⟩
      · rcases ho with ho | ho
        · exact Or.inl ⟨by simpa [hvF] using ho.1, ho.2⟩
        · exact Or.inr ⟨by simpa [hvF] using ho.1, ho.2⟩

/-- Simultaneously reorient the circuit and cocircuit signatures. -/
noncomputable def reorient (A : Set α) : OrthogonalPair U where
  circuits := {X | ∃ C ∈ P.circuits, X = C.reorient A}
  cocircuits := {Y | ∃ D ∈ P.cocircuits, Y = D.reorient A}
  circuit_support := by
    rintro X ⟨C, hC, rfl⟩
    simpa using P.circuit_support hC
  cocircuit_support := by
    rintro Y ⟨D, hD, rfl⟩
    simpa using P.cocircuit_support hD
  exists_circuit := by
    intro K hK
    obtain ⟨C, hC, hCsupport⟩ := P.exists_circuit hK
    exact ⟨C.reorient A, ⟨C, hC, rfl⟩, by simpa using hCsupport⟩
  exists_cocircuit := by
    intro K hK
    obtain ⟨D, hD, hDsupport⟩ := P.exists_cocircuit hK
    exact ⟨D.reorient A, ⟨D, hD, rfl⟩, by simpa using hDsupport⟩
  neg_circuit := by
    rintro X ⟨C, hC, hXC⟩
    refine ⟨-C, P.neg_circuit hC, ?_⟩
    simp [hXC]
  neg_cocircuit := by
    rintro Y ⟨D, hD, hYD⟩
    refine ⟨-D, P.neg_cocircuit hD, ?_⟩
    simp [hYD]
  orthogonal := by
    rintro X Y ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    exact SignedSubset.reorient_orthogonal_iff.mpr (P.orthogonal hC hD)

/-- A positive signed circuit through `e`. -/
def HasPositiveCircuitAt (e : α) : Prop :=
  ∃ C, C ∈ P.circuits ∧ C.negative = ∅ ∧ e ∈ C.positive

/-- A positive signed cocircuit through `e`. -/
def HasPositiveCocircuitAt (e : α) : Prop :=
  ∃ D, D ∈ P.cocircuits ∧ D.negative = ∅ ∧ e ∈ D.positive

/-- A signed set supported exactly at a positive coordinate has no negative part. -/
private theorem negative_eq_empty_of_support_eq_singleton
    {X : SignedSubset α} {e : α} (hX : X.support = {e})
    (hepos : e ∈ X.positive) : X.negative = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hxneg
  have hxe : x = e := by
    have hxSupport : x ∈ X.support := Or.inr hxneg
    rw [hX] at hxSupport
    simpa using hxSupport
  subst x
  exact Set.disjoint_left.1 X.disjoint hepos hxneg

set_option maxHeartbeats 800000 in
/-- Finite Farkas alternative: every ground element lies in a positive circuit
or in a positive cocircuit.  The proof uses only the fields of `OrthogonalPair`;
in particular it does not presuppose cocircuit elimination. -/
theorem farkas [Fintype α] {e : α} (heGround : e ∈ U.E) :
    P.HasPositiveCircuitAt e ∨ P.HasPositiveCocircuitAt e := by
  classical
  induction hn : U.E.ncard using Nat.strong_induction_on generalizing U P with
  | h n ih =>
      by_cases hrest : (U.E \ {e}).Nonempty
      · obtain ⟨f, hfGround, hfe⟩ := hrest
        have hfe' : f ≠ e := by simpa using hfe
        have heDelete : e ∈ (U ＼ {f}).E := by
          rw [Matroid.delete_ground]
          exact ⟨heGround, by simpa [eq_comm] using hfe'⟩
        have heContract : e ∈ (U ／ {f}).E := by
          rw [Matroid.contract_ground]
          exact ⟨heGround, by simpa [eq_comm] using hfe'⟩
        have hstrict : U.E \ {f} ⊂ U.E :=
          Set.sdiff_singleton_ssubset.mpr hfGround
        have hcardlt : (U.E \ {f}).ncard < U.E.ncard :=
          Set.ncard_lt_ncard hstrict
        have hdeleteCard : (U ＼ {f}).E.ncard < n := by
          rw [Matroid.delete_ground, ← hn]
          exact hcardlt
        have hcontractCard : (U ／ {f}).E.ncard < n := by
          rw [Matroid.contract_ground, ← hn]
          exact hcardlt
        have hDeleteAlt := ih _ hdeleteCard (P.delete f) heDelete rfl
        rcases hDeleteAlt with hCdelete | hDdelete
        · left
          rcases hCdelete with ⟨X, ⟨C, hC, _, hXC⟩, hXneg, heXpos⟩
          refine ⟨C, hC, ?_, ?_⟩
          · simpa [hXC] using hXneg
          · simpa [hXC] using heXpos
        · have hContractAlt := ih _ hcontractCard (P.contract f) heContract rfl
          rcases hContractAlt with hCcontract | hDcontract
          · rcases hDdelete with
              ⟨Y, ⟨_, D, hD, hYD⟩, hYneg, heYpos⟩
            rcases hCcontract with
              ⟨X, ⟨_, C, hC, hXC⟩, hXneg, heXpos⟩
            have hDeraseNeg : (D.erase f).negative = ∅ := by
              simpa [hYD] using hYneg
            have hCeraseNeg : (C.erase f).negative = ∅ := by
              simpa [hXC] using hXneg
            have heDpos : e ∈ D.positive := by
              have : e ∈ (D.erase f).positive := by simpa [hYD] using heYpos
              exact this.1
            have heCpos : e ∈ C.positive := by
              have : e ∈ (C.erase f).positive := by simpa [hXC] using heXpos
              exact this.1
            by_cases hfCsupport : f ∈ C.support
            · by_cases hfCpos : f ∈ C.positive
              · left
                refine ⟨C, hC, ?_, heCpos⟩
                apply Set.eq_empty_iff_forall_notMem.mpr
                intro x hxCneg
                have hxf : x = f := by
                  by_contra h
                  have : x ∈ (C.erase f).negative := ⟨hxCneg, by simpa using h⟩
                  rw [hCeraseNeg] at this
                  exact this.elim
                subst x
                exact Set.disjoint_left.1 C.disjoint hfCpos hxCneg
              · by_cases hfDsupport : f ∈ D.support
                · by_cases hfDpos : f ∈ D.positive
                  · right
                    refine ⟨D, hD, ?_, heDpos⟩
                    apply Set.eq_empty_iff_forall_notMem.mpr
                    intro x hxDneg
                    have hxf : x = f := by
                      by_contra h
                      have : x ∈ (D.erase f).negative :=
                        ⟨hxDneg, by simpa using h⟩
                      rw [hDeraseNeg] at this
                      exact this.elim
                    subst x
                    exact Set.disjoint_left.1 D.disjoint hfDpos hxDneg
                  · have horth := P.orthogonal hC hD
                    rcases horth with hdisjoint | ⟨u, hu, v, hv, _, hvopp⟩
                    · exact (Set.disjoint_left.1 hdisjoint (Or.inl heCpos)
                        (Or.inl heDpos)).elim
                    · rcases hvopp with hvopp | hvopp
                      · by_cases hvf : v = f
                        · subst v
                          exact (hfCpos hvopp.1).elim
                        · have hvErase : v ∈ (D.erase f).negative :=
                            ⟨hvopp.2, by simpa using hvf⟩
                          rw [hDeraseNeg] at hvErase
                          exact hvErase.elim
                      · by_cases hvf : v = f
                        · subst v
                          exact (hfDpos hvopp.2).elim
                        · have hvErase : v ∈ (C.erase f).negative :=
                            ⟨hvopp.1, by simpa using hvf⟩
                          rw [hCeraseNeg] at hvErase
                          exact hvErase.elim
                · right
                  refine ⟨D, hD, ?_, heDpos⟩
                  apply Set.eq_empty_iff_forall_notMem.mpr
                  intro x hxDneg
                  by_cases hxf : x = f
                  · subst x
                    exact hfDsupport (Or.inr hxDneg)
                  · have : x ∈ (D.erase f).negative :=
                      ⟨hxDneg, by simpa using hxf⟩
                    rw [hDeraseNeg] at this
                    exact this.elim
            · left
              refine ⟨C, hC, ?_, heCpos⟩
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro x hxCneg
              by_cases hxf : x = f
              · subst x
                exact hfCsupport (Or.inr hxCneg)
              · have : x ∈ (C.erase f).negative :=
                  ⟨hxCneg, by simpa using hxf⟩
                rw [hCeraseNeg] at this
                exact this.elim
          · right
            rcases hDcontract with ⟨D, ⟨D', hD', _, hDD'⟩, hDneg, heDpos⟩
            refine ⟨D', hD', ?_, ?_⟩
            · simpa [hDD'] using hDneg
            · simpa [hDD'] using heDpos
      · have hgroundSubset : U.E ⊆ {e} := by
          intro x hxE
          by_contra hxe
          exact hrest ⟨x, hxE, by simpa using hxe⟩
        by_cases hIndep : U.Indep {e}
        · have heColoop : U.IsColoop e := by
            rw [Matroid.isColoop_iff_forall_mem_isBase]
            intro B hB
            by_contra heB
            have hBempty : B = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro x hxB
              have hxe : x = e := by
                simpa using hgroundSubset (hB.subset_ground hxB)
              exact heB (hxe ▸ hxB)
            have hsingletonSub : B ⊆ {e} := by simp [hBempty]
            have hsingleSubB : {e} ⊆ B :=
              (Matroid.isBase_iff_maximal_indep.mp hB).2 hIndep hsingletonSub
            exact heB (hsingleSubB (by simp))
          have hK : U.IsCocircuit {e} := Matroid.singleton_isCocircuit.mpr heColoop
          obtain ⟨D, hD, hDsupport, heDpos⟩ :=
            P.exists_cocircuit_positive (e := e) hK (by simp)
          right
          exact ⟨D, hD,
            negative_eq_empty_of_support_eq_singleton hDsupport heDpos, heDpos⟩
        · have heLoop : U.IsLoop e :=
            (Matroid.singleton_not_indep heGround).mp hIndep
          have hK : U.IsCircuit {e} := Matroid.singleton_isCircuit.mpr heLoop
          obtain ⟨C, hC, hCsupport, heCpos⟩ :=
            P.exists_circuit_positive (e := e) hK (by simp)
          left
          exact ⟨C, hC,
            negative_eq_empty_of_support_eq_singleton hCsupport heCpos, heCpos⟩

/-- The four-painting form of the finite Farkas alternative.  The colors
`R,G,B,W` respectively prescribe positive, negative, contracted, and deleted
coordinates.  The conclusion is stated back in the original pair, rather than
only in the deletion/contraction minor. -/
theorem fourPainting [Fintype α]
    {R G B W : Set α} {e : α}
    (heGround : e ∈ U.E) (heR : e ∈ R)
    (hRG : Disjoint R G) (hRB : Disjoint R B) (hRW : Disjoint R W)
    (hBW : Disjoint B W)
    (hcover : U.E ⊆ R ∪ G ∪ B ∪ W) :
    (∃ C, C ∈ P.circuits ∧
      C.positive ⊆ R ∪ B ∧ C.negative ⊆ G ∪ B ∧
      Disjoint C.support W ∧ e ∈ C.positive) ∨
    (∃ D, D ∈ P.cocircuits ∧
      D.positive ⊆ R ∪ W ∧ D.negative ⊆ G ∪ W ∧
      Disjoint D.support B ∧ e ∈ D.positive) := by
  classical
  let Q := (P.reorient G).contractSet B
  let Q' := Q.deleteSet W
  have heB : e ∉ B := Set.disjoint_left.1 hRB heR
  have heW : e ∉ W := Set.disjoint_left.1 hRW heR
  have heMinor : e ∈ ((U ／ B) ＼ W).E := by
    rw [Matroid.delete_ground, Matroid.contract_ground]
    exact ⟨⟨heGround, heB⟩, heW⟩
  rcases Q'.farkas heMinor with hCircuit | hCocircuit
  · left
    rcases hCircuit with
      ⟨X, ⟨Y, ⟨_, C', ⟨C, hC, rfl⟩, hYC⟩, hYW, hXY⟩,
        hXnegative, heXpositive⟩
    have hCremoveNegative : ((C.reorient G).remove B).negative = ∅ := by
      simpa [hXY, hYC] using hXnegative
    have heCremovePositive : e ∈ ((C.reorient G).remove B).positive := by
      simpa [hXY, hYC] using heXpositive
    have hCW : Disjoint C.support W := by
      rw [Set.disjoint_left] at hYW ⊢
      intro x hxC hxW
      have hxNotB : x ∉ B := fun hxB ↦
        Set.disjoint_left.1 hBW hxB hxW
      have hxY : x ∈ Y.support := by
        rw [hYC, SignedSubset.support_remove,
          SignedSubset.support_reorient]
        exact ⟨hxC, hxNotB⟩
      exact hYW hxY hxW
    have hCground : C.support ⊆ U.E :=
      (P.circuit_support hC).subset_ground
    refine ⟨C, hC, ?_, ?_, hCW, ?_⟩
    · intro x hxC
      by_cases hxB : x ∈ B
      · exact Or.inr hxB
      have hxNotG : x ∉ G := by
        intro hxG
        have hxNeg : x ∈ ((C.reorient G).remove B).negative := by
          exact ⟨Or.inr ⟨hxC, hxG⟩, hxB⟩
        rw [hCremoveNegative] at hxNeg
        exact hxNeg.elim
      have hxNotW : x ∉ W := fun hxW ↦
        Set.disjoint_left.1 hCW (Or.inl hxC) hxW
      rcases hcover (hCground (Or.inl hxC)) with hxRGB | hxW
      · rcases hxRGB with hxRG | hxB'
        · rcases hxRG with hxR | hxG
          · exact Or.inl hxR
          · exact (hxNotG hxG).elim
        · exact Or.inr hxB'
      · exact (hxNotW hxW).elim
    · intro x hxC
      by_cases hxB : x ∈ B
      · exact Or.inr hxB
      by_cases hxG : x ∈ G
      · exact Or.inl hxG
      have hxNeg : x ∈ ((C.reorient G).remove B).negative := by
        exact ⟨Or.inl ⟨hxC, hxG⟩, hxB⟩
      rw [hCremoveNegative] at hxNeg
      exact hxNeg.elim
    · rcases heCremovePositive.1 with heC | heC
      · exact heC.1
      · exact (Set.disjoint_left.1 hRG heR heC.2).elim
  · right
    rcases hCocircuit with
      ⟨Y, ⟨_, Z, ⟨D', ⟨D, hD, rfl⟩, hDB, rfl⟩, rfl⟩,
        hYnegative, heYpositive⟩
    have hDremoveNegative : ((D.reorient G).remove W).negative = ∅ :=
      hYnegative
    have heDremovePositive : e ∈ ((D.reorient G).remove W).positive :=
      heYpositive
    have hDground : D.support ⊆ U.E :=
      (P.cocircuit_support hD).subset_ground
    have hDB' : Disjoint D.support B := by simpa using hDB
    refine ⟨D, hD, ?_, ?_, hDB', ?_⟩
    · intro x hxD
      by_cases hxW : x ∈ W
      · exact Or.inr hxW
      have hxNotG : x ∉ G := by
        intro hxG
        have hxNeg : x ∈ ((D.reorient G).remove W).negative := by
          exact ⟨Or.inr ⟨hxD, hxG⟩, hxW⟩
        rw [hDremoveNegative] at hxNeg
        exact hxNeg.elim
      have hxNotB : x ∉ B := fun hxB ↦
        Set.disjoint_left.1 hDB' (Or.inl hxD) hxB
      rcases hcover (hDground (Or.inl hxD)) with hxRGB | hxW'
      · rcases hxRGB with hxRG | hxB
        · rcases hxRG with hxR | hxG
          · exact Or.inl hxR
          · exact (hxNotG hxG).elim
        · exact (hxNotB hxB).elim
      · exact Or.inr hxW'
    · intro x hxD
      by_cases hxW : x ∈ W
      · exact Or.inr hxW
      by_cases hxG : x ∈ G
      · exact Or.inl hxG
      have hxNeg : x ∈ ((D.reorient G).remove W).negative := by
        exact ⟨Or.inl ⟨hxD, hxG⟩, hxW⟩
      rw [hDremoveNegative] at hxNeg
      exact hxNeg.elim
    · rcases heDremovePositive.1 with heD | heD
      · exact heD.1
      · exact (Set.disjoint_left.1 hRG heR heD.2).elim

end OrthogonalPair

namespace Data

variable (M : Data α)

/-- The signed circuits and support-minimal covectors of an oriented matroid
form an orthogonal pair over its underlying ordinary matroid. -/
noncomputable def orthogonalPair [Fintype α] :
    OrthogonalPair M.underlying where
  circuits := M.circuits
  cocircuits := {D | M.IsCocircuit D}
  circuit_support := by
    intro C hC
    exact (M.underlying_spec.2 C.support).mpr ⟨C, hC, rfl⟩
  cocircuit_support := fun hD ↦ M.isCocircuit_support hD
  exists_circuit := by
    intro K hK
    exact (M.underlying_spec.2 K).mp hK
  exists_cocircuit := fun hK ↦ M.exists_isCocircuit_support_eq hK
  neg_circuit := fun hC ↦ M.neg_isCircuit hC
  neg_cocircuit := fun hD ↦ M.neg_isCocircuit hD
  orthogonal := fun hC hD ↦ hD.2.1 hC

end Data

end OrientedMatroid
end BeyondSperner
