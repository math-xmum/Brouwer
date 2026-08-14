import BeyondSperner.Simplicial.ChainSimplex
import BeyondSperner.OrientedMatroid.Todd

/-!
# Oriented-matroid colorings: the nondegenerate case

Definitions and proved statements from Section 6.  The types expose every mathematical hypothesis
used by the paper, and the file proves the nondegenerate counting route through Theorem 6.5,
including its parity conclusion.
-/

namespace BeyondSperner

open Classical
open Set

namespace MatroidColoring

variable {I M V : Type*}

/--
The oriented-matroid framework of Sections 6 and 8: an acyclic oriented matroid, a basis
`B = {v_i}`, and a distinguished `b ∈ conv(B) \ B`.
-/
structure Framework (I M : Type*) where
  matroid : OrientedMatroid.Data M
  vertex : I ↪ M
  distinguished : M
  basis_isBasis : matroid.IsBasis (Set.range vertex)
  distinguished_notMem_basis : distinguished ∉ Set.range vertex
  acyclic : matroid.IsAcyclic
  distinguished_mem_convexHull :
    matroid.MemConvexHull distinguished (Set.range vertex)

namespace Framework

variable (F : Framework I M)

/-- The distinguished basis is good. -/
theorem basis_isGoodBasis :
    F.matroid.IsGoodBasis F.distinguished (Set.range F.vertex) :=
  ⟨F.basis_isBasis, F.distinguished_mem_convexHull⟩

/-- The framework hypotheses force the distinguished basis to be nonempty. -/
theorem index_nonempty (F : Framework I M) : Nonempty I := by
  rcases (basis_isGoodBasis F).2 with hb | ⟨C, hC, hCpos, _⟩
  · exact (F.distinguished_notMem_basis hb).elim
  · obtain ⟨x, hx⟩ := F.acyclic.positive_nonempty hC
    obtain ⟨i, _⟩ := hCpos hx
    exact ⟨i⟩

/-- Every finite basis in the framework has the cardinality of the distinguished basis. -/
theorem card_eq_card_index_of_isBasis
    [Fintype I] [Finite M] [DecidableEq M] (X : Finset M)
    (hX : F.matroid.IsBasis (X : Set M)) :
    X.card = Fintype.card I := by
  have hXbase : F.matroid.underlying.IsBase (X : Set M) :=
    F.matroid.isBasis_iff_underlying_isBase.mp hX
  have hBbase : F.matroid.underlying.IsBase (Set.range F.vertex) :=
    F.matroid.isBasis_iff_underlying_isBase.mp F.basis_isBasis
  have hcard := hXbase.ncard_eq_ncard_of_isBase hBbase
  simpa [Set.ncard_range_of_injective F.vertex.injective] using hcard

/--
Nondegeneracy from Section 6: `b` is not in the convex hull of fewer than `|I|` elements of
`M \ {b}`.
-/
def IsNondegenerate [Fintype I] [DecidableEq M] : Prop :=
  ∀ X : Finset M,
    F.distinguished ∉ X → X.card < Fintype.card I →
      ¬ F.matroid.MemConvexHull F.distinguished (X : Set M)

/-- The basis obtained by replacing `v_i` with `w`. -/
def replaceBasis (i : I) (w : M) : Set M :=
  (Set.range F.vertex \ {F.vertex i}) ∪ {w}

/--
Lemma 6.1, with the implicit `X ⊆ M-b` condition made explicit as `b ∉ X`.  Without this
hypothesis the printed statement is false because convex hull membership includes membership.
-/
theorem not_memConvexHull_of_card_eq_of_not_isBasis
    [Fintype I] [Finite M] [DecidableEq M] (hnd : F.IsNondegenerate)
    (X : Finset M) (hXb : F.distinguished ∉ X)
    (hcard : X.card = Fintype.card I)
    (hnotBasis : ¬ F.matroid.IsBasis (X : Set M)) :
    ¬ F.matroid.MemConvexHull F.distinguished (X : Set M) := by
  intro hbX
  rcases hbX with hbX | ⟨τ, hτ, hτpos, hτneg⟩
  · exact hXb hbX
  have hbτneg : F.distinguished ∈ τ.negative := by
    rw [hτneg]
    simp
  have hτposfin : τ.positive.Finite := X.finite_toSet.subset hτpos
  let P : Finset M := hτposfin.toFinset
  have hbP : F.distinguished ∉ P := by
    intro hb
    have hbpos : F.distinguished ∈ τ.positive := by simpa [P] using hb
    exact Set.disjoint_left.1 τ.disjoint hbpos hbτneg
  have hτposlarge : Fintype.card I ≤ τ.positive.ncard := by
    by_contra hnot
    have hsmall : P.card < Fintype.card I := by
      change hτposfin.toFinset.card < Fintype.card I
      rw [← Set.ncard_eq_toFinset_card τ.positive hτposfin]
      exact Nat.lt_of_not_ge hnot
    apply hnd P hbP hsmall
    exact Or.inr ⟨τ, hτ, by simp [P], hτneg⟩
  have hXfin : ((X : Finset M) : Set M).Finite := X.finite_toSet
  have hXncard : ((X : Set M)).ncard = Fintype.card I := by
    simpa using hcard
  have hτposEq : τ.positive = (X : Set M) := by
    exact Set.eq_of_subset_of_ncard_le hτpos (by omega) hXfin
  have hnotIndependent : ¬ F.matroid.IsIndependent (X : Set M) := by
    intro hXind
    have hXindU := F.matroid.isIndependent_iff_underlying_indep.mp hXind
    obtain ⟨B', hB', hXB'⟩ := hXindU.exists_isBase_superset
    have hB₀ : F.matroid.underlying.IsBase (Set.range F.vertex) :=
      F.matroid.isBasis_iff_underlying_isBase.mp F.basis_isBasis
    have hB₀fin : (Set.range F.vertex).Finite := Set.finite_range F.vertex
    have hB'fin : B'.Finite := hB₀.finite_of_finite hB₀fin hB'
    have hB₀card : (Set.range F.vertex).ncard = Fintype.card I := by
      rw [Set.ncard_range_of_injective F.vertex.injective]
      simp
    have hB'card : B'.ncard = Fintype.card I := by
      rw [hB'.ncard_eq_ncard_of_isBase hB₀, hB₀card]
    have hXB'eq : (X : Set M) = B' :=
      Set.eq_of_subset_of_ncard_le hXB' (by omega) hB'fin
    apply hnotBasis
    apply F.matroid.isBasis_iff_underlying_isBase.mpr
    simpa [hXB'eq] using hB'
  simp only [OrientedMatroid.Data.IsIndependent, not_forall, not_not] at hnotIndependent
  obtain ⟨σ, hσ, hσsub⟩ := hnotIndependent
  have hσsubτ : σ.support ⊆ τ.support := by
    intro x hx
    exact Or.inl (hτposEq.symm ▸ hσsub hx)
  rcases F.matroid.eq_or_eq_neg_of_support_subset hσ hτ hσsubτ with hστ | hστ
  · have hbσ : F.distinguished ∈ σ.support := by
      rw [hστ]
      exact Or.inr hbτneg
    exact hXb (hσsub hbσ)
  · have hbσ : F.distinguished ∈ σ.support := by
      rw [hστ, SignedSubset.support_neg]
      exact Or.inr hbτneg
    exact hXb (hσsub hbσ)

/-- Lemma 6.2: unique good-basis pivot. -/
theorem existsUnique_goodBasis_replace
    [Fintype I] [Finite M] [DecidableEq M] (hnd : F.IsNondegenerate)
    {w : M} (hwB : w ∉ Set.range F.vertex) (hwb : w ≠ F.distinguished) :
    ∃! i : I,
      F.matroid.IsGoodBasis F.distinguished (F.replaceBasis i w) := by
  let B : Set M := Set.range F.vertex
  have hBfinite : B.Finite := Set.finite_range F.vertex
  have hBcard : B.ncard = Fintype.card I := by
    simp [B, Set.ncard_range_of_injective F.vertex.injective]
  obtain ⟨σ, hσ, hσpos, hσneg⟩ :
      ∃ σ : SignedSubset M, F.matroid.IsCircuit σ ∧
        σ.positive ⊆ B ∧ σ.negative = {F.distinguished} := by
    rcases F.distinguished_mem_convexHull with hbB | h
    · exact (F.distinguished_notMem_basis hbB).elim
    · simpa [B] using h
  have hσposfinite : σ.positive.Finite := hBfinite.subset hσpos
  have hσposEq : σ.positive = B := by
    have hlarge : Fintype.card I ≤ σ.positive.ncard := by
      by_contra hnot
      let P : Finset M := hσposfinite.toFinset
      have hbP : F.distinguished ∉ P := by
        intro hb
        have hbpos : F.distinguished ∈ σ.positive := by simpa [P] using hb
        have hbneg : F.distinguished ∈ σ.negative := by simp [hσneg]
        exact Set.disjoint_left.1 σ.disjoint hbpos hbneg
      have hsmall : P.card < Fintype.card I := by
        change hσposfinite.toFinset.card < Fintype.card I
        rw [← Set.ncard_eq_toFinset_card σ.positive hσposfinite]
        exact Nat.lt_of_not_ge hnot
      apply hnd P hbP hsmall
      exact Or.inr ⟨σ, hσ, by simp [P], hσneg⟩
    exact Set.eq_of_subset_of_ncard_le hσpos (by omega) hBfinite
  let U : Matroid M := F.matroid.underlying
  have hUB : U.IsBase B := by
    exact F.matroid.isBasis_iff_underlying_isBase.mp F.basis_isBasis
  have hwGround : w ∈ U.E := by
    rw [F.matroid.underlying_spec.1]
    trivial
  have hFund : U.IsCircuit (U.fundCircuit w B) :=
    hUB.fundCircuit_isCircuit hwGround hwB
  obtain ⟨τ₀, hτ₀, hτ₀support⟩ :=
    (F.matroid.underlying_spec.2 (U.fundCircuit w B)).mp hFund
  have hwτ₀ : w ∈ τ₀.support := by
    rw [hτ₀support]
    exact U.mem_fundCircuit w B
  have hτ₀sub : τ₀.support ⊆ insert w B := by
    rw [hτ₀support]
    exact U.fundCircuit_subset_insert w B
  obtain ⟨τ, hτ, hwτpos, hτsub⟩ :
      ∃ τ : SignedSubset M, F.matroid.IsCircuit τ ∧
        w ∈ τ.positive ∧ τ.support ⊆ insert w B := by
    rcases hwτ₀ with hwτ₀ | hwτ₀
    · exact ⟨τ₀, hτ₀, hwτ₀, hτ₀sub⟩
    · exact ⟨-τ₀, F.matroid.neg_isCircuit hτ₀, by simpa using hwτ₀, by simpa using hτ₀sub⟩
  obtain ⟨e, heτneg⟩ := F.acyclic hτ
  have heB : e ∈ B := by
    rcases hτsub (Or.inr heτneg) with hew | heB
    · subst e
      exact (Set.disjoint_left.1 τ.disjoint hwτpos heτneg).elim
    · exact heB
  have heσpos : e ∈ σ.positive := by simpa [hσposEq] using heB
  have heOpp : σ.OppositeAt τ e := Or.inl ⟨heσpos, heτneg⟩
  have hwσ : w ∉ σ.support := by
    intro hw
    rcases hw with hwσpos | hwσneg
    · exact hwB (hσpos hwσpos)
    · have : w = F.distinguished := by simpa [hσneg] using hwσneg
      exact hwb this
  have hτsubTodd : τ.support ⊆ σ.support ∪ {w} := by
    intro x hx
    rcases hτsub hx with hxw | hxB
    · exact Or.inr (by simp [hxw])
    · exact Or.inl (Or.inl (hσposEq.symm ▸ hxB))
  obtain ⟨ω, hω, hωcon, hωunique, hσω⟩ :=
    OrientedMatroid.todd_unique F.matroid hσ hτ ⟨Or.inl hwτpos, hwσ⟩
      ⟨e, ⟨Or.inl heσpos, Or.inr heτneg⟩, heOpp⟩ hτsubTodd
  have hωnegSub : ω.negative ⊆ {F.distinguished} := by
    intro x hx
    have hx' := hωcon.2.1 hx
    rcases hx'.1 with hxσ | hxτ
    · simpa [hσneg] using hxσ
    · have hxB : x ∈ B := by
        rcases hτsub (Or.inr hxτ) with hxw | hxB
        · subst x
          exact (Set.disjoint_left.1 τ.disjoint hwτpos hxτ).elim
        · exact hxB
      exact (hx'.2 (hσposEq.symm ▸ hxB)).elim
  have hωnegEq : ω.negative = {F.distinguished} := by
    apply Set.Subset.antisymm hωnegSub
    obtain ⟨x, hx⟩ := F.acyclic hω
    have hxb : x = F.distinguished := by simpa using hωnegSub hx
    simpa [← hxb] using hx
  have hωposSub : ω.positive ⊆ B ∪ {w} := by
    intro x hx
    rcases (hωcon.1 hx).1 with hxσ | hxτ
    · exact Or.inl (hσposEq ▸ hxσ)
    · rcases hτsub (Or.inl hxτ) with hxw | hxB
      · exact Or.inr (by simp [hxw])
      · exact Or.inl hxB
  have hwωpos : w ∈ ω.positive := by
    rcases hωcon.2.2.2 with hsame | hsame
    · exact hsame.1
    · exact (Set.disjoint_left.1 τ.disjoint hwτpos hsame.2).elim
  have hωposfinite : ω.positive.Finite :=
    (hBfinite.union (Set.finite_singleton w)).subset hωposSub
  have hωlarge : Fintype.card I ≤ ω.positive.ncard := by
    by_contra hnot
    let P : Finset M := hωposfinite.toFinset
    have hbP : F.distinguished ∉ P := by
      intro hb
      have hbpos : F.distinguished ∈ ω.positive := by simpa [P] using hb
      have hbneg : F.distinguished ∈ ω.negative := by simp [hωnegEq]
      exact Set.disjoint_left.1 ω.disjoint hbpos hbneg
    have hsmall : P.card < Fintype.card I := by
      change hωposfinite.toFinset.card < Fintype.card I
      rw [← Set.ncard_eq_toFinset_card ω.positive hωposfinite]
      exact Nat.lt_of_not_ge hnot
    apply hnd P hbP hsmall
    exact Or.inr ⟨ω, hω, by simp [P], hωnegEq⟩
  have hBnotSubω : ¬ B ⊆ ω.positive := by
    intro hBω
    have hσωsub : σ.support ⊆ ω.support := by
      intro x hx
      rcases hx with hxσ | hxσ
      · exact Or.inl (hBω (hσposEq ▸ hxσ))
      · exact Or.inr (hωnegEq.symm ▸ (hσneg ▸ hxσ))
    rcases F.matroid.eq_or_eq_neg_of_support_subset hσ hω hσωsub with hEq | hEq
    · exact hwσ (hEq ▸ Or.inl hwωpos)
    · exact hwσ (by rw [hEq, SignedSubset.support_neg]; exact Or.inl hwωpos)
  obtain ⟨x, hxB, hxω⟩ := Set.not_subset.1 hBnotSubω
  obtain ⟨i, rfl⟩ := hxB
  have hReplaceFinite (j : I) : (F.replaceBasis j w).Finite :=
    hBfinite.sdiff.union (Set.finite_singleton w)
  have hReplaceCard (j : I) : (F.replaceBasis j w).ncard = Fintype.card I := by
    have hvB : F.vertex j ∈ B := ⟨j, rfl⟩
    have hwDiff : w ∉ B \ {F.vertex j} := fun hw ↦ hwB hw.1
    change ((B \ {F.vertex j}) ∪ {w}).ncard = Fintype.card I
    rw [show (B \ {F.vertex j}) ∪ {w} = insert w (B \ {F.vertex j}) by
      ext y; simp]
    rw [Set.ncard_insert_of_notMem hwDiff, Set.ncard_sdiff_singleton_of_mem hvB, hBcard]
    have hcardpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨j⟩
    omega
  have hωposSubReplace : ω.positive ⊆ F.replaceBasis i w := by
    intro y hy
    rcases hωposSub hy with hyB | hyw
    · exact Or.inl ⟨hyB, fun hyi ↦ hxω (by simpa using hyi ▸ hy)⟩
    · exact Or.inr hyw
  have hωposEq : ω.positive = F.replaceBasis i w := by
    apply Set.eq_of_subset_of_ncard_le hωposSubReplace
    · rw [hReplaceCard]
      exact hωlarge
  have hGoodI : F.matroid.IsGoodBasis F.distinguished (F.replaceBasis i w) := by
    have hbReplace : F.distinguished ∉ F.replaceBasis i w := by
      rintro (hbB | hbw)
      · exact F.distinguished_notMem_basis hbB.1
      · exact hwb (by simpa using hbw.symm)
    have hconv : F.matroid.MemConvexHull F.distinguished (F.replaceBasis i w) :=
      Or.inr ⟨ω, hω, by simp [hωposEq], hωnegEq⟩
    refine ⟨?_, hconv⟩
    by_contra hnotBasis
    let X : Finset M := (hReplaceFinite i).toFinset
    have hXb : F.distinguished ∉ X := by simpa [X] using hbReplace
    have hXcard : X.card = Fintype.card I := by
      change (hReplaceFinite i).toFinset.card = Fintype.card I
      rw [← Set.ncard_eq_toFinset_card (F.replaceBasis i w) (hReplaceFinite i), hReplaceCard]
    exact (F.not_memConvexHull_of_card_eq_of_not_isBasis hnd X hXb hXcard
      (by simpa [X] using hnotBasis)) (by simpa [X] using hconv)
  refine ⟨i, hGoodI, ?_⟩
  intro j hGoodJ
  have hbReplaceJ : F.distinguished ∉ F.replaceBasis j w := by
    rintro (hbB | hbw)
    · exact F.distinguished_notMem_basis hbB.1
    · exact hwb (by simpa using hbw.symm)
  obtain ⟨W, hW, hWpos, hWneg⟩ :
      ∃ W : SignedSubset M, F.matroid.IsCircuit W ∧
        W.positive ⊆ F.replaceBasis j w ∧
          W.negative = {F.distinguished} := by
    rcases hGoodJ.2 with hb | hcir
    · exact (hbReplaceJ hb).elim
    · exact hcir
  have hWposfinite : W.positive.Finite := (hReplaceFinite j).subset hWpos
  have hWlarge : Fintype.card I ≤ W.positive.ncard := by
    by_contra hnot
    let P : Finset M := hWposfinite.toFinset
    have hbP : F.distinguished ∉ P := by
      intro hb
      have hbpos : F.distinguished ∈ W.positive := by simpa [P] using hb
      have hbneg : F.distinguished ∈ W.negative := by simp [hWneg]
      exact Set.disjoint_left.1 W.disjoint hbpos hbneg
    have hsmall : P.card < Fintype.card I := by
      change hWposfinite.toFinset.card < Fintype.card I
      rw [← Set.ncard_eq_toFinset_card W.positive hWposfinite]
      exact Nat.lt_of_not_ge hnot
    apply hnd P hbP hsmall
    exact Or.inr ⟨W, hW, by simp [P], hWneg⟩
  have hWposEq : W.positive = F.replaceBasis j w := by
    apply Set.eq_of_subset_of_ncard_le hWpos
    · rw [hReplaceCard]
      exact hWlarge
  have hwWpos : w ∈ W.positive := by
    rw [hWposEq]
    exact Or.inr (Set.mem_singleton w)
  have hWcon : OrientedMatroid.ToddConclusion W σ τ w := by
    refine ⟨?_, ?_, Or.inl hwWpos, Or.inl ⟨hwWpos, hwτpos⟩⟩
    · intro y hy
      rw [hWposEq] at hy
      refine ⟨?_, ?_⟩
      · rcases hy with hyB | hyw
        · exact Or.inl (hσposEq.symm ▸ hyB.1)
        · have hyEq : y = w := by simpa using hyw
          subst y
          exact Or.inr hwτpos
      · intro hyσneg
        have hyb : y = F.distinguished := by simpa [hσneg] using hyσneg
        subst y
        exact hbReplaceJ (hWposEq.symm ▸ hy)
    · intro y hy
      have hyb : y = F.distinguished := by simpa [hWneg] using hy
      subst y
      refine ⟨Or.inl (by simp [hσneg]), ?_⟩
      intro hbσpos
      exact F.distinguished_notMem_basis (hσpos hbσpos)
  have hWω : W = ω := hωunique W hW hWcon
  have hReplaceEq : F.replaceBasis j w = F.replaceBasis i w := by
    rw [← hWposEq, hWω, hωposEq]
  by_contra hji
  have hvne : F.vertex i ≠ F.vertex j := fun h ↦ hji (F.vertex.injective h).symm
  have hviJ : F.vertex i ∈ F.replaceBasis j w :=
    Or.inl ⟨⟨i, rfl⟩, by simpa using hvne⟩
  have hviI : F.vertex i ∈ F.replaceBasis i w := hReplaceEq.symm ▸ hviJ
  rcases hviI with hviI | hviw
  · exact hviI.2 rfl
  · exact hwB ⟨i, by simpa using hviw⟩

/-- Formula used in Lemma 6.3. -/
def replacementIsGood [DecidableEq M]
    (i : I) (D : Finset M) (d : M) : Prop :=
  d ∈ D ∧
    F.matroid.IsGoodBasis F.distinguished
      ((insert (F.vertex i) (D.erase d) : Finset M) : Set M)

/-- A good basis has exactly one good replacement by a distinguished-basis element. -/
theorem card_goodReplacements_eq_one_of_goodBasis
    [Fintype I] [Fintype M] [DecidableEq M] (hnd : F.IsNondegenerate)
    (i : I) (D : Finset M) (hbD : F.distinguished ∉ D)
    (hD : F.matroid.IsGoodBasis F.distinguished (D : Set M)) :
    (Finset.univ.filter fun d ↦ F.replacementIsGood i D d).card = 1 := by
  classical
  have hDcard : D.card = Fintype.card I :=
    F.card_eq_card_index_of_isBasis D hD.1
  by_cases hviD : F.vertex i ∈ D
  · have hfilter :
        Finset.univ.filter (fun d ↦ F.replacementIsGood i D d) = {F.vertex i} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hdD, hdGood⟩
        by_contra hdne
        have hEq : insert (F.vertex i) (D.erase d) = D.erase d := by
          apply Finset.insert_eq_self.mpr
          simp [hviD, Ne.symm hdne]
        have hcardBasis :=
          F.card_eq_card_index_of_isBasis (insert (F.vertex i) (D.erase d)) hdGood.1
        rw [hEq, Finset.card_erase_of_mem hdD, hDcard] at hcardBasis
        have hcardpos : 0 < Fintype.card I := by
          rw [← hDcard]
          exact Finset.card_pos.mpr ⟨d, hdD⟩
        omega
      · intro hdi
        subst d
        refine ⟨hviD, ?_⟩
        have hEq : insert (F.vertex i) (D.erase (F.vertex i)) = D := by
          exact Finset.insert_erase hviD
        simpa [hEq] using hD
    rw [hfilter]
    simp
  · let equiv : I ≃ D := Fintype.equivOfCardEq (by simpa using hDcard.symm)
    let vertex' : I ↪ M := equiv.toEmbedding.trans (Function.Embedding.subtype _)
    have hrangeVertex' : Set.range vertex' = (D : Set M) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (equiv j).property
      · intro hx
        obtain ⟨j, hj⟩ := equiv.surjective ⟨x, hx⟩
        exact ⟨j, congrArg Subtype.val hj⟩
    let F' : Framework I M := {
      matroid := F.matroid
      vertex := vertex'
      distinguished := F.distinguished
      basis_isBasis := by simpa [hrangeVertex'] using hD.1
      distinguished_notMem_basis := by simpa [hrangeVertex'] using hbD
      acyclic := F.acyclic
      distinguished_mem_convexHull := by simpa [hrangeVertex'] using hD.2 }
    have hnd' : F'.IsNondegenerate := by
      intro X hbX hcard
      exact hnd X hbX hcard
    have hviRange : F.vertex i ∉ Set.range F'.vertex := by
      simpa [F', hrangeVertex'] using hviD
    have hvib : F.vertex i ≠ F.distinguished := by
      intro h
      exact F.distinguished_notMem_basis ⟨i, h⟩
    obtain ⟨j, hjGood, hjUnique⟩ :=
      F'.existsUnique_goodBasis_replace hnd' hviRange hvib
    let d : M := F'.vertex j
    have hdD : d ∈ D := by
      change F'.vertex j ∈ (D : Set M)
      rw [← hrangeVertex']
      exact ⟨j, rfl⟩
    have hreplace (k : I) :
        F'.replaceBasis k (F.vertex i) =
          ((insert (F.vertex i) (D.erase (F'.vertex k)) : Finset M) : Set M) := by
      rw [Framework.replaceBasis, hrangeVertex']
      ext x
      simp
    have hdGood : F.replacementIsGood i D d := by
      refine ⟨hdD, ?_⟩
      simpa [F', d, ← hreplace j] using hjGood
    have hfilter :
        Finset.univ.filter (fun x ↦ F.replacementIsGood i D x) = {d} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro hxGood
        obtain ⟨k, hk⟩ := (Set.ext_iff.mp hrangeVertex' x).mpr hxGood.1
        have hkGood : F'.matroid.IsGoodBasis F'.distinguished
            (F'.replaceBasis k (F.vertex i)) := by
          simpa [F', hreplace k, hk] using hxGood.2
        have hkj : k = j := hjUnique k hkGood
        calc
          x = F'.vertex k := hk.symm
          _ = F'.vertex j := by rw [hkj]
          _ = d := rfl
      · intro hxd
        simpa [hxd] using hdGood
    rw [hfilter]
    simp

/-- Lemma 6.3: the number of good replacements is zero or two. -/
theorem card_goodReplacements_eq_zero_or_two
    [Fintype I] [Fintype M] [DecidableEq M] (hnd : F.IsNondegenerate)
    (i : I) (D : Finset M) (hDcard : D.card = Fintype.card I)
    (hD : ¬ F.matroid.MemConvexHull F.distinguished (D : Set M)) :
    (Finset.univ.filter fun d ↦ F.replacementIsGood i D d).card = 0 ∨
      (Finset.univ.filter fun d ↦ F.replacementIsGood i D d).card = 2 := by
  classical
  let S : Finset M := Finset.univ.filter fun d ↦ F.replacementIsGood i D d
  by_cases hS : S = ∅
  · exact Or.inl (by simp [S, hS])
  · right
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨d, hdS⟩ := hSne
    have hdRep : F.replacementIsGood i D d := by simpa [S] using hdS
    have hdD : d ∈ D := hdRep.1
    let B' : Finset M := insert (F.vertex i) (D.erase d)
    have hB'good : F.matroid.IsGoodBasis F.distinguished (B' : Set M) := by
      simpa [B'] using hdRep.2
    have hbD : F.distinguished ∉ D := by
      intro hb
      exact hD (F.matroid.memConvexHull_of_mem hb)
    have hdb : d ≠ F.distinguished := by
      intro hdb
      exact hbD (hdb ▸ hdD)
    have hdvi : d ≠ F.vertex i := by
      intro hdvi
      subst d
      apply hD
      have hB'D : (B' : Set M) = (D : Set M) := by
        ext x
        simp [B', hdD]
      simpa [hB'D] using hB'good.2
    have hB'baseU : F.matroid.underlying.IsBase (B' : Set M) :=
      F.matroid.isBasis_iff_underlying_isBase.mp hB'good.1
    have hBbaseU : F.matroid.underlying.IsBase (Set.range F.vertex) :=
      F.matroid.isBasis_iff_underlying_isBase.mp F.basis_isBasis
    have hB'cardSet : ((B' : Finset M) : Set M).ncard = Fintype.card I := by
      rw [hB'baseU.ncard_eq_ncard_of_isBase hBbaseU]
      simp [Set.ncard_range_of_injective F.vertex.injective]
    have hB'card : B'.card = Fintype.card I := by simpa using hB'cardSet
    have hviD : F.vertex i ∉ D := by
      intro hviD
      have hB'eq : B' = D.erase d := by
        ext x
        simp [B', hviD, Ne.symm hdvi]
      have hcardpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
      rw [hB'eq, Finset.card_erase_of_mem hdD, hDcard] at hB'card
      omega
    let equiv : I ≃ B' := Fintype.equivOfCardEq (by simpa using hB'card.symm)
    let vertex' : I ↪ M := equiv.toEmbedding.trans (Function.Embedding.subtype _)
    have hrangeVertex' : Set.range vertex' = (B' : Set M) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (equiv j).property
      · intro hx
        obtain ⟨j, hj⟩ := equiv.surjective ⟨x, hx⟩
        exact ⟨j, congrArg Subtype.val hj⟩
    have hbB' : F.distinguished ∉ (B' : Set M) := by
      intro hb
      simp only [B', Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff,
        Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hb
      rcases hb with hbvi | hbD'
      · exact F.distinguished_notMem_basis ⟨i, hbvi.symm⟩
      · exact hbD hbD'.1
    let F' : Framework I M := {
      matroid := F.matroid
      vertex := vertex'
      distinguished := F.distinguished
      basis_isBasis := by simpa [hrangeVertex'] using hB'good.1
      distinguished_notMem_basis := by simpa [hrangeVertex'] using hbB'
      acyclic := F.acyclic
      distinguished_mem_convexHull := by simpa [hrangeVertex'] using hB'good.2 }
    have hnd' : F'.IsNondegenerate := by
      intro X hbX hcard
      exact hnd X hbX hcard
    have hdB' : d ∉ (B' : Set M) := by
      simp [B', hdvi, hdD]
    have hdRangeF' : d ∉ Set.range F'.vertex := by
      simpa [F', hrangeVertex'] using hdB'
    obtain ⟨k, hkGood, hkUnique⟩ :=
      F'.existsUnique_goodBasis_replace hnd' hdRangeF' hdb
    let e : M := F'.vertex k
    have heB' : e ∈ (B' : Set M) := by
      rw [← hrangeVertex']
      exact ⟨k, rfl⟩
    have hF'replace : F'.replaceBasis k d = ((B' : Set M) \ {e}) ∪ {d} := by
      rw [Framework.replaceBasis]
      simp only [e]
      rw [hrangeVertex']
    have hevi : e ≠ F.vertex i := by
      intro hevi
      apply hD
      have hEq : F'.replaceBasis k d = (D : Set M) := by
        rw [hF'replace, hevi]
        ext x
        simp [B', hdD, hviD]
      simpa [hEq] using hkGood.2
    have heD : e ∈ D := by
      simp only [B', Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff,
        Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at heB'
      exact (heB'.resolve_left hevi).1
    have hed : e ≠ d := by
      simp only [B', Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff,
        Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at heB'
      exact (heB'.resolve_left hevi).2
    have hExchangeEq : F'.replaceBasis k d =
        ((insert (F.vertex i) (D.erase e) : Finset M) : Set M) := by
      rw [hF'replace]
      ext y
      simp only [B', Finset.coe_insert, Finset.coe_erase, Set.mem_union,
        Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
      change (((y = F.vertex i ∨ (y ∈ D ∧ y ≠ d)) ∧ y ≠ e) ∨ y = d) ↔
        (y = F.vertex i ∨ (y ∈ D ∧ y ≠ e))
      constructor
      · rintro (⟨hyi | ⟨hyD, hyd⟩, hye⟩ | rfl)
        · exact Or.inl hyi
        · exact Or.inr ⟨hyD, hye⟩
        · exact Or.inr ⟨hdD, Ne.symm hed⟩
      · rintro (hyi | ⟨hyD, hye⟩)
        · refine Or.inl ⟨Or.inl hyi, ?_⟩
          intro hyeq
          exact hevi (hyeq.symm.trans hyi)
        · by_cases hyd : y = d
          · exact Or.inr hyd
          · exact Or.inl ⟨Or.inr ⟨hyD, hyd⟩, hye⟩
    have heRep : F.replacementIsGood i D e := by
      refine ⟨heD, ?_⟩
      simpa [hExchangeEq] using hkGood
    have heS : e ∈ S := by simpa [S] using heRep
    have hde : d ≠ e := Ne.symm hed
    have hOnly : ∀ x ∈ S, x = d ∨ x = e := by
      intro x hxS
      have hxRep : F.replacementIsGood i D x := by simpa [S] using hxS
      by_cases hxd : x = d
      · exact Or.inl hxd
      · right
        have hxD : x ∈ D := hxRep.1
        have hxvi : x ≠ F.vertex i := by
          intro hxvi
          subst x
          exact hviD hxD
        have hxB' : x ∈ (B' : Set M) := by
          simp [B', hxvi, hxD, hxd]
        obtain ⟨l, hl⟩ := (Set.ext_iff.mp hrangeVertex' x).mpr hxB'
        have hGoodL : F'.matroid.IsGoodBasis F'.distinguished
            (F'.replaceBasis l d) := by
          have hEq : F'.replaceBasis l d =
              ((insert (F.vertex i) (D.erase x) : Finset M) : Set M) := by
            rw [Framework.replaceBasis, hrangeVertex']
            have hl' : F'.vertex l = x := hl
            rw [hl']
            ext y
            simp only [B', Finset.coe_insert, Finset.coe_erase, Set.mem_union,
              Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
            change (((y = F.vertex i ∨ (y ∈ D ∧ y ≠ d)) ∧ y ≠ x) ∨ y = d) ↔
              (y = F.vertex i ∨ (y ∈ D ∧ y ≠ x))
            constructor
            · rintro (⟨hyi | ⟨hyD, hyd⟩, hyx⟩ | rfl)
              · exact Or.inl hyi
              · exact Or.inr ⟨hyD, hyx⟩
              · exact Or.inr ⟨hdD, Ne.symm hxd⟩
            · rintro (hyi | ⟨hyD, hyx⟩)
              · refine Or.inl ⟨Or.inl hyi, ?_⟩
                intro hyxeq
                exact hxvi (hyxeq.symm.trans hyi)
              · by_cases hyd : y = d
                · exact Or.inr hyd
                · exact Or.inl ⟨Or.inr ⟨hyD, hyd⟩, hyx⟩
          simpa [F', hEq] using hxRep.2
        have hlk : l = k := hkUnique l hGoodL
        calc
          x = F'.vertex l := hl.symm
          _ = F'.vertex k := by rw [hlk]
          _ = e := rfl
    have hSeq : S = {d, e} := by
      ext x
      constructor
      · intro hx
        rcases hOnly x hx with rfl | rfl <;> simp
      · intro hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hdS
        · exact heS
    rw [show (Finset.univ.filter fun d ↦ F.replacementIsGood i D d) = S by rfl, hSeq]
    simp [hde]

private theorem image_erase_eq_erase_image_of_injOn
    {X : Type*} [DecidableEq X] [DecidableEq M]
    (g : X → M) (S : Finset X) (hginj : Set.InjOn g (S : Set X))
    {x : X} (hx : x ∈ S) :
    (S.erase x).image g = (S.image g).erase (g x) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzx : z ≠ x := by simpa using (Finset.mem_erase.mp hz).1
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨z, (Finset.mem_erase.mp hz).2, rfl⟩⟩
    intro h
    exact hzx (hginj (Finset.mem_erase.mp hz).2 hx h)
  · intro hy
    obtain ⟨hyne, z, hzS, hzy⟩ := Finset.mem_erase.mp hy |>.imp_right Finset.mem_image.mp
    have hzx : z ≠ x := by
      intro hzx
      subst z
      exact hyne hzy.symm
    exact Finset.mem_image.mpr ⟨z, Finset.mem_erase.mpr ⟨hzx, hzS⟩, hzy⟩

/-- Lemma 6.4: the local F₂ boundary evaluation for a colored top simplex. -/
theorem boundary_goodBasis_parity
    {X : Type*} [DecidableEq X] [Fintype I] [Fintype M] [DecidableEq M]
    (hnd : F.IsNondegenerate) (i : I) (S : Finset X)
    (hScard : S.card = Fintype.card I) (g : X → M)
    (hgb : ∀ x ∈ S, g x ≠ F.distinguished) :
    (∑ x ∈ S,
        if F.matroid.IsGoodBasis F.distinguished
            (insert (F.vertex i) ((S.erase x).image g) : Set M)
        then (1 : ZMod 2) else 0) =
      if F.matroid.IsGoodBasis F.distinguished (S.image g : Set M)
      then 1 else 0 := by
  classical
  let P : X → Prop := fun x ↦
    F.matroid.IsGoodBasis F.distinguished
      (insert (F.vertex i) ((S.erase x).image g) : Set M)
  let T : Finset X := S.filter P
  let D : Finset M := S.image g
  have hbD : F.distinguished ∉ D := by
    intro hb
    obtain ⟨x, hxS, hxb⟩ := Finset.mem_image.mp hb
    exact hgb x hxS hxb
  have hDle : D.card ≤ Fintype.card I := by
    calc
      D.card ≤ S.card := Finset.card_image_le
      _ = Fintype.card I := hScard
  have hsum :
      (∑ x ∈ S,
          if F.matroid.IsGoodBasis F.distinguished
              (insert (F.vertex i) ((S.erase x).image g) : Set M)
          then (1 : ZMod 2) else 0) = (T.card : ZMod 2) := by
    simp [T, P, Finset.sum_boole]
  rw [hsum]
  by_cases hDcard : D.card = Fintype.card I
  · have hginj : Set.InjOn g (S : Set X) := by
      apply Finset.card_image_iff.mp
      simpa [D, hScard] using hDcard
    have himageT : T.image g =
        Finset.univ.filter (fun d ↦ F.replacementIsGood i D d) := by
      ext d
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, hxT, rfl⟩
        have hxS : x ∈ S := (Finset.mem_filter.mp hxT).1
        have hxP : P x := (Finset.mem_filter.mp hxT).2
        refine ⟨Finset.mem_image.mpr ⟨x, hxS, rfl⟩, ?_⟩
        dsimp [P] at hxP
        rw [image_erase_eq_erase_image_of_injOn g S hginj hxS] at hxP
        simpa only [D, Finset.coe_insert] using hxP
      · rintro ⟨hdD, hdGood⟩
        obtain ⟨x, hxS, hxd⟩ := Finset.mem_image.mp (show d ∈ S.image g from hdD)
        refine ⟨x, ?_, hxd⟩
        apply Finset.mem_filter.mpr
        refine ⟨hxS, ?_⟩
        dsimp [P]
        rw [image_erase_eq_erase_image_of_injOn g S hginj hxS]
        simpa only [D, hxd, Finset.coe_insert] using hdGood
    have hTcard : T.card =
        (Finset.univ.filter (fun d ↦ F.replacementIsGood i D d)).card := by
      rw [← himageT]
      exact (Finset.card_image_of_injOn (hginj.mono (Finset.filter_subset _ _))).symm
    rw [hTcard]
    by_cases hDgood : F.matroid.IsGoodBasis F.distinguished (D : Set M)
    · rw [F.card_goodReplacements_eq_one_of_goodBasis hnd i D hbD hDgood]
      have hDgood' : F.matroid.IsGoodBasis F.distinguished (S.image g : Set M) := by
        simpa only [D] using hDgood
      rw [if_pos hDgood']
      simp
    · have hDconv : ¬ F.matroid.MemConvexHull F.distinguished (D : Set M) := by
        intro hconv
        apply hDgood
        refine ⟨?_, hconv⟩
        by_contra hnotBasis
        exact (F.not_memConvexHull_of_card_eq_of_not_isBasis hnd D hbD hDcard hnotBasis) hconv
      rcases F.card_goodReplacements_eq_zero_or_two hnd i D hDcard hDconv with hzero | htwo
      · rw [hzero]
        have hDgood' : ¬ F.matroid.IsGoodBasis F.distinguished (S.image g : Set M) := by
          simpa only [D] using hDgood
        rw [if_neg hDgood']
        exact CharTwo.two_eq_zero
      · rw [htwo]
        have hDgood' : ¬ F.matroid.IsGoodBasis F.distinguished (S.image g : Set M) := by
          simpa only [D] using hDgood
        rw [if_neg hDgood']
        exact CharTwo.two_eq_zero
  · have hDlt : D.card < Fintype.card I := Nat.lt_of_le_of_ne hDle hDcard
    have hDnotGood : ¬ F.matroid.IsGoodBasis F.distinguished (D : Set M) := by
      intro hGood
      have := F.card_eq_card_index_of_isBasis D hGood.1
      omega
    have hTcard : T.card = 0 ∨ T.card = 2 := by
      by_cases hTempty : T = ∅
      · exact Or.inl (by simp [hTempty])
      · right
        obtain ⟨x, hxT⟩ := Finset.nonempty_iff_ne_empty.mpr hTempty
        have hxS : x ∈ S := (Finset.mem_filter.mp hxT).1
        have hxP : P x := (Finset.mem_filter.mp hxT).2
        have duplicate_of_mem : ∀ {z : X}, z ∈ T →
            ∃ w ∈ S, w ≠ z ∧ g w = g z := by
          intro z hzT
          have hzS : z ∈ S := (Finset.mem_filter.mp hzT).1
          have hzP : P z := (Finset.mem_filter.mp hzT).2
          let E : Finset M := (S.erase z).image g
          have hQcard : (insert (F.vertex i) E).card = Fintype.card I := by
            apply F.card_eq_card_index_of_isBasis
            simpa [P, E] using hzP.1
          have hEcard : E.card + 1 = Fintype.card I := by
            have hEle : E.card ≤ (S.erase z).card := Finset.card_image_le
            have hErase : (S.erase z).card + 1 = Fintype.card I := by
              rw [Finset.card_erase_of_mem hzS, hScard]
              have hpos : 0 < Fintype.card I := by
                rw [← hScard]
                exact Finset.card_pos.mpr ⟨z, hzS⟩
              omega
            have hQle : (insert (F.vertex i) E).card ≤ E.card + 1 :=
              Finset.card_insert_le _ _
            omega
          have hDinsert : D = insert (g z) E := by
            dsimp [D, E]
            rw [← Finset.image_insert]
            exact congrArg (Finset.image g) (Finset.insert_erase hzS).symm
          have hgzE : g z ∈ E := by
            by_contra hgzE
            have hcardInsert := Finset.card_insert_of_notMem hgzE
            rw [← hDinsert, hEcard] at hcardInsert
            omega
          obtain ⟨w, hwErase, hwg⟩ := Finset.mem_image.mp hgzE
          exact ⟨w, (Finset.mem_erase.mp hwErase).2,
            (Finset.mem_erase.mp hwErase).1, hwg⟩
        obtain ⟨y, hyS, hyx, hyg⟩ := duplicate_of_mem hxT
        have hEraseImageEq : (S.erase y).image g = (S.erase x).image g := by
          ext d
          constructor
          · intro hd
            obtain ⟨z, hzErase, hzd⟩ := Finset.mem_image.mp hd
            have hzS := (Finset.mem_erase.mp hzErase).2
            by_cases hzx : z = x
            · subst z
              exact Finset.mem_image.mpr
                ⟨y, Finset.mem_erase.mpr ⟨hyx, hyS⟩, hyg.trans hzd⟩
            · exact Finset.mem_image.mpr ⟨z, Finset.mem_erase.mpr ⟨hzx, hzS⟩, hzd⟩
          · intro hd
            obtain ⟨z, hzErase, hzd⟩ := Finset.mem_image.mp hd
            have hzS := (Finset.mem_erase.mp hzErase).2
            by_cases hzy : z = y
            · subst z
              exact Finset.mem_image.mpr
                ⟨x, Finset.mem_erase.mpr ⟨Ne.symm hyx, hxS⟩, hyg.symm.trans hzd⟩
            · exact Finset.mem_image.mpr ⟨z, Finset.mem_erase.mpr ⟨hzy, hzS⟩, hzd⟩
        have hyT : y ∈ T := by
          apply Finset.mem_filter.mpr
          refine ⟨hyS, ?_⟩
          dsimp [P] at hxP ⊢
          rw [hEraseImageEq]
          exact hxP
        have hEraseCard : ((S.erase x).image g).card = (S.erase x).card := by
          let E : Finset M := (S.erase x).image g
          have hQcard : (insert (F.vertex i) E).card = Fintype.card I := by
            apply F.card_eq_card_index_of_isBasis
            simpa [P, E] using hxP.1
          have hEle : E.card ≤ (S.erase x).card := Finset.card_image_le
          have hErase : (S.erase x).card + 1 = Fintype.card I := by
            rw [Finset.card_erase_of_mem hxS, hScard]
            have hpos : 0 < Fintype.card I := by
              rw [← hScard]
              exact Finset.card_pos.mpr ⟨x, hxS⟩
            omega
          have hQle : (insert (F.vertex i) E).card ≤ E.card + 1 :=
            Finset.card_insert_le _ _
          dsimp [E] at hQcard hEle hQle ⊢
          omega
        have hginjErase : Set.InjOn g ((S.erase x : Finset X) : Set X) :=
          Finset.card_image_iff.mp hEraseCard
        have hOnly : ∀ z ∈ T, z = x ∨ z = y := by
          intro z hzT
          by_cases hzx : z = x
          · exact Or.inl hzx
          · right
            obtain ⟨w, hwS, hwz, hwg⟩ := duplicate_of_mem hzT
            have hzErase : z ∈ S.erase x := Finset.mem_erase.mpr ⟨hzx, (Finset.mem_filter.mp hzT).1⟩
            by_cases hwx : w = x
            · subst w
              exact hginjErase hzErase (Finset.mem_erase.mpr ⟨hyx, hyS⟩)
                (hwg.symm.trans hyg.symm)
            · have hwErase : w ∈ S.erase x := Finset.mem_erase.mpr ⟨hwx, hwS⟩
              exact (hwz (hginjErase hwErase hzErase hwg)).elim
        have hTeq : T = {x, y} := by
          ext z
          constructor
          · intro hz
            rcases hOnly z hz with rfl | rfl <;> simp
          · intro hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hxT
            · exact hyT
        rw [hTeq]
        simp [Ne.symm hyx]
    rcases hTcard with hzero | htwo
    · rw [hzero]
      have hDnotGood' : ¬ F.matroid.IsGoodBasis F.distinguished (S.image g : Set M) := by
        simpa only [D] using hDnotGood
      rw [if_neg hDnotGood']
      exact CharTwo.two_eq_zero
    · rw [htwo]
      have hDnotGood' : ¬ F.matroid.IsGoodBasis F.distinguished (S.image g : Set M) := by
        simpa only [D] using hDnotGood
      rw [if_neg hDnotGood']
      exact CharTwo.two_eq_zero

end Framework

section Coloring

variable [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  [DecidableEq M]

/-- A matroid coloring `c : V_D → M-b`. -/
abbrev Coloring (D : SimplexFamily I V) (F : Framework I M) :=
  D.Vertex → {m : M // m ≠ F.distinguished}

/-- Extend a coloring to the envelope by coloring the formal vertex `i` with `v_i`. -/
noncomputable def envelopeColor (D : SimplexFamily I V) (F : Framework I M)
    (c : Coloring D F) : V ⊕ I → M :=
  Sum.elim
    (fun v ↦ if hv : v ∈ D.vertexSet then (c ⟨v, hv⟩).1 else F.distinguished)
    F.vertex

omit [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq M] in @[simp]
theorem envelopeColor_inl_of_mem (D : SimplexFamily I V) (F : Framework I M)
    (c : Coloring D F) {v : V} (hv : v ∈ D.vertexSet) :
    envelopeColor D F c (Sum.inl v) = (c ⟨v, hv⟩).1 := by
  simp [envelopeColor, hv]

omit [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq M] in @[simp]
theorem envelopeColor_inr (D : SimplexFamily I V) (F : Framework I M)
    (c : Coloring D F) (i : I) :
    envelopeColor D F c (Sum.inr i) = F.vertex i := by
  simp [envelopeColor]

omit [Fintype I] [Fintype V] [DecidableEq I] in
/-- Every vertex of a simplex of `D(A)` belongs to the universal vertex set `V_D`. -/
theorem mem_vertexSet_of_mem_simplex (D : SimplexFamily I V)
    {A : Finset I} {σ : Finset V} (hσ : σ ∈ D.complex A)
    {v : V} (hv : v ∈ σ) : v ∈ D.vertexSet := by
  refine ⟨A, ?_⟩
  exact D.complex A |>.downward_closed hσ (by simpa using hv)

/-- Image of a simplex under a coloring. -/
def colorImage (D : SimplexFamily I V) (F : Framework I M)
    (c : Coloring D F) {A : Finset I} (σ : Finset V)
    (hσ : σ ∈ D.complex A) : Finset M :=
  σ.attach.image fun v ↦
    (c ⟨v.1, mem_vertexSet_of_mem_simplex D hσ v.2⟩).1

/-- Formula (33): `c(τ) ∪ {v_i | i ∈ I\C}`. -/
def completedImage (D : SimplexFamily I V) (F : Framework I M)
    (c : Coloring D F) (C : Finset I) (τ : Finset V)
    (hτ : τ ∈ D.complex C) : Finset M :=
  colorImage D F c τ hτ ∪ (Finset.univ \ C).image F.vertex

omit [Fintype V] in theorem envelopeColor_image_cell (D : SimplexFamily I V) (F : Framework I M)
    (c : Coloring D F) (C : Finset I) (τ : Finset V)
    (hτ : τ ∈ D.complex C) :
    (Envelope.oldSimplex τ ∪ Envelope.indexSimplex (Finset.univ \ C)).image
        (envelopeColor D F c) = completedImage D F c C τ hτ := by
  ext m
  simp only [Envelope.oldSimplex, Envelope.indexSimplex, completedImage, colorImage,
    Finset.image_union, Finset.image_image, Finset.mem_union, Finset.mem_image,
    Finset.mem_attach, true_and, Function.comp_apply, Subtype.exists,
    envelopeColor, Sum.elim_inl, Sum.elim_inr, Finset.mem_sdiff, Finset.mem_univ]
  constructor
  · rintro (h | h)
    · left
      obtain ⟨a, ha, ham⟩ := h
      have hva := mem_vertexSet_of_mem_simplex D hτ ha
      simp [hva] at ham
      exact ⟨a, ha, ham⟩
    · exact Or.inr h
  · rintro (h | h)
    · left
      obtain ⟨a, ha, ham⟩ := h
      refine ⟨a, ha, ?_⟩
      have hva := mem_vertexSet_of_mem_simplex D hτ ha
      simpa [hva] using ham
    · exact Or.inr h

private theorem envelope_boundary_cochain_eval
    [Fintype M] [Nonempty I] (D : SimplexFamily I V) (F : Framework I M)
    (c : Coloring D F) (i : I) :
    SimplexFamily.cochainEval
        (fun ρ ↦ if F.matroid.IsGoodBasis F.distinguished
          (insert (F.vertex i) (ρ.image (envelopeColor D F c)) : Set M)
          then 1 else 0)
        ((Envelope.family D).boundaryIndexChain (Finset.univ : Finset I)) = 1 := by
  classical
  let φ : Finset (V ⊕ I) → ZMod 2 := fun ρ ↦
    if F.matroid.IsGoodBasis F.distinguished
      (insert (F.vertex i) (ρ.image (envelopeColor D F c)) : Set M)
    then 1 else 0
  have hboundary (B : Finset I)
      (hB : B ∈ SimplexFamily.boundaryIndices (Finset.univ : Finset I)) :
      B ⊆ Finset.univ ∧ B.card + 1 = Fintype.card I := by
    have h := Finset.mem_filter.mp hB
    exact ⟨Finset.mem_powerset.mp h.1, by simpa using h.2⟩
  have hgood_iff (B : Finset I)
      (hB : B ∈ SimplexFamily.boundaryIndices (Finset.univ : Finset I)) :
      F.matroid.IsGoodBasis F.distinguished
          (insert (F.vertex i)
            ((Envelope.indexSimplex (V := V) B).image (envelopeColor D F c)) : Set M) ↔
        i ∉ B := by
    have hBdata := hboundary B hB
    have himage :
        (Envelope.indexSimplex (V := V) B).image (envelopeColor D F c) =
          B.image F.vertex := by
      ext m
      simp [Envelope.indexSimplex, envelopeColor]
    rw [himage]
    constructor
    · intro hgood hiB
      have hviImage : F.vertex i ∈ B.image F.vertex :=
        Finset.mem_image.mpr ⟨i, hiB, rfl⟩
      have hEq : insert (F.vertex i) (B.image F.vertex) = B.image F.vertex :=
        Finset.insert_eq_self.mpr hviImage
      have hgood' : F.matroid.IsGoodBasis F.distinguished
          ((insert (F.vertex i) (B.image F.vertex) : Finset M) : Set M) := by
        simpa only [Finset.coe_insert] using hgood
      have hcard :=
        F.card_eq_card_index_of_isBasis (insert (F.vertex i) (B.image F.vertex)) hgood'.1
      rw [hEq, Finset.card_image_of_injective _ F.vertex.injective] at hcard
      omega
    · intro hiB
      have hsub : B ⊆ Finset.univ.erase i := by
        intro j hj
        exact Finset.mem_erase.mpr ⟨fun hji ↦ hiB (hji ▸ hj), Finset.mem_univ j⟩
      have heraseCard : (Finset.univ.erase i : Finset I).card + 1 = Fintype.card I := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
        have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
        omega
      have hBeq : B = Finset.univ.erase i :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      have hcolorEq :
          insert (F.vertex i) (B.image F.vertex) = Finset.univ.image F.vertex := by
        subst B
        rw [Finset.image_erase F.vertex.injective]
        exact Finset.insert_erase
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have hgoodFull : F.matroid.IsGoodBasis F.distinguished
          (Finset.univ.image F.vertex : Set M) := by
        simpa [Finset.coe_image] using F.basis_isGoodBasis
      rw [← hcolorEq] at hgoodFull
      simpa only [Finset.coe_insert] using hgoodFull
  have hinner (B : Finset I)
      (hB : B ∈ SimplexFamily.boundaryIndices (Finset.univ : Finset I)) :
      (∑ σ ∈ ((Envelope.family D).complex B).topSimplices B.card, φ σ) =
        if i ∉ B then 1 else 0 := by
    have hBne : B ≠ Finset.univ := by
      intro h
      have hcard := (hboundary B hB).2
      rw [h, Finset.card_univ] at hcard
      omega
    change (∑ σ ∈ (Envelope.complex D B).topSimplices B.card, φ σ) = _
    rw [Envelope.topSimplices_of_ne_univ D hBne]
    simp only [Finset.sum_singleton, φ]
    simp only [hgood_iff B hB]
  have hfilter :
      (SimplexFamily.boundaryIndices (Finset.univ : Finset I)).filter
          (fun B ↦ i ∉ B) = {Finset.univ.erase i} := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hB, hiB⟩
      have hBdata := hboundary B hB
      have hsub : B ⊆ Finset.univ.erase i := by
        intro j hj
        exact Finset.mem_erase.mpr ⟨fun hji ↦ hiB (hji ▸ hj), Finset.mem_univ j⟩
      have heraseCard : (Finset.univ.erase i : Finset I).card + 1 = Fintype.card I := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
        have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
        omega
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
    · intro h
      subst B
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (Finset.erase_subset _ _), ?_⟩
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
        have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
        omega
      · simp
  change SimplexFamily.cochainEval φ
      ((Envelope.family D).boundaryIndexChain (Finset.univ : Finset I)) = 1
  rw [SimplexFamily.cochainEval_boundaryIndexChain]
  calc
    (∑ B ∈ SimplexFamily.boundaryIndices (Finset.univ : Finset I),
        ∑ σ ∈ ((Envelope.family D).complex B).topSimplices B.card, φ σ) =
        ∑ B ∈ SimplexFamily.boundaryIndices (Finset.univ : Finset I),
          if i ∉ B then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      exact hinner B hB
    _ = ((SimplexFamily.boundaryIndices (Finset.univ : Finset I)).filter
          (fun B ↦ i ∉ B)).card := by
      rw [Finset.sum_boole]
    _ = 1 := by rw [hfilter]; simp

/-- The conclusion attached to a pair `(C,τ)` in Theorems 6.5 and 8.5. -/
def IsSolution (D : SimplexFamily I V) (F : Framework I M)
    (c : Coloring D F) (C : Finset I) (τ : Finset V) : Prop :=
  ∃ hτ : τ ∈ D.complex C,
    C.Nonempty ∧ τ.card = C.card ∧
      F.matroid.IsGoodBasis F.distinguished
        (completedImage D F c C τ hτ : Set M)

/-- The finite set of all solution pairs, used to state the parity clause of Theorem 6.5. -/
noncomputable def solutionPairs (D : SimplexFamily I V) (F : Framework I M)
    (c : Coloring D F) : Finset (Finset I × Finset V) :=
  Finset.univ.filter fun p ↦ IsSolution D F c p.1 p.2

/-- Theorem 6.5, including the oddness assertion. -/
theorem theorem6_5
    [Fintype M] (D : SimplexFamily I V) (F : Framework I M)
    (hchain : D.IsChainSimplex) (hnd : F.IsNondegenerate)
    (c : Coloring D F) :
    (solutionPairs D F c).Nonempty ∧ Odd (solutionPairs D F c).card := by
  classical
  let : Nonempty I := Framework.index_nonempty F
  let i : I := Classical.choice (inferInstance : Nonempty I)
  let g : V ⊕ I → M := envelopeColor D F c
  let φ : Finset (V ⊕ I) → ZMod 2 := fun ρ ↦
    if F.matroid.IsGoodBasis F.distinguished
      (insert (F.vertex i) (ρ.image g) : Set M)
    then 1 else 0
  let tops : Finset (Finset (V ⊕ I)) :=
    ((Envelope.family D).complex (Finset.univ : Finset I)).topSimplices
      (Finset.univ : Finset I).card
  let goodTops : Finset (Finset (V ⊕ I)) :=
    tops.filter fun ρ ↦
      F.matroid.IsGoodBasis F.distinguished (ρ.image g : Set M)
  have hlocal (ρ : Finset (V ⊕ I)) (hρ : ρ ∈ tops) :
      (∑ z ∈ ρ, φ (ρ.erase z)) =
        if F.matroid.IsGoodBasis F.distinguished (ρ.image g : Set M)
        then 1 else 0 := by
    have hρraw := Finset.mem_filter.mp hρ
    have hρcomplex : ρ ∈ Envelope.complex D (Finset.univ : Finset I) :=
      (FiniteSimplicialComplex.mem_simplices_iff
        (Envelope.complex D (Finset.univ : Finset I)) ρ).mp hρraw.1
    have hρtop :
        ρ ∈ Envelope.complex D (Finset.univ : Finset I) ∧
          ρ.card = (Finset.univ : Finset I).card := ⟨hρcomplex, hρraw.2⟩
    obtain ⟨C, hC, htopτ, hindex⟩ :=
      (Envelope.isTopSimplex_univ_iff D ρ).mp hρtop
    have hgb : ∀ z ∈ ρ, g z ≠ F.distinguished := by
      intro z hz
      cases z with
      | inl v =>
          have hvold : v ∈ Envelope.oldPart ρ := by
            simpa [Envelope.oldPart] using hz
          have hvVertex :=
            mem_vertexSet_of_mem_simplex D htopτ.1 hvold
          exact by
            simpa [g, envelopeColor, hvVertex] using
              (c ⟨v, hvVertex⟩).property
      | inr j =>
          intro hj
          apply F.distinguished_notMem_basis
          exact ⟨j, by simpa [g, envelopeColor] using hj⟩
    simpa [φ, g, Finset.card_univ] using
      F.boundary_goodBasis_parity hnd i ρ (by simpa using hρraw.2) g hgb
  have hleft :
      SimplexFamily.cochainEval φ
          (SimplexFamily.boundary
            ((Envelope.family D).topChain (Finset.univ : Finset I))) =
        (goodTops.card : ZMod 2) := by
    rw [SimplexFamily.cochainEval_boundary_topChain]
    change (∑ ρ ∈ tops, ∑ z ∈ ρ, φ (ρ.erase z)) = _
    calc
      (∑ ρ ∈ tops, ∑ z ∈ ρ, φ (ρ.erase z)) =
          ∑ ρ ∈ tops,
            if F.matroid.IsGoodBasis F.distinguished (ρ.image g : Set M)
            then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        exact hlocal ρ hρ
      _ = (goodTops.card : ZMod 2) := by
        simp [goodTops, Finset.sum_boole]
  have hright :
      SimplexFamily.cochainEval φ
          ((Envelope.family D).boundaryIndexChain (Finset.univ : Finset I)) = 1 := by
    simpa [φ, g] using envelope_boundary_cochain_eval D F c i
  have hchainE :=
    (Envelope.chain_family hchain) (Finset.univ : Finset I)
  have heval := congrArg (SimplexFamily.cochainEval φ) hchainE
  have hgoodTopsCast : (goodTops.card : ZMod 2) = 1 := by
    rw [hleft] at heval
    rw [hright] at heval
    exact heval
  have hgoodTopsOdd : Odd goodTops.card :=
    ZMod.natCast_eq_one_iff_odd.mp hgoodTopsCast
  let encode : Finset I × Finset V → Finset (V ⊕ I) := fun p ↦
    Envelope.oldSimplex p.2 ∪ Envelope.indexSimplex (Finset.univ \ p.1)
  have hcardEq : (solutionPairs D F c).card = goodTops.card := by
    apply Finset.card_bij (fun p _ ↦ encode p)
    · intro p hp
      have hpSol : IsSolution D F c p.1 p.2 := (Finset.mem_filter.mp hp).2
      obtain ⟨hτ, hC, hcard, hgood⟩ := hpSol
      apply Finset.mem_filter.mpr
      constructor
      · dsimp [tops, encode]
        apply Finset.mem_filter.mpr
        constructor
        · apply (FiniteSimplicialComplex.mem_simplices_iff
            (Envelope.complex D (Finset.univ : Finset I)) _).mpr
          exact (Envelope.isTopSimplex_univ_iff D _).mpr
            ⟨p.1, hC, ⟨by simp; exact hτ, by simpa using hcard⟩, by simp⟩ |>.1
        · have htop := (Envelope.isTopSimplex_univ_iff D
              (Envelope.oldSimplex p.2 ∪
                Envelope.indexSimplex (Finset.univ \ p.1))).mpr
              ⟨p.1, hC, ⟨by simpa using hτ, by simpa using hcard⟩, by simp⟩
          exact htop.2
      · dsimp [encode, g]
        rw [envelopeColor_image_cell D F c p.1 p.2 hτ]
        exact hgood
    · intro p hp q hq hpq
      apply Prod.ext
      · have hindex := congrArg Envelope.indexPart hpq
        simp only [encode, Envelope.indexPart_oldSimplex_union_indexSimplex] at hindex
        have := congrArg (fun K : Finset I ↦ Finset.univ \ K) hindex
        simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ p.1),
          Finset.sdiff_sdiff_eq_self (Finset.subset_univ q.1)] using this
      · have hold := congrArg Envelope.oldPart hpq
        simpa [encode] using hold
    · intro ρ hρ
      have hρdata := Finset.mem_filter.mp hρ
      have hρtopraw := Finset.mem_filter.mp hρdata.1
      have hρcomplex : ρ ∈ Envelope.complex D (Finset.univ : Finset I) :=
        (FiniteSimplicialComplex.mem_simplices_iff
          (Envelope.complex D (Finset.univ : Finset I)) ρ).mp hρtopraw.1
      obtain ⟨C, hC, htopτ, hindex⟩ :=
        (Envelope.isTopSimplex_univ_iff D ρ).mp ⟨hρcomplex, hρtopraw.2⟩
      let p : Finset I × Finset V := (C, Envelope.oldPart ρ)
      have hpSol : IsSolution D F c p.1 p.2 := by
        refine ⟨htopτ.1, hC, htopτ.2, ?_⟩
        have hρeq :
            ρ = Envelope.oldSimplex (Envelope.oldPart ρ) ∪
              Envelope.indexSimplex (Finset.univ \ C) := by
          calc
            ρ = Envelope.oldSimplex (Envelope.oldPart ρ) ∪
                Envelope.indexSimplex (Envelope.indexPart ρ) :=
              Envelope.old_index_decomposition ρ
            _ = Envelope.oldSimplex (Envelope.oldPart ρ) ∪
                Envelope.indexSimplex (Finset.univ \ C) := by rw [hindex]
        have himage := envelopeColor_image_cell D F c C (Envelope.oldPart ρ) htopτ.1
        rw [← himage, ← hρeq]
        simpa [g] using hρdata.2
      have hp : p ∈ solutionPairs D F c :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpSol⟩
      refine ⟨p, hp, ?_⟩
      calc
        encode p = Envelope.oldSimplex (Envelope.oldPart ρ) ∪
            Envelope.indexSimplex (Envelope.indexPart ρ) := by
          simp only [encode, p, hindex]
        _ = ρ := (Envelope.old_index_decomposition ρ).symm
  have hsolutionOdd : Odd (solutionPairs D F c).card := by
    rw [hcardEq]
    exact hgoodTopsOdd
  exact ⟨Finset.card_pos.mp hsolutionOdd.pos, hsolutionOdd⟩

end Coloring

end MatroidColoring

end BeyondSperner
