import BeyondSperner.OrientedMatroid.LexicographicExtension
import BeyondSperner.Coloring.Matroid.Nondegenerate

/-!
# Oriented-matroid colorings: the general case

Statements from Section 8.  The lexicographic perturbation data is bundled explicitly so that the
types distinguish the original oriented matroid `M`, its one-point extension `L = M+p`, and the
deletion `L-b`.
-/

namespace BeyondSperner

open Classical
open Set

namespace MatroidColoring

variable {I M V β : Type*}

namespace Framework

/-- Some distinguished-basis element can be exchanged for the distinguished point. -/
theorem exists_replaceBasis_isBasis
    [Fintype I] [Finite M] [DecidableEq M] (F : Framework I M) :
    ∃ i : I, F.matroid.IsBasis (F.replaceBasis i F.distinguished) := by
  rcases F.distinguished_mem_convexHull with hb | ⟨C, hC, hCpos, hCneg⟩
  · exact (F.distinguished_notMem_basis hb).elim
  obtain ⟨e, heCpos⟩ := F.acyclic.positive_nonempty hC
  obtain ⟨i, hei⟩ := hCpos heCpos
  subst e
  let U : Matroid M := F.matroid.underlying
  let B : Set M := Set.range F.vertex
  have hBbase : U.IsBase B :=
    F.matroid.isBasis_iff_underlying_isBase.mp F.basis_isBasis
  have hbGround : F.distinguished ∈ U.E := by
    rw [F.matroid.underlying_spec.1]
    trivial
  have hbB : F.distinguished ∉ B := F.distinguished_notMem_basis
  have hCsupport : U.IsCircuit C.support :=
    (F.matroid.underlying_spec.2 C.support).mpr ⟨C, hC, rfl⟩
  have hCsub : C.support ⊆ insert F.distinguished B := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inr (hCpos hx)
    · have hxb : x = F.distinguished := by simpa [hCneg] using hx
      exact Or.inl hxb
  have hCfund : C.support = U.fundCircuit F.distinguished B :=
    hCsupport.eq_fundCircuit_of_subset hBbase.indep hCsub
  have hviFund : F.vertex i ∈ U.fundCircuit F.distinguished B := by
    rw [← hCfund]
    exact Or.inl heCpos
  have hind : U.Indep (insert F.distinguished B \ {F.vertex i}) :=
    (hBbase.indep.mem_fundCircuit_iff
      (by rw [hBbase.closure_eq]; exact hbGround) hbB).mp hviFund
  have hbaseExchange : U.IsBase (insert F.distinguished B \ {F.vertex i}) :=
    hBbase.exchange_isBase_of_indep' ⟨i, rfl⟩ hbB hind
  refine ⟨i, F.matroid.isBasis_iff_underlying_isBase.mpr ?_⟩
  have hEq :
      insert F.distinguished B \ {F.vertex i} =
        F.replaceBasis i F.distinguished := by
    ext x
    have hbvi : F.distinguished ≠ F.vertex i := by
      intro h
      exact F.distinguished_notMem_basis ⟨i, h.symm⟩
    simp only [B, Framework.replaceBasis, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_union, Set.mem_range]
    aesop
  simpa [hEq] using hbaseExchange

end Framework

/--
The ordered perturbation used in Section 8: choose `v₀` such that `B-v₀+b` is a basis and take the
lexicographic extension associated with the ordered basis `(b,v₁,...,vₙ)`.
-/
structure PerturbationSetup [Fintype I] [DecidableEq I] [DecidableEq M]
    (F : Framework I M) (β : Type*) where
  pivot : I
  tail : List I
  tail_nodup : tail.Nodup
  tail_toFinset : tail.toFinset = Finset.univ.erase pivot
  replacement_isBasis : F.matroid.IsBasis (F.replaceBasis pivot F.distinguished)
  extension : OrientedMatroid.OnePointExtension F.matroid β
  isLexicographic : extension.IsLexicographicFor
    (F.distinguished :: tail.map F.vertex)

/-- The lexicographic-extension theorem produces the perturbation data used in Section 8. -/
theorem exists_perturbationSetup
    [Fintype I] [Fintype M] [DecidableEq I] [DecidableEq M]
    (F : Framework I M) :
    ∃ _P : PerturbationSetup F (M ⊕ Unit), True := by
  obtain ⟨pivot, hpivot⟩ := F.exists_replaceBasis_isBasis
  let tail : List I := (Finset.univ.erase pivot).toList
  have htailNodup : tail.Nodup := by
    exact Finset.nodup_toList _
  have htailFinset : tail.toFinset = Finset.univ.erase pivot := by
    exact Finset.toList_toFinset _
  let order : List M := F.distinguished :: tail.map F.vertex
  have horderNodup : order.Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro hb
      obtain ⟨i, _, hbi⟩ := List.mem_map.mp hb
      exact F.distinguished_notMem_basis ⟨i, hbi⟩
    · exact htailNodup.map F.vertex.injective
  have horderSet : (order.toFinset : Set M) =
      F.replaceBasis pivot F.distinguished := by
    ext x
    simp only [Finset.mem_coe, List.mem_toFinset, order, List.mem_cons,
      List.mem_map, Framework.replaceBasis, Set.mem_union, Set.mem_sdiff,
      Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact Or.inr rfl
      · left
        refine ⟨⟨i, rfl⟩, ?_⟩
        intro hip
        have hiFin : i ∈ tail.toFinset := List.mem_toFinset.mpr hi
        rw [htailFinset] at hiFin
        exact (Finset.mem_erase.mp hiFin).1
          (F.vertex.injective hip)
    · rintro (⟨⟨i, rfl⟩, hip⟩ | rfl)
      · right
        refine ⟨i, ?_, rfl⟩
        have hi : i ∈ tail.toFinset := by
          rw [htailFinset]
          exact Finset.mem_erase.mpr
            ⟨fun h ↦ hip (congrArg F.vertex h), Finset.mem_univ i⟩
        exact List.mem_toFinset.mp hi
      · exact Or.inl rfl
  have horderIndependent : F.matroid.IsIndependent (order.toFinset : Set M) := by
    rw [horderSet]
    exact hpivot.1
  obtain ⟨L, hL⟩ :=
    OrientedMatroid.exists_lexicographicExtension F.matroid order horderNodup
      horderIndependent
  refine ⟨{
    pivot := pivot
    tail := tail
    tail_nodup := htailNodup
    tail_toFinset := htailFinset
    replacement_isBasis := hpivot
    extension := L
    isLexicographic := by simpa [order] using hL }, trivial⟩

namespace PerturbationSetup

variable [Fintype I] [DecidableEq I] [DecidableEq M]
  {F : Framework I M} (P : PerturbationSetup F β)

/-- The lexicographic list contains exactly one entry for every color. -/
theorem order_length :
    (F.distinguished :: P.tail.map F.vertex).length = Fintype.card I := by
  have htailCard : P.tail.length = (Finset.univ.erase P.pivot).card := by
    rw [← P.tail_toFinset]
    exact (List.toFinset_card_of_nodup P.tail_nodup).symm
  rw [List.length_cons, List.length_map, htailCard,
    Finset.card_erase_of_mem (Finset.mem_univ P.pivot), Finset.card_univ]
  have hcardPos : 0 < Fintype.card I :=
    Fintype.card_pos_iff.mpr F.index_nonempty
  omega

/-- The underlying set of the lexicographic list is the replacement basis. -/
theorem order_toFinset :
    ((F.distinguished :: P.tail.map F.vertex).toFinset : Set M) =
      F.replaceBasis P.pivot F.distinguished := by
  ext x
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_cons, List.mem_map,
    Framework.replaceBasis, Set.mem_union, Set.mem_sdiff, Set.mem_range,
    Set.mem_singleton_iff]
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact Or.inr rfl
    · left
      refine ⟨⟨i, rfl⟩, ?_⟩
      intro hip
      have hiFin : i ∈ P.tail.toFinset := List.mem_toFinset.mpr hi
      rw [P.tail_toFinset] at hiFin
      exact (Finset.mem_erase.mp hiFin).1 (F.vertex.injective hip)
  · rintro (⟨⟨i, rfl⟩, hip⟩ | rfl)
    · right
      refine ⟨i, ?_, rfl⟩
      apply List.mem_toFinset.mp
      rw [P.tail_toFinset]
      exact Finset.mem_erase.mpr
        ⟨fun h ↦ hip (congrArg F.vertex h), Finset.mem_univ i⟩
    · exact Or.inl rfl

/-- The signed circuit with positive part `B-v₀+b` and negative part `{p}` from Lemma 8.1. -/
def fundamentalCircuit : SignedSubset β where
  positive := P.extension.old '' F.replaceBasis P.pivot F.distinguished
  negative := {P.extension.new}
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨y, _, rfl⟩ hx
    simp only [Set.mem_singleton_iff] at hx
    exact P.extension.new_not_old ⟨y, hx⟩

/-- Lemma 8.1, lower bound for every circuit containing the new point. -/
theorem new_mem_circuit_card
    [Fintype M] [Fintype β] {C : SignedSubset β}
    (hC : P.extension.matroid.IsCircuit C) (hp : P.extension.new ∈ C.support) :
    Fintype.card I + 1 ≤ C.support.ncard := by
  classical
  let order : List M := F.distinguished :: P.tail.map F.vertex
  let S : Set M := P.extension.old ⁻¹' C.support
  have holdImage : P.extension.old '' S = C.support \ {P.extension.new} := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨hy, fun h ↦ P.extension.new_not_old ⟨y, h⟩⟩
    · intro x hx
      have hxground : x ∈ Set.range P.extension.old ∪ {P.extension.new} := by
        rw [P.extension.ground_eq]
        trivial
      rcases hxground with ⟨y, rfl⟩ | hxnew
      · exact ⟨y, hx.1, rfl⟩
      · exact (hx.2 (by simpa using hxnew)).elim
  have hSindependent : F.matroid.IsIndependent S := by
    intro R hR hRsub
    have hmapR : P.extension.matroid.IsCircuit (R.map P.extension.old) :=
      (P.extension.old_isCircuit_iff R).mpr hR
    have hmapSub : (R.map P.extension.old).support ⊆ C.support := by
      rw [SignedSubset.support_map]
      rintro _ ⟨x, hx, rfl⟩
      exact hRsub hx
    rcases P.extension.matroid.eq_or_eq_neg_of_support_subset hmapR hC hmapSub with
      hEq | hEq
    · have hpmap : P.extension.new ∈ (R.map P.extension.old).support := hEq ▸ hp
      rw [SignedSubset.support_map] at hpmap
      obtain ⟨x, _, hx⟩ := hpmap
      exact P.extension.new_not_old ⟨x, hx⟩
    · have hpmap : P.extension.new ∈ (R.map P.extension.old).support := by
        rw [hEq, SignedSubset.support_neg]
        exact hp
      rw [SignedSubset.support_map] at hpmap
      obtain ⟨x, _, hx⟩ := hpmap
      exact P.extension.new_not_old ⟨x, hx⟩
  have hsupportCard : C.support.ncard = S.ncard + 1 := by
    rw [← Set.ncard_sdiff_singleton_add_one hp, ← holdImage,
      Set.ncard_image_of_injective S P.extension.old.injective]
  by_contra hlarge
  have hsmall : S.ncard < Fintype.card I := by omega
  let Sfin : Finset M := Set.toFinite S |>.toFinset
  let Ofin : Finset M := order.toFinset
  have hSfin : (Sfin : Set M) = S := by
    ext x
    simp [Sfin, S]
  have hOfin : (Ofin : Set M) = (order.toFinset : Set M) := rfl
  have hSunderlying : F.matroid.underlying.Indep (Sfin : Set M) := by
    rw [hSfin]
    exact F.matroid.isIndependent_iff_underlying_indep.mp hSindependent
  have hOunderlying : F.matroid.underlying.Indep (Ofin : Set M) := by
    rw [hOfin]
    exact F.matroid.isIndependent_iff_underlying_indep.mp P.isLexicographic.2.1
  have hfinCard : Sfin.card < Ofin.card := by
    have hScard : Sfin.card = S.ncard := by
      rw [Set.ncard_eq_toFinset_card S (Set.toFinite S)]
    have hOcard : Ofin.card = Fintype.card I := by
      change order.toFinset.card = Fintype.card I
      rw [List.toFinset_card_of_nodup P.isLexicographic.1]
      exact P.order_length
    omega
  obtain ⟨a, haO, haS, hInsertUnderlying⟩ :=
    hSunderlying.augment_finset hOunderlying hfinCard
  have haSset : a ∉ S := by
    rw [← hSfin]
    simpa using haS
  have hInsertIndependent : F.matroid.IsIndependent (insert a S) := by
    apply F.matroid.isIndependent_iff_underlying_indep.mpr
    simpa [hSfin] using hInsertUnderlying
  obtain ⟨D, hD, hDinter⟩ :=
    OrientedMatroid.Data.IsIndependent.exists_isCocircuit_support_inter_eq_singleton
      F.matroid hInsertIndependent (Set.mem_insert a S)
  have haD : a ∈ D.support := by
    have : a ∈ D.support ∩ insert a S := by simp [hDinter]
    exact this.1
  have haOrder : a ∈ (order.toFinset : Set M) := by
    simpa [Ofin] using haO
  have hDorder : (D.support ∩ (order.toFinset : Set M)).Nonempty :=
    ⟨a, haD, haOrder⟩
  obtain ⟨E, hE, hpE, hEcomap⟩ :=
    P.extension.exists_liftedCocircuit order P.isLexicographic hD hDorder
  have hinter : C.support ∩ E.support = {P.extension.new} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxground : x ∈ Set.range P.extension.old ∪ {P.extension.new} := by
        rw [P.extension.ground_eq]
        trivial
      rcases hxground with ⟨y, rfl⟩ | hxnew
      · have hyS : y ∈ S := hx.1
        have hyComap : y ∈ (E.comap P.extension.old).support := by
          rw [SignedSubset.support_comap]
          exact hx.2
        have hyD : y ∈ D.support := by simpa [hEcomap] using hyComap
        have hyInter : y ∈ D.support ∩ insert a S := ⟨hyD, Or.inr hyS⟩
        have hya : y = a := by simpa [hDinter] using hyInter
        exact (haSset (hya ▸ hyS)).elim
      · simpa using hxnew
    · exact Set.singleton_subset_iff.mpr ⟨hp, hpE⟩
  exact SignedSubset.not_orthogonal_of_support_inter_eq_singleton hinter
    (hE.2.1 hC)

/-- Lemma 8.1, the distinguished perturbation circuit. -/
theorem fundamentalCircuit_isCircuit [Fintype M] [Fintype β] :
    P.extension.matroid.IsCircuit P.fundamentalCircuit := by
  classical
  let order : List M := F.distinguished :: P.tail.map F.vertex
  let B₀ : Set M := F.replaceBasis P.pivot F.distinguished
  let B : Set β := P.extension.old '' B₀
  have hB₀basis : F.matroid.IsBasis B₀ := P.replacement_isBasis
  have hBbasis : P.extension.matroid.IsBasis B := by
    exact P.isLexicographic.2.2.1 B₀ |>.mp hB₀basis
  have hpB : P.extension.new ∉ B := by
    rintro ⟨x, _, hx⟩
    exact P.extension.new_not_old ⟨x, hx⟩
  let C₀ : SignedSubset β :=
    P.extension.matroid.signedFundCircuit B hBbasis P.extension.new
  have hC₀ : P.extension.matroid.IsCircuit C₀ :=
    P.extension.matroid.signedFundCircuit_isCircuit hBbasis hpB
  have hpC₀pos : P.extension.new ∈ C₀.positive :=
    P.extension.matroid.signedFundCircuit_external_positive hBbasis hpB
  have hpC₀support : P.extension.new ∈ C₀.support := Or.inl hpC₀pos
  have hC₀supportSub : C₀.support ⊆ insert P.extension.new B := by
    rw [P.extension.matroid.signedFundCircuit_support hBbasis hpB]
    exact P.extension.matroid.underlying.fundCircuit_subset_insert _ _
  have hB₀card : B₀.ncard = Fintype.card I := by
    have hB₀base : F.matroid.underlying.IsBase B₀ :=
      F.matroid.isBasis_iff_underlying_isBase.mp hB₀basis
    have hVertexBase : F.matroid.underlying.IsBase (Set.range F.vertex) :=
      F.matroid.isBasis_iff_underlying_isBase.mp F.basis_isBasis
    have hcard := hB₀base.ncard_eq_ncard_of_isBase hVertexBase
    simpa [B₀, Set.ncard_range_of_injective F.vertex.injective] using hcard
  have hBcard : B.ncard = Fintype.card I := by
    change (P.extension.old '' B₀).ncard = Fintype.card I
    rw [Set.ncard_image_of_injective B₀ P.extension.old.injective, hB₀card]
  have hInsertCard : (insert P.extension.new B).ncard = Fintype.card I + 1 := by
    rw [Set.ncard_insert_of_notMem hpB, hBcard]
  have hC₀large : Fintype.card I + 1 ≤ C₀.support.ncard :=
    P.new_mem_circuit_card hC₀ hpC₀support
  have hC₀support : C₀.support = insert P.extension.new B := by
    apply Set.eq_of_subset_of_ncard_le hC₀supportSub
    omega
  have holdNegative : B ⊆ C₀.negative := by
    rintro _ ⟨a, haB₀, rfl⟩
    obtain ⟨D, hD, hDinter⟩ :=
      OrientedMatroid.Data.IsIndependent.exists_isCocircuit_support_inter_eq_singleton
        F.matroid hB₀basis.1 haB₀
    have hDorder : D.support ∩ (order.toFinset : Set M) = {a} := by
      have horderSet : (order.toFinset : Set M) = B₀ := by
        simpa [order, B₀] using P.order_toFinset
      rw [horderSet]
      exact hDinter
    obtain ⟨E, hE, hpE, hEcomap, hEsame⟩ :=
      P.extension.exists_liftedCocircuit_sameSignWithin order P.isLexicographic hD hDorder
    have haD : a ∈ D.support := by
      have : a ∈ D.support ∩ B₀ := by simp [hDinter]
      exact this.1
    have holdaE : P.extension.old a ∈ E.support := by
      have : a ∈ (E.comap P.extension.old).support := by simpa [hEcomap] using haD
      rw [SignedSubset.support_comap] at this
      exact this
    have hinter : C₀.support ∩ E.support =
        {P.extension.new, P.extension.old a} := by
      apply Set.Subset.antisymm
      · intro x hx
        have hxground : x ∈ Set.range P.extension.old ∪ {P.extension.new} := by
          rw [P.extension.ground_eq]
          trivial
        rcases hxground with ⟨y, rfl⟩ | hxnew
        · have hyB₀ : y ∈ B₀ := by
            have : P.extension.old y ∈ B := by
              rw [hC₀support] at hx
              rcases hx.1 with hnew | hBmem
              · exact (P.extension.new_not_old ⟨y, hnew⟩).elim
              · exact hBmem
            obtain ⟨z, hz, hzy⟩ := this
            exact P.extension.old.injective hzy.symm ▸ hz
          have hyD : y ∈ D.support := by
            have : y ∈ (E.comap P.extension.old).support := by
              rw [SignedSubset.support_comap]
              exact hx.2
            simpa [hEcomap] using this
          have hya : y = a := by
            have : y ∈ D.support ∩ B₀ := ⟨hyD, hyB₀⟩
            rw [hDinter] at this
            simpa using this
          simp [hya]
        · exact Or.inl (by simpa using hxnew)
      · intro x hx
        rcases hx with (rfl | hx)
        · exact ⟨hpC₀support, hpE⟩
        · have hxa : x = P.extension.old a := by simpa using hx
          subst x
          exact ⟨hC₀support.symm ▸ Or.inr ⟨a, haB₀, rfl⟩, holdaE⟩
    have horth : C₀.Orthogonal E := hE.2.1 hC₀
    rcases horth with hdisjoint | ⟨u, hu, v, hv, husame, hvopp⟩
    · exact (Set.disjoint_left.1 hdisjoint hpC₀support hpE).elim
    · have huCases : u = P.extension.new ∨ u = P.extension.old a := by
        rw [hinter] at hu
        simpa using hu
      have hvCases : v = P.extension.new ∨ v = P.extension.old a := by
        rw [hinter] at hv
        simpa using hv
      rcases hEsame with hEpos | hEneg
      · rcases hvCases with rfl | rfl
        · have hsameAtNew : C₀.SameSignAt E P.extension.new :=
            Or.inl ⟨hpC₀pos, hEpos.1⟩
          exact (hsameAtNew.not_oppositeAt hvopp).elim
        · rcases hvopp with hvopp | hvopp
          · exact (Set.disjoint_left.1 E.disjoint hEpos.2 hvopp.2).elim
          · exact hvopp.1
      · rcases huCases with rfl | rfl
        · have hoppAtNew : C₀.OppositeAt E P.extension.new :=
            Or.inl ⟨hpC₀pos, hEneg.1⟩
          exact (husame.not_oppositeAt hoppAtNew).elim
        · rcases husame with husame | husame
          · exact (Set.disjoint_left.1 E.disjoint husame.2 hEneg.2).elim
          · exact husame.1
  have hC₀negative : C₀.negative = B := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxSupport : x ∈ C₀.support := Or.inr hx
      rw [hC₀support] at hxSupport
      rcases hxSupport with hxp | hxB
      · subst x
        exact (Set.disjoint_left.1 C₀.disjoint hpC₀pos hx).elim
      · exact hxB
    · exact holdNegative
  have hC₀positive : C₀.positive = {P.extension.new} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxSupport : x ∈ C₀.support := Or.inl hx
      rw [hC₀support] at hxSupport
      rcases hxSupport with hxp | hxB
      · simp [hxp]
      · exact (Set.disjoint_left.1 C₀.disjoint hx (holdNegative hxB)).elim
    · exact Set.singleton_subset_iff.mpr hpC₀pos
  have hEq : P.fundamentalCircuit = -C₀ := by
    apply SignedSubset.ext
    · change B = C₀.negative
      exact hC₀negative.symm
    · change {P.extension.new} = C₀.positive
      exact hC₀positive.symm
  rw [hEq]
  exact P.extension.matroid.neg_isCircuit hC₀

/-- Lemma 8.2, expressed across the old-element embedding. -/
theorem circuit_transfer_unique
    [Fintype M] [Fintype β]
    {C : SignedSubset β} (hC : P.extension.matroid.IsCircuit C)
    (hp : P.extension.new ∈ C.negative)
    (hb : P.extension.old F.distinguished ∉ C.support) :
    ∃! R : SignedSubset M,
      F.matroid.IsCircuit R ∧ F.distinguished ∈ R.negative ∧
        P.extension.old '' (R.negative \ {F.distinguished}) ⊆ C.negative ∧
        P.extension.old '' R.positive ⊆ C.positive := by
  classical
  let S : Set M := P.extension.old ⁻¹' C.support
  have hSindependent : F.matroid.IsIndependent S := by
    intro Q hQ hQsub
    have hmapQ : P.extension.matroid.IsCircuit (Q.map P.extension.old) :=
      (P.extension.old_isCircuit_iff Q).mpr hQ
    have hmapSub : (Q.map P.extension.old).support ⊆ C.support := by
      rw [SignedSubset.support_map]
      rintro _ ⟨x, hx, rfl⟩
      exact hQsub hx
    rcases P.extension.matroid.eq_or_eq_neg_of_support_subset hmapQ hC hmapSub with
      hEq | hEq
    · have hpmap : P.extension.new ∈ (Q.map P.extension.old).support := hEq ▸ Or.inr hp
      rw [SignedSubset.support_map] at hpmap
      obtain ⟨x, _, hx⟩ := hpmap
      exact P.extension.new_not_old ⟨x, hx⟩
    · have hpmap : P.extension.new ∈ (Q.map P.extension.old).support := by
        rw [hEq, SignedSubset.support_neg]
        exact Or.inr hp
      rw [SignedSubset.support_map] at hpmap
      obtain ⟨x, _, hx⟩ := hpmap
      exact P.extension.new_not_old ⟨x, hx⟩
  have hbS : F.distinguished ∉ S := hb
  have hInsertDependent : ¬ F.matroid.IsIndependent (insert F.distinguished S) := by
    intro hInsertIndependent
    obtain ⟨D, hD, hDinter⟩ :=
      OrientedMatroid.Data.IsIndependent.exists_isCocircuit_support_inter_eq_singleton
        F.matroid hInsertIndependent (Set.mem_insert F.distinguished S)
    have hbD : F.distinguished ∈ D.support := by
      have : F.distinguished ∈ D.support ∩ insert F.distinguished S := by
        rw [hDinter]
        simp
      exact this.1
    obtain ⟨E, hE, hpE, hEcomap, _⟩ :=
      P.extension.exists_liftedCocircuit_sameSignWithin_head F.distinguished
        (P.tail.map F.vertex) P.isLexicographic hD hbD
    have hinter : C.support ∩ E.support = {P.extension.new} := by
      apply Set.Subset.antisymm
      · intro x hx
        have hxground : x ∈ Set.range P.extension.old ∪ {P.extension.new} := by
          rw [P.extension.ground_eq]
          trivial
        rcases hxground with ⟨y, rfl⟩ | hxnew
        · have hyS : y ∈ S := hx.1
          have hyD : y ∈ D.support := by
            have : y ∈ (E.comap P.extension.old).support := by
              rw [SignedSubset.support_comap]
              exact hx.2
            simpa [hEcomap] using this
          have hyInter : y ∈ D.support ∩ insert F.distinguished S :=
            ⟨hyD, Or.inr hyS⟩
          have hyb : y = F.distinguished := by
            rw [hDinter] at hyInter
            simpa using hyInter
          exact (hb (hyb ▸ hx.1)).elim
        · simpa using hxnew
      · exact Set.singleton_subset_iff.mpr ⟨Or.inr hp, hpE⟩
    exact SignedSubset.not_orthogonal_of_support_inter_eq_singleton hinter
      (hE.2.1 hC)
  have hSunderlying : F.matroid.underlying.Indep S :=
    F.matroid.isIndependent_iff_underlying_indep.mp hSindependent
  have hInsertDepUnderlying : F.matroid.underlying.Dep (insert F.distinguished S) := by
    rw [Matroid.dep_iff]
    refine ⟨?_, ?_⟩
    · intro h
      exact hInsertDependent (F.matroid.isIndependent_iff_underlying_indep.mpr h)
    · rw [F.matroid.underlying_spec.1]
      exact Set.subset_univ _
  have hbClosure : F.distinguished ∈ F.matroid.underlying.closure S :=
    (hSunderlying.mem_closure_iff_of_notMem hbS).mpr hInsertDepUnderlying
  have hFundUnsigned : F.matroid.underlying.IsCircuit
      (F.matroid.underlying.fundCircuit F.distinguished S) :=
    hSunderlying.fundCircuit_isCircuit hbClosure hbS
  obtain ⟨Q, hQ, hQsupport, hbQpos⟩ :=
    F.matroid.exists_isCircuit_support_eq_positive hFundUnsigned
      (F.matroid.underlying.mem_fundCircuit F.distinguished S)
  let R : SignedSubset M := -Q
  have hR : F.matroid.IsCircuit R := F.matroid.neg_isCircuit hQ
  have hbRneg : F.distinguished ∈ R.negative := by simpa [R] using hbQpos
  have hRsupport : R.support = F.matroid.underlying.fundCircuit F.distinguished S := by
    simpa [R] using hQsupport
  have hRsupportSub : R.support ⊆ insert F.distinguished S := by
    rw [hRsupport]
    exact F.matroid.underlying.fundCircuit_subset_insert _ _
  obtain ⟨B, hBbase, hSB⟩ := hSunderlying.exists_isBase_superset
  have hB : F.matroid.IsBasis B :=
    F.matroid.isBasis_iff_underlying_isBase.mpr hBbase
  have hbB : F.distinguished ∉ B := by
    intro hbB
    have hInsertSub : insert F.distinguished S ⊆ B := insert_subset hbB hSB
    exact hInsertDependent
      (F.matroid.isIndependent_iff_underlying_indep.mpr (hBbase.indep.subset hInsertSub))
  have hRsupportFull :
      R.support = F.matroid.underlying.fundCircuit F.distinguished B := by
    have hRU : F.matroid.underlying.IsCircuit R.support :=
      (F.matroid.underlying_spec.2 R.support).mpr ⟨R, hR, rfl⟩
    apply hRU.eq_fundCircuit_of_subset hBbase.indep
    exact hRsupportSub.trans (insert_subset_insert hSB)
  have hSameOnSupport : ∀ x ∈ R.support, x ≠ F.distinguished →
      R.SameSignAt (C.comap P.extension.old) x := by
    intro x hxR hxb
    have hxS : x ∈ S := by
      rcases hRsupportSub hxR with hxb' | hxS
      · exact (hxb hxb').elim
      · exact hxS
    let D : SignedSubset M := F.matroid.fundamentalCocircuit B hB x
    have hxB : x ∈ B := hSB hxS
    have hD : F.matroid.IsCocircuit D :=
      F.matroid.fundamentalCocircuit_isCocircuit hB hxB
    have hDsupport : D.support = F.matroid.underlying.fundCocircuit x B := by
      simpa [D] using F.matroid.fundamentalCocircuit_support hB hxB
    have hbD : F.distinguished ∈ D.support := by
      rw [hDsupport, hBbase.mem_fundCocircuit_iff_mem_fundCircuit, ← hRsupportFull]
      exact hxR
    obtain ⟨E, hE, hpE, hEcomap, hEsame⟩ :=
      P.extension.exists_liftedCocircuit_sameSignWithin_head F.distinguished
        (P.tail.map F.vertex) P.isLexicographic hD hbD
    have hDBinter : D.support ∩ B = {x} := by
      rw [hDsupport]
      exact F.matroid.underlying.fundCocircuit_inter_eq hxB
    have hRDinter : R.support ∩ D.support = {F.distinguished, x} := by
      apply Set.Subset.antisymm
      · intro y hy
        rcases hRsupportSub hy.1 with hyb | hyS
        · exact Or.inl hyb
        · have hyDB : y ∈ D.support ∩ B := ⟨hy.2, hSB hyS⟩
          rw [hDBinter] at hyDB
          exact Or.inr (by simpa using hyDB)
      · intro y hy
        rcases hy with (rfl | hyx)
        · exact ⟨Or.inr hbRneg, hbD⟩
        · have hyx' : y = x := by simpa using hyx
          subst y
          have hxD : x ∈ D.support := by
            rw [hDsupport]
            exact F.matroid.underlying.mem_fundCocircuit x B
          exact ⟨hxR, hxD⟩
    have hCEinter : C.support ∩ E.support =
        {P.extension.new, P.extension.old x} := by
      apply Set.Subset.antisymm
      · intro y hy
        have hyground : y ∈ Set.range P.extension.old ∪ {P.extension.new} := by
          rw [P.extension.ground_eq]
          trivial
        rcases hyground with ⟨z, rfl⟩ | hyp
        · have hzS : z ∈ S := hy.1
          have hzD : z ∈ D.support := by
            have : z ∈ (E.comap P.extension.old).support := by
              rw [SignedSubset.support_comap]
              exact hy.2
            simpa [hEcomap] using this
          have hzDB : z ∈ D.support ∩ B := ⟨hzD, hSB hzS⟩
          rw [hDBinter] at hzDB
          exact Or.inr (congrArg P.extension.old (by simpa using hzDB))
        · exact Or.inl (by simpa using hyp)
      · intro y hy
        rcases hy with (rfl | hyx)
        · exact ⟨Or.inr hp, hpE⟩
        · have hyx' : y = P.extension.old x := by simpa using hyx
          subst y
          have hxE : P.extension.old x ∈ E.support := by
            have hxD : x ∈ D.support := by
              rw [hDsupport]
              exact F.matroid.underlying.mem_fundCocircuit x B
            have : x ∈ (E.comap P.extension.old).support := by
              simpa [hEcomap] using hxD
            rwa [SignedSubset.support_comap] at this
          exact ⟨hxS, hxE⟩
    have hRDorth : R.Orthogonal D := hD.2.1 hR
    have hCEorth : C.Orthogonal E := hE.2.1 hC
    have hColdSupport : x ∈ (C.comap P.extension.old).support := by
      rw [SignedSubset.support_comap]
      exact hxS
    have hDbOld :
        (P.extension.old F.distinguished ∈ E.positive ↔ F.distinguished ∈ D.positive) ∧
        (P.extension.old F.distinguished ∈ E.negative ↔ F.distinguished ∈ D.negative) := by
      constructor
      · change (F.distinguished ∈ (E.comap P.extension.old).positive ↔ _)
        rw [hEcomap]
      · change (F.distinguished ∈ (E.comap P.extension.old).negative ↔ _)
        rw [hEcomap]
    have hDxOld :
        (P.extension.old x ∈ E.positive ↔ x ∈ D.positive) ∧
        (P.extension.old x ∈ E.negative ↔ x ∈ D.negative) := by
      constructor
      · change (x ∈ (E.comap P.extension.old).positive ↔ _)
        rw [hEcomap]
      · change (x ∈ (E.comap P.extension.old).negative ↔ _)
        rw [hEcomap]
    rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem
        (show F.distinguished ∈ R.support ∩ D.support from ⟨Or.inr hbRneg, hbD⟩) with
      hRDbSame | hRDbOpp
    · have hbDneg : F.distinguished ∈ D.negative := by
        rcases hRDbSame with h | h
        · exact (Set.disjoint_left.1 R.disjoint h.1 hbRneg).elim
        · exact h.2
      have hpEneg : P.extension.new ∈ E.negative := by
        rcases hEsame with h | h
        · exact (Set.disjoint_left.1 E.disjoint h.2 (hDbOld.2.mpr hbDneg)).elim
        · exact h.1
      have hCEpSame : C.SameSignAt E P.extension.new := Or.inr ⟨hp, hpEneg⟩
      have hRDxOpp :=
        SignedSubset.oppositeAt_of_orthogonal_of_inter_eq_pair_of_sameSignAt
          hRDorth hRDinter hRDbSame
      have hCExOpp :=
        SignedSubset.oppositeAt_of_orthogonal_of_inter_eq_pair_of_sameSignAt
          hCEorth hCEinter hCEpSame
      have hColdDOpp : (C.comap P.extension.old).OppositeAt D x := by
        rcases hCExOpp with h | h
        · exact Or.inl ⟨h.1, hDxOld.2.mp h.2⟩
        · exact Or.inr ⟨h.1, hDxOld.1.mp h.2⟩
      exact hRDxOpp.sameSignAt_of_oppositeAt hColdDOpp
    · have hbDpos : F.distinguished ∈ D.positive := by
        rcases hRDbOpp with h | h
        · exact (Set.disjoint_left.1 R.disjoint h.1 hbRneg).elim
        · exact h.2
      have hpEpos : P.extension.new ∈ E.positive := by
        rcases hEsame with h | h
        · exact h.1
        · exact (Set.disjoint_left.1 E.disjoint (hDbOld.1.mpr hbDpos) h.2).elim
      have hCEpOpp : C.OppositeAt E P.extension.new := Or.inr ⟨hp, hpEpos⟩
      have hRDxSame :=
        SignedSubset.sameSignAt_of_orthogonal_of_inter_eq_pair_of_oppositeAt
          hRDorth hRDinter hRDbOpp
      have hCExSame :=
        SignedSubset.sameSignAt_of_orthogonal_of_inter_eq_pair_of_oppositeAt
          hCEorth hCEinter hCEpOpp
      have hColdDSame : (C.comap P.extension.old).SameSignAt D x := by
        rcases hCExSame with h | h
        · exact Or.inl ⟨h.1, hDxOld.1.mp h.2⟩
        · exact Or.inr ⟨h.1, hDxOld.2.mp h.2⟩
      exact hRDxSame.trans (SignedSubset.sameSignAt_comm.mp hColdDSame)
  have hRnegative : P.extension.old '' (R.negative \ {F.distinguished}) ⊆ C.negative := by
    rintro _ ⟨x, hx, rfl⟩
    have hxSupport : x ∈ R.support := Or.inr hx.1
    have hsame := hSameOnSupport x hxSupport (by simpa using hx.2)
    rcases hsame with h | h
    · exact (Set.disjoint_left.1 R.disjoint h.1 hx.1).elim
    · exact h.2
  have hRpositive : P.extension.old '' R.positive ⊆ C.positive := by
    rintro _ ⟨x, hx, rfl⟩
    have hxSupport : x ∈ R.support := Or.inl hx
    have hxb : x ≠ F.distinguished := by
      intro h
      subst x
      exact Set.disjoint_left.1 R.disjoint hx hbRneg
    have hsame := hSameOnSupport x hxSupport hxb
    rcases hsame with h | h
    · exact h.2
    · exact (Set.disjoint_left.1 R.disjoint hx h.1).elim
  refine ⟨R, ⟨hR, hbRneg, hRnegative, hRpositive⟩, ?_⟩
  intro T hTprops
  rcases hTprops with ⟨hT, hbTneg, hTnegative, hTpositive⟩
  have hTsupportSub : T.support ⊆ insert F.distinguished S := by
    intro x hx
    rcases hx with hxpos | hxneg
    · right
      exact Or.inl (hTpositive ⟨x, hxpos, rfl⟩)
    · by_cases hxb : x = F.distinguished
      · exact Or.inl hxb
      · right
        exact Or.inr (hTnegative ⟨x, ⟨hxneg, by simpa using hxb⟩, rfl⟩)
  have hTU : F.matroid.underlying.IsCircuit T.support :=
    (F.matroid.underlying_spec.2 T.support).mpr ⟨T, hT, rfl⟩
  have hTsupport : T.support = F.matroid.underlying.fundCircuit F.distinguished S :=
    hTU.eq_fundCircuit_of_subset hSunderlying hTsupportSub
  have hsubTR : T.support ⊆ R.support := by rw [hTsupport, hRsupport]
  rcases F.matroid.eq_or_eq_neg_of_support_subset hT hR hsubTR with hEq | hEq
  · exact hEq
  · have : F.distinguished ∈ R.positive := by simpa [hEq] using hbTneg
    exact (Set.disjoint_left.1 R.disjoint this hbRneg).elim

/-- Corollary 8.3: deleting the old point `b` from the extension preserves acyclicity. -/
theorem delete_distinguished_isAcyclic [Fintype M] [Fintype β] :
    (P.extension.matroid.delete (P.extension.old F.distinguished)).IsAcyclic := by
  intro C hC
  by_contra hCnegative
  have hCnegativeEmpty : C.negative = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hCnegative
  let f : {x : β // x ≠ P.extension.old F.distinguished} ↪ β :=
    Function.Embedding.subtype _
  change P.extension.matroid.IsCircuit (C.map f) at hC
  have hMapNegative : (C.map f).negative = ∅ := by
    simp [hCnegativeEmpty]
  have hOldNotSupport :
      P.extension.old F.distinguished ∉ (C.map f).support := by
    intro hb
    rw [SignedSubset.support_map] at hb
    obtain ⟨x, _, hx⟩ := hb
    exact x.property hx
  by_cases hp : P.extension.new ∈ (C.map f).support
  · have hpPositive : P.extension.new ∈ (C.map f).positive := by
      rcases hp with hp | hp
      · exact hp
      · rw [hMapNegative] at hp
        exact hp.elim
    have hNegCircuit : P.extension.matroid.IsCircuit (-(C.map f)) :=
      P.extension.matroid.neg_isCircuit hC
    have hpNegative : P.extension.new ∈ (-(C.map f)).negative := by
      simpa using hpPositive
    have hOldNotNegSupport :
        P.extension.old F.distinguished ∉ (-(C.map f)).support := by
      simpa using hOldNotSupport
    obtain ⟨R, hR, _, _, hRpositive⟩ :=
      (P.circuit_transfer_unique hNegCircuit hpNegative hOldNotNegSupport).exists
    have hRpositiveEmpty : R.positive = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hximage := hRpositive ⟨x, hx, rfl⟩
      change P.extension.old x ∈ (C.map f).negative at hximage
      rw [hMapNegative] at hximage
      exact hximage
    exact (F.acyclic.positive_nonempty hR).ne_empty hRpositiveEmpty
  · have hSupportOld : (C.map f).support ⊆ Set.range P.extension.old := by
      intro x hx
      have hxground : x ∈ Set.range P.extension.old ∪ {P.extension.new} := by
        rw [P.extension.ground_eq]
        trivial
      rcases hxground with hxold | hxnew
      · exact hxold
      · have hxeq : x = P.extension.new := by simpa using hxnew
        apply (hp ?_).elim
        rwa [← hxeq]
    have hrecover :
        ((C.map f).comap P.extension.old).map P.extension.old = C.map f :=
      SignedSubset.map_comap_of_support_subset_range _ _ hSupportOld
    have hOldCircuit :
        F.matroid.IsCircuit ((C.map f).comap P.extension.old) := by
      apply (P.extension.old_isCircuit_iff _).mp
      simpa [hrecover] using hC
    have hOldNegativeEmpty :
        ((C.map f).comap P.extension.old).negative = ∅ := by
      rw [SignedSubset.comap_negative, hMapNegative]
      simp
    exact (F.acyclic hOldCircuit).ne_empty hOldNegativeEmpty

/-- Corollary 8.4: convex-hull membership transfers from the perturbation `p` back to `b`. -/
theorem distinguished_memConvexHull_of_new
    [Fintype M] [Fintype β]
    (ε : Set M) (hbε : F.distinguished ∉ ε)
    (hp : P.extension.matroid.MemConvexHull P.extension.new
      (P.extension.old '' ε)) :
    F.matroid.MemConvexHull F.distinguished ε := by
  rcases hp with hp | ⟨C, hC, hCpos, hCneg⟩
  · obtain ⟨x, _, hx⟩ := hp
    exact (P.extension.new_not_old ⟨x, hx⟩).elim
  have hpCneg : P.extension.new ∈ C.negative := by
    rw [hCneg]
    simp
  have hbC : P.extension.old F.distinguished ∉ C.support := by
    intro hb
    rcases hb with hbpos | hbneg
    · obtain ⟨x, hxε, hx⟩ := hCpos hbpos
      exact hbε (P.extension.old.injective hx.symm ▸ hxε)
    · have holdnew : P.extension.old F.distinguished = P.extension.new := by
        simpa [hCneg] using hbneg
      exact P.extension.new_not_old ⟨F.distinguished, holdnew⟩
  obtain ⟨R, hR, hbRneg, hRneg, hRpos⟩ :=
    (P.circuit_transfer_unique hC hpCneg hbC).exists
  have hRnegEq : R.negative = {F.distinguished} := by
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hxb : x = F.distinguished
      · simp [hxb]
      have hximage : P.extension.old x ∈
          P.extension.old '' (R.negative \ {F.distinguished}) :=
        ⟨x, ⟨hx, by simpa using hxb⟩, rfl⟩
      have hxCneg := hRneg hximage
      have hxnew : P.extension.old x = P.extension.new := by
        simpa [hCneg] using hxCneg
      exact (P.extension.new_not_old ⟨x, hxnew⟩).elim
    · simpa using hbRneg
  refine Or.inr ⟨R, hR, ?_, hRnegEq⟩
  intro x hx
  have hximage : P.extension.old x ∈ P.extension.old '' R.positive := ⟨x, hx, rfl⟩
  obtain ⟨y, hyε, hxy⟩ := hCpos (hRpos hximage)
  exact P.extension.old.injective hxy.symm ▸ hyε

/-- The framework obtained by deleting the old distinguished point and using the new point as the
distinguished element. -/
noncomputable def deletedFramework
    [Fintype M] [Fintype β] : Framework I
      {x : β // x ≠ P.extension.old F.distinguished} := by
  let f : {x : β // x ≠ P.extension.old F.distinguished} ↪ β :=
    Function.Embedding.subtype _
  let vertex' : I ↪ {x : β // x ≠ P.extension.old F.distinguished} :=
    { toFun := fun i ↦ ⟨P.extension.old (F.vertex i), by
          intro h
          exact F.distinguished_notMem_basis
            ⟨i, P.extension.old.injective h⟩⟩
      inj' := fun i j h ↦ F.vertex.injective
        (P.extension.old.injective (congrArg Subtype.val h)) }
  let new' : {x : β // x ≠ P.extension.old F.distinguished} :=
    ⟨P.extension.new, by
      intro h
      exact P.extension.new_not_old ⟨F.distinguished, h.symm⟩⟩
  have hrangeImage :
      f '' Set.range vertex' = P.extension.old '' Set.range F.vertex := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨F.vertex i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨vertex' i, ⟨i, rfl⟩, rfl⟩
  have hbasisL :
      P.extension.matroid.IsBasis (P.extension.old '' Set.range F.vertex) := by
    exact P.isLexicographic.2.2.1 (Set.range F.vertex) |>.mp F.basis_isBasis
  have hbasisDelete :
      (P.extension.matroid.delete
        (P.extension.old F.distinguished)).IsBasis (Set.range vertex') := by
    change (P.extension.matroid.restrict f).IsBasis (Set.range vertex')
    apply P.extension.matroid.restrict_isBasis_of_isBasis_image
    simpa [hrangeImage] using hbasisL
  have hnewNotRange : new' ∉ Set.range vertex' := by
    rintro ⟨i, hi⟩
    exact P.extension.new_not_old
      ⟨F.vertex i, congrArg Subtype.val hi⟩
  have hnewConv :
      (P.extension.matroid.delete
        (P.extension.old F.distinguished)).MemConvexHull new'
        (Set.range vertex') := by
    obtain ⟨T, hT, hTpos, hTneg⟩ :
        ∃ T : SignedSubset M, F.matroid.IsCircuit T ∧
          T.positive ⊆ Set.range F.vertex ∧
            T.negative = {F.distinguished} := by
      rcases F.distinguished_mem_convexHull with hb | h
      · exact (F.distinguished_notMem_basis hb).elim
      · exact h
    let T' : SignedSubset β := T.map P.extension.old
    have hT' : P.extension.matroid.IsCircuit T' := by
      exact (P.extension.old_isCircuit_iff T).mpr hT
    have hbFundPos :
        P.extension.old F.distinguished ∈ P.fundamentalCircuit.positive := by
      exact ⟨F.distinguished, Or.inr rfl, rfl⟩
    have hbTneg : P.extension.old F.distinguished ∈ T'.negative := by
      exact ⟨F.distinguished, by simp [hTneg], rfl⟩
    have hopposite :
        P.fundamentalCircuit.OppositeAt T'
          (P.extension.old F.distinguished) :=
      Or.inl ⟨hbFundPos, hbTneg⟩
    have hpFundNeg : P.extension.new ∈ P.fundamentalCircuit.negative := by
      simp [fundamentalCircuit]
    have hpNotTpos : P.extension.new ∉ T'.positive := by
      rintro ⟨x, _, hx⟩
      exact P.extension.new_not_old ⟨x, hx⟩
    have hsurvives :
        OrientedMatroid.SurvivesFrom P.fundamentalCircuit T' P.extension.new :=
      Or.inr ⟨hpFundNeg, hpNotTpos⟩
    obtain ⟨W, hW, hWelim, hpW⟩ :=
      P.extension.matroid.strongElimination
        P.fundamentalCircuit_isCircuit hT' hopposite hsurvives
    have hWavoid :
        P.extension.old F.distinguished ∉ W.support := by
      intro hb
      rcases hb with hb | hb
      · exact (hWelim.1 hb).2 (Set.mem_singleton _)
      · exact (hWelim.2 hb).2 (Set.mem_singleton _)
    have hWposOldBasis :
        W.positive ⊆ P.extension.old '' Set.range F.vertex := by
      intro x hx
      have hx' := (hWelim.1 hx).1
      rcases hx' with hxFund | hxT
      · obtain ⟨y, hyRep, rfl⟩ := hxFund
        rcases hyRep with hyB | hyb
        · exact ⟨y, hyB.1, rfl⟩
        · have hyEq : y = F.distinguished := by simpa using hyb
          subst y
          exact ((hWelim.1 hx).2 rfl).elim
      · obtain ⟨y, hyT, rfl⟩ := hxT
        exact ⟨y, hTpos hyT, rfl⟩
    have hWnegSub : W.negative ⊆ {P.extension.new} := by
      intro x hx
      have hx' := (hWelim.2 hx).1
      rcases hx' with hxFund | hxT
      · simpa [fundamentalCircuit] using hxFund
      · obtain ⟨y, hyTneg, rfl⟩ := hxT
        have hyb : y = F.distinguished := by simpa [hTneg] using hyTneg
        subst y
        exact ((hWelim.2 hx).2 rfl).elim
    have hpWneg : P.extension.new ∈ W.negative := by
      rcases hpW with hpWpos | hpWneg
      · obtain ⟨y, _, hy⟩ := hWposOldBasis hpWpos
        exact (P.extension.new_not_old ⟨y, hy⟩).elim
      · exact hpWneg
    have hWnegEq : W.negative = {P.extension.new} :=
      Set.Subset.antisymm hWnegSub (by simpa using hpWneg)
    let W' : SignedSubset {x : β // x ≠ P.extension.old F.distinguished} :=
      W.comap f
    have hWrange :
        W.support ⊆ Set.range f := by
      intro x hx
      have hxne : x ≠ P.extension.old F.distinguished := fun h ↦ hWavoid (h ▸ hx)
      exact ⟨⟨x, hxne⟩, rfl⟩
    have hWrecover : W'.map f = W :=
      SignedSubset.map_comap_of_support_subset_range f W hWrange
    have hW'delete :
        (P.extension.matroid.delete
          (P.extension.old F.distinguished)).IsCircuit W' := by
      change P.extension.matroid.IsCircuit (W'.map f)
      simpa [hWrecover] using hW
    refine Or.inr ⟨W', hW'delete, ?_, ?_⟩
    · intro x hx
      have hxval : x.1 ∈ W.positive := by simpa [W', f] using hx
      obtain ⟨y, hyB, hy⟩ := hWposOldBasis hxval
      obtain ⟨j, hj⟩ := hyB
      subst y
      refine ⟨j, Subtype.ext ?_⟩
      change P.extension.old (F.vertex j) = x.1
      exact hy
    · ext x
      constructor
      · intro hx
        have hxval : x.1 ∈ W.negative := by simpa [W', f] using hx
        have hxnew : x.1 = P.extension.new := by simpa [hWnegEq] using hxval
        exact Set.mem_singleton_iff.mpr (Subtype.ext hxnew)
      · intro hx
        have hxnew : x = new' := Set.mem_singleton_iff.mp hx
        subst x
        simpa [W', f, new'] using hpWneg
  exact {
    matroid := P.extension.matroid.delete (P.extension.old F.distinguished)
    vertex := vertex'
    distinguished := new'
    basis_isBasis := hbasisDelete
    distinguished_notMem_basis := hnewNotRange
    acyclic := P.delete_distinguished_isAcyclic
    distinguished_mem_convexHull := hnewConv }

/-- Lift the original coloring through the old-element embedding into the deleted framework. -/
noncomputable def deletedColoring
    [Fintype M] [Fintype β] [DecidableEq V] (D : SimplexFamily I V)
    (c : Coloring D F) : Coloring D P.deletedFramework :=
  fun x ↦
    ⟨⟨P.extension.old (c x).1, by
        intro h
        exact (c x).property (P.extension.old.injective h)⟩,
      by
        intro h
        have hval := congrArg Subtype.val h
        change P.extension.old (c x).1 = P.extension.new at hval
        exact P.extension.new_not_old ⟨(c x).1, hval⟩⟩

@[simp]
theorem deletedFramework_vertex_val
    [Fintype M] [Fintype β] (i : I) :
    (P.deletedFramework.vertex i).1 = P.extension.old (F.vertex i) := by
  rfl

@[simp]
theorem deletedFramework_distinguished_val
    [Fintype M] [Fintype β] :
    P.deletedFramework.distinguished.1 = P.extension.new := by
  rfl

@[simp]
theorem deletedColoring_val
    [Fintype M] [Fintype β] [DecidableEq V] (D : SimplexFamily I V)
    (c : Coloring D F) (x : D.vertexSet) :
    ((P.deletedColoring D c x).1 :
      {y : β // y ≠ P.extension.old F.distinguished}).1 =
        P.extension.old (c x).1 := by
  rfl

set_option maxHeartbeats 800000 in
/-- The completed image in the deleted framework is exactly the old-element lift of the original
completed image. -/
theorem image_deleted_completedImage
    [Fintype M] [Fintype β] [Fintype V] [DecidableEq V]
    (D : SimplexFamily I V) (c : Coloring D F)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    let f : {x : β // x ≠ P.extension.old F.distinguished} ↪ β :=
      Function.Embedding.subtype _
    f '' (completedImage D P.deletedFramework (P.deletedColoring (V := V) D c)
        C tau htau : Set _) =
      P.extension.old '' (completedImage D F c C tau htau : Set M) := by
  dsimp only
  ext x
  simp only [Set.mem_image, Finset.mem_coe, completedImage, Finset.mem_union,
    colorImage, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨y, (⟨v, hvy⟩ | ⟨i, hi, hiy⟩), hyx⟩
    · refine ⟨(c ⟨v.1, mem_vertexSet_of_mem_simplex D htau v.2⟩).1,
          Or.inl ⟨v, rfl⟩, ?_⟩
      rw [← hyx]
      exact congrArg Subtype.val hvy
    · refine ⟨F.vertex i, Or.inr ⟨i, hi, rfl⟩, ?_⟩
      rw [← hyx]
      exact congrArg Subtype.val hiy
  · rintro ⟨m, (⟨v, hvm⟩ | ⟨i, hi, him⟩), hmx⟩
    · let y := (P.deletedColoring (V := V) D c
          ⟨v.1, mem_vertexSet_of_mem_simplex D htau v.2⟩).1
      refine ⟨y, Or.inl ⟨v, rfl⟩, ?_⟩
      change y.1 = x
      rw [deletedColoring_val, hvm, hmx]
    · let y := P.deletedFramework.vertex i
      refine ⟨y, Or.inr ⟨i, hi, rfl⟩, ?_⟩
      change y.1 = x
      rw [deletedFramework_vertex_val, him, hmx]

/-- Lemma 8.1 makes the deleted framework nondegenerate: a convexity circuit for fewer than
`|I|` old elements would be a circuit through the new point with support of size at most `|I|`. -/
theorem deletedFramework_isNondegenerate
    [Fintype M] [Fintype β] : P.deletedFramework.IsNondegenerate := by
  intro X hpX hXcard hconv
  rcases hconv with hp | ⟨C, hC, hCpos, hCneg⟩
  · exact hpX hp
  let f : {x : β // x ≠ P.extension.old F.distinguished} ↪ β :=
    Function.Embedding.subtype _
  change P.extension.matroid.IsCircuit (C.map f) at hC
  have hpCneg : P.deletedFramework.distinguished ∈ C.negative := by
    rw [hCneg]
    simp
  have hpMapNeg : P.extension.new ∈ (C.map f).negative := by
    exact ⟨P.deletedFramework.distinguished, hpCneg, rfl⟩
  have hlower : Fintype.card I + 1 ≤ C.support.ncard := by
    have h := P.new_mem_circuit_card hC (Or.inr hpMapNeg)
    rw [SignedSubset.support_map,
      Set.ncard_image_of_injective _ f.injective] at h
    exact h
  have hsupport : C.support ⊆ (X : Set _) ∪ {P.deletedFramework.distinguished} := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hCpos hx)
    · have hxnew : x = P.deletedFramework.distinguished := by
        simpa [hCneg] using hx
      exact Or.inr (by simp [hxnew])
  have hupper : C.support.ncard ≤ X.card + 1 := by
    calc
      C.support.ncard ≤
          ((X : Set {x : β // x ≠ P.extension.old F.distinguished}) ∪
            {P.deletedFramework.distinguished}).ncard :=
        Set.ncard_le_ncard hsupport (Set.toFinite _)
      _ ≤
          (X : Set {x : β // x ≠ P.extension.old F.distinguished}).ncard +
            ({P.deletedFramework.distinguished} :
              Set {x : β // x ≠ P.extension.old F.distinguished}).ncard :=
        Set.ncard_union_le _ _
      _ = X.card + 1 := by simp
  omega

set_option maxHeartbeats 800000 in
/-- A good completed image found after deletion transfers back to a good completed image in the
original framework. -/
theorem goodBasis_of_deleted_goodBasis
    [Fintype M] [Fintype β] [Fintype V] [DecidableEq V]
    (D : SimplexFamily I V) (c : Coloring D F)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C)
    (hgood : P.deletedFramework.matroid.IsGoodBasis
      P.deletedFramework.distinguished
      (completedImage D P.deletedFramework (P.deletedColoring (V := V) D c)
        C tau htau : Set _)) :
    F.matroid.IsGoodBasis F.distinguished
      (completedImage D F c C tau htau : Set M) := by
  let f : {x : β // x ≠ P.extension.old F.distinguished} ↪ β :=
    Function.Embedding.subtype _
  let eps' : Finset {x : β // x ≠ P.extension.old F.distinguished} :=
    completedImage D P.deletedFramework (P.deletedColoring (V := V) D c)
      C tau htau
  let eps : Finset M := completedImage D F c C tau htau
  have himage : f '' (eps' : Set _) = P.extension.old '' (eps : Set M) := by
    simpa [f, eps', eps] using P.image_deleted_completedImage D c C tau htau
  have hindL : P.extension.matroid.IsIndependent
      (P.extension.old '' (eps : Set M)) := by
    have hind' : P.deletedFramework.matroid.IsIndependent (eps' : Set _) := by
      simpa [eps'] using hgood.1.1
    change (P.extension.matroid.restrict f).IsIndependent (eps' : Set _) at hind'
    have hindImage :=
      (P.extension.matroid.restrict_isIndependent_iff f (eps' : Set _)).mp hind'
    simpa [himage] using hindImage
  have hindF : F.matroid.IsIndependent (eps : Set M) := by
    intro R hR hRsub
    apply hindL ((P.extension.old_isCircuit_iff R).mpr hR)
    rw [SignedSubset.support_map]
    exact Set.image_mono hRsub
  have hcard' : eps'.card = Fintype.card I := by
    apply P.deletedFramework.card_eq_card_index_of_isBasis eps'
    simpa [eps'] using hgood.1
  have hcardEq : eps'.card = eps.card := by
    have hncard := congrArg Set.ncard himage
    simpa [Set.ncard_image_of_injective] using hncard
  have hcard : eps.card = Fintype.card I := hcardEq.symm.trans hcard'
  have hbasis : F.matroid.IsBasis (eps : Set M) := by
    refine ⟨hindF, ?_⟩
    intro X hX hsub
    have hXU := F.matroid.isIndependent_iff_underlying_indep.mp hX
    obtain ⟨B, hB, hXB⟩ := hXU.exists_isBase_superset
    have hB0 : F.matroid.underlying.IsBase (Set.range F.vertex) :=
      F.matroid.isBasis_iff_underlying_isBase.mp F.basis_isBasis
    have hBfinite : B.Finite :=
      hB0.finite_of_finite (Set.finite_range F.vertex) hB
    have hBcard : B.ncard = Fintype.card I := by
      rw [hB.ncard_eq_ncard_of_isBase hB0,
        Set.ncard_range_of_injective F.vertex.injective]
      simp
    have hepsB : (eps : Set M) = B := by
      apply Set.eq_of_subset_of_ncard_le (hsub.trans hXB) (by
        have hepsNcard : (eps : Set M).ncard = Fintype.card I := by
          simpa using hcard
        omega) hBfinite
    intro x hx
    have hxB := hXB hx
    rwa [← hepsB] at hxB
  have hbNotEps : F.distinguished ∉ eps := by
    intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · simp only [colorImage, Finset.mem_image, Finset.mem_attach] at hb
      obtain ⟨v, _, hvb⟩ := hb
      exact (c ⟨v.1, mem_vertexSet_of_mem_simplex D htau v.2⟩).property hvb
    · simp only [Finset.mem_image] at hb
      obtain ⟨i, _, hiv⟩ := hb
      exact F.distinguished_notMem_basis ⟨i, hiv⟩
  have hpL : P.extension.matroid.MemConvexHull P.extension.new
      (P.extension.old '' (eps : Set M)) := by
    rcases hgood.2 with hp | ⟨R, hR, hRpos, hRneg⟩
    · have hpImage : P.extension.new ∈ f '' (eps' : Set _) := by
        refine ⟨P.deletedFramework.distinguished, ?_, ?_⟩
        · simpa [eps'] using hp
        · exact P.deletedFramework_distinguished_val
      have hpOld : P.extension.new ∈ P.extension.old '' (eps : Set M) := by
        rwa [himage] at hpImage
      obtain ⟨m, _, hm⟩ := hpOld
      exact (P.extension.new_not_old ⟨m, hm⟩).elim
    · refine Or.inr ⟨R.map f, ?_, ?_, ?_⟩
      · exact hR
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [← himage]
        exact ⟨y, hRpos hy, rfl⟩
      · rw [SignedSubset.map_negative, hRneg]
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          have hynew : y = P.deletedFramework.distinguished := by simpa using hy
          subst y
          change P.deletedFramework.distinguished.1 = P.extension.new
          exact P.deletedFramework_distinguished_val
        · intro hx
          have hxnew : x = P.extension.new := by simpa using hx
          subst x
          exact ⟨P.deletedFramework.distinguished, by simp,
            P.deletedFramework_distinguished_val⟩
  exact ⟨hbasis, P.distinguished_memConvexHull_of_new (eps : Set M) hbNotEps hpL⟩

end PerturbationSetup

section MainTheorem

variable [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  [DecidableEq M]

/-- Theorem 8.5: the general matroid-coloring theorem, without nondegeneracy or parity. -/
theorem theorem8_5
    [Fintype M] (D : SimplexFamily I V) (F : Framework I M)
    (hchain : D.IsChainSimplex) (c : Coloring D F) :
    ∃ C : Finset I, ∃ τ : Finset V, IsSolution D F c C τ := by
  let : DecidableEq (M ⊕ Unit) := Classical.decEq _
  obtain ⟨P, _⟩ := exists_perturbationSetup F
  let F' := P.deletedFramework
  let c' : Coloring D F' := P.deletedColoring (V := V) D c
  have hnd' : F'.IsNondegenerate := by
    simpa [F'] using P.deletedFramework_isNondegenerate
  have hnonempty := (theorem6_5 D F' hchain hnd' c').1
  obtain ⟨p, hp⟩ := hnonempty
  rcases p with ⟨C, tau⟩
  have hsol' : IsSolution D F' c' C tau :=
    (Finset.mem_filter.mp hp).2
  obtain ⟨htau, hC, hcard, hgood⟩ := hsol'
  refine ⟨C, tau, htau, hC, hcard, ?_⟩
  apply P.goodBasis_of_deleted_goodBasis D c C tau htau
  simpa [F', c'] using hgood

end MainTheorem

end MatroidColoring

end BeyondSperner
