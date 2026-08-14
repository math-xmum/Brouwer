import BeyondSperner.OrientedMatroid.LexicographicExtensionConstruction
import BeyondSperner.OrientedMatroid.Todd

/-!
# Secondary cocircuits of a lexicographic extension

This file discharges the last rank-two (coline) obligation in the
lexicographic-extension construction.  It is deliberately separated from the
conditional assembly: the latter only needs an orthogonal signing of every
ordinary cocircuit support, while this file proves that the required signing
exists for the genuinely new supports avoiding the extension point.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid

variable {α : Type*}

/-- The complement of an ordinary cocircuit is a closed set (a hyperplane).
This small rank-free formulation is the only hyperplane API needed below. -/
private theorem cocircuit_compl_closure_eq [Finite α]
    {U : Matroid α} {K : Set α} (hK : U.IsCocircuit K) :
    U.closure (U.E \ K) = U.E \ K := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxE : x ∈ U.E := U.closure_subset_ground _ hx
    refine ⟨hxE, ?_⟩
    intro hxK
    have hmin := Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hK
    let T : Set α := K \ {x}
    have hcomp : U.E \ T = insert x (U.E \ K) := by
      ext y
      by_cases hyx : y = x
      · subst y
        simp [T, hxE, hxK]
      · simp [T, hyx]
    have hTnonspanning : ¬ U.Spanning (U.E \ T) := by
      rw [hcomp]
      intro hsp
      apply hmin.1
      refine ⟨?_, sdiff_subset⟩
      rw [← U.closure_insert_eq_of_mem_closure hx]
      exact hsp.closure_eq
    have hKT : K ⊆ T := hmin.2 hTnonspanning sdiff_subset
    exact (hKT hxK).2 rfl
  · exact U.subset_closure _ sdiff_subset

/-- Every nonspanning set is avoided by some cocircuit. -/
private theorem exists_isCocircuit_subset_compl_of_not_spanning
    [Finite α] {U : Matroid α} {H : Set α} (hHE : H ⊆ U.E)
    (hH : ¬ U.Spanning H) :
    ∃ K : Set α, U.IsCocircuit K ∧ K ⊆ U.E \ H := by
  obtain ⟨I, hIH⟩ := U.exists_isBasis H hHE
  obtain ⟨B, hB, hIB⟩ := hIH.indep.exists_isBase_superset
  have hnotBI : ¬ B ⊆ I := by
    intro hBI
    apply hH
    exact hB.spanning_of_superset (hBI.trans hIH.subset) hHE
  obtain ⟨e, heB, heI⟩ := Set.not_subset.mp hnotBI
  let K : Set α := U.fundCocircuit e B
  have hK : U.IsCocircuit K := U.fundCocircuit_isCocircuit heB hB
  refine ⟨K, hK, ?_⟩
  intro x hxK
  refine ⟨hK.subset_ground hxK, ?_⟩
  intro hxH
  have hfundInter : K ∩ B = {e} := by
    simpa [K] using U.fundCocircuit_inter_eq heB
  have hIKcompl : I ⊆ U.E \ K := by
    intro i hiI
    refine ⟨hIH.indep.subset_ground hiI, ?_⟩
    intro hiK
    have hiEq : i = e := by
      have : i ∈ K ∩ B := ⟨hiK, hIB hiI⟩
      simpa [hfundInter] using this
    exact heI (hiEq ▸ hiI)
  have hxClosureI : x ∈ U.closure I := hIH.subset_closure hxH
  have hxClosureCompl : x ∈ U.closure (U.E \ K) :=
    U.closure_subset_closure hIKcompl hxClosureI
  rw [cocircuit_compl_closure_eq hK] at hxClosureCompl
  exact hxClosureCompl.2 hxK

/-- In a genuinely new cocircuit of a principal extension which avoids the
new point, the old complement is a closed nonspanning set of corank at least
two.  The last clause is the rank-free form of the corank-two assertion. -/
private theorem strict_old_compl_properties [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {L : Set (α ⊕ Unit)}
    (hL : (PrincipalExtension.matroid U A hUE hA).IsCocircuit L)
    (hpL : PrincipalExtension.new α ∉ L)
    (hstrict : ¬ U.IsCocircuit (PrincipalExtension.oldPart L)) :
    let H := U.E \ PrincipalExtension.oldPart L
    ¬ U.Spanning H ∧ U.closure H = H ∧
      ∀ a ∈ PrincipalExtension.oldPart L, ¬ U.Spanning (insert a H) := by
  classical
  let U' := PrincipalExtension.matroid U A hUE hA
  let K : Set α := PrincipalExtension.oldPart L
  let H : Set α := U.E \ K
  have hshape : Sum.inl '' K = L :=
    PrincipalExtension.image_oldPart_eq_of_notMem L hpL
  have hLmin := Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hL
  have hHnonspanning : ¬ U.Spanning H := by
    intro hsp
    have hspImage : U'.Spanning (Sum.inl '' H) :=
      (PrincipalExtension.matroid_spanning_image_inl_iff
        U A hUE hA H).mpr hsp
    apply hLmin.1
    apply hspImage.superset
    · rintro _ ⟨x, hxH, rfl⟩
      refine ⟨by simp, ?_⟩
      intro hxL
      have hxK : x ∈ K := by
        rw [← hshape] at hxL
        simpa using hxL
      exact hxH.2 hxK
  have hHclosed : U.closure H = H := by
    apply Set.Subset.antisymm
    · intro x hxClosure
      have hxE : x ∈ U.E := U.closure_subset_ground _ hxClosure
      have hxExtClosure : Sum.inl x ∈ U'.closure (Sum.inl '' H) :=
        (PrincipalExtension.inl_mem_matroid_closure_image_inl_iff
          U A hUE hA H x).mpr hxClosure
      have hImageSub : Sum.inl '' H ⊆ U'.E \ L := by
        rintro _ ⟨y, hyH, rfl⟩
        refine ⟨by simp [U'], ?_⟩
        intro hyL
        have hyK : y ∈ K := by
          rw [← hshape] at hyL
          simpa using hyL
        exact hyH.2 hyK
      have hxExtCompl : Sum.inl x ∈ U'.closure (U'.E \ L) :=
        U'.closure_subset_closure hImageSub hxExtClosure
      rw [cocircuit_compl_closure_eq hL] at hxExtCompl
      refine ⟨hxE, ?_⟩
      intro hxK
      exact hxExtCompl.2 (hshape ▸ ⟨x, hxK, rfl⟩)
    · exact U.subset_closure _ sdiff_subset
  refine ⟨hHnonspanning, hHclosed, ?_⟩
  intro a haK hInsertSpanning
  apply hstrict
  rw [Matroid.isCocircuit_iff_minimal_compl_nonspanning,
    minimal_subset_iff]
  refine ⟨by simpa [H, K] using hHnonspanning, ?_⟩
  intro T hTnonspanning hTK
  apply Set.Subset.antisymm
  · intro x hxK
    by_contra hxT
    have hxE : x ∈ U.E := by simp [hUE]
    have hxNotClosure : x ∉ U.closure H := by
      rw [hHclosed]
      exact fun hxH ↦ hxH.2 hxK
    have hxClosureInsert : x ∈ U.closure (insert a H) := by
      rw [hInsertSpanning.closure_eq]
      exact hxE
    have hClosureEq : U.closure (insert x H) =
        U.closure (insert a H) :=
      U.closure_insert_congr ⟨hxClosureInsert, hxNotClosure⟩
    have hInsertXSpanning : U.Spanning (insert x H) := by
      refine ⟨?_, insert_subset hxE sdiff_subset⟩
      rw [hClosureEq]
      exact hInsertSpanning.closure_eq
    apply hTnonspanning
    apply hInsertXSpanning.superset
    · intro y hy
      rcases hy with rfl | hyH
      · exact ⟨hxE, hxT⟩
      · exact ⟨hyH.1, fun hyT ↦ hyH.2 (hTK hyT)⟩
  · exact hTK

/-- Two distinct old cocircuits contained in a strict secondary support and
distinguished by one element already cover that support.  The proof is the
rank-two argument in circuit language: if the new point together with the
intersection of the two old hyperplanes spanned, eliminating the new point
from two closure circuits would contradict closedness of one hyperplane. -/
private theorem cocircuit_union_eq_strict_oldPart [Finite α]
    (U : Matroid α) (A : Set α) (hUE : U.E = Set.univ) (hA : U.Indep A)
    {L : Set (α ⊕ Unit)}
    (hL : (PrincipalExtension.matroid U A hUE hA).IsCocircuit L)
    (hpL : PrincipalExtension.new α ∉ L)
    {X Y : Set α} (hX : U.IsCocircuit X) (hY : U.IsCocircuit Y)
    (hXK : X ⊆ PrincipalExtension.oldPart L)
    (hYK : Y ⊆ PrincipalExtension.oldPart L)
    {a : α} (haX : a ∉ X) (haY : a ∈ Y) :
    X ∪ Y = PrincipalExtension.oldPart L := by
  classical
  let U' := PrincipalExtension.matroid U A hUE hA
  let K : Set α := PrincipalExtension.oldPart L
  let HX : Set α := U.E \ X
  let HY : Set α := U.E \ Y
  let Z : Set α := U.E \ (X ∪ Y)
  have hshape : Sum.inl '' K = L :=
    PrincipalExtension.image_oldPart_eq_of_notMem L hpL
  have hXclosed : U.closure HX = HX := by
    simpa [HX] using cocircuit_compl_closure_eq hX
  have hYclosed : U.closure HY = HY := by
    simpa [HY] using cocircuit_compl_closure_eq hY
  have haE : a ∈ U.E := hY.subset_ground haY
  have haHX : a ∈ HX := ⟨haE, haX⟩
  have haNotHY : a ∉ HY := fun ha ↦ ha.2 haY
  have hnotXY : ¬ X ⊆ Y := by
    intro hXY
    have hEq : X = Y := hX.eq_of_subset_isCircuit hY hXY
    exact haX (hEq ▸ haY)
  obtain ⟨b, hbX, hbY⟩ := Set.not_subset.mp hnotXY
  have hbE : b ∈ U.E := hX.subset_ground hbX
  have hbHY : b ∈ HY := ⟨hbE, hbY⟩
  have hbNotHX : b ∉ HX := fun hb ↦ hb.2 hbX
  have hab : a ≠ b := fun hab ↦ hbY (hab ▸ haY)
  have hZHX : Z ⊆ HX := by
    intro x hx
    exact ⟨hx.1, fun hxX ↦ hx.2 (Or.inl hxX)⟩
  have hZHY : Z ⊆ HY := by
    intro x hx
    exact ⟨hx.1, fun hxY ↦ hx.2 (Or.inr hxY)⟩
  have haNotClosureZ : a ∉ U.closure Z := by
    intro ha
    have : a ∈ U.closure HY :=
      U.closure_subset_closure hZHY ha
    rw [hYclosed] at this
    exact haNotHY this
  have hbNotClosureZ : b ∉ U.closure Z := by
    intro hb
    have : b ∈ U.closure HX :=
      U.closure_subset_closure hZHX hb
    rw [hXclosed] at this
    exact hbNotHX this
  have haNotClosureInsertB : a ∉ U.closure (insert b Z) := by
    intro ha
    have hsub : insert b Z ⊆ HY := insert_subset hbHY hZHY
    have : a ∈ U.closure HY := U.closure_subset_closure hsub ha
    rw [hYclosed] at this
    exact haNotHY this
  have hSsubK : X ∪ Y ⊆ K := union_subset hXK hYK
  apply Set.Subset.antisymm hSsubK
  have hLmin := Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hL
  have hImageSub : Sum.inl '' (X ∪ Y) ⊆ L := by
    rw [← hshape]
    exact Set.image_mono hSsubK
  have hComplShape : U'.E \ (Sum.inl '' (X ∪ Y)) =
      insert (PrincipalExtension.new α) (Sum.inl '' Z) := by
    ext z
    rcases z with x | u
    · simp [U', Z, hUE, PrincipalExtension.new]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [U', PrincipalExtension.new]
  have hNonspanning : ¬ U'.Spanning
      (U'.E \ (Sum.inl '' (X ∪ Y))) := by
    rw [hComplShape]
    intro hsp
    have haClosure : Sum.inl a ∈
        U'.closure (insert (PrincipalExtension.new α) (Sum.inl '' Z)) := by
      rw [hsp.closure_eq]
      simp [U']
    have hbClosure : Sum.inl b ∈
        U'.closure (insert (PrincipalExtension.new α) (Sum.inl '' Z)) := by
      rw [hsp.closure_eq]
      simp [U']
    have haNotSet : Sum.inl a ∉
        insert (PrincipalExtension.new α) (Sum.inl '' Z) := by
      intro ha
      rcases ha with ha | ⟨x, hxZ, hxa⟩
      · simp [PrincipalExtension.new] at ha
      · have : x = a := Sum.inl_injective hxa
        subst x
        exact haNotClosureZ (U.subset_closure _ sdiff_subset hxZ)
    have hbNotSet : Sum.inl b ∉
        insert (PrincipalExtension.new α) (Sum.inl '' Z) := by
      intro hb
      rcases hb with hb | ⟨x, hxZ, hxb⟩
      · simp [PrincipalExtension.new] at hb
      · have : x = b := Sum.inl_injective hxb
        subst x
        exact hbNotClosureZ (U.subset_closure _ sdiff_subset hxZ)
    obtain ⟨Ca, hCaSub, hCa, haCa⟩ :=
      U'.exists_isCircuit_of_mem_closure haClosure haNotSet
    obtain ⟨Cb, hCbSub, hCb, hbCb⟩ :=
      U'.exists_isCircuit_of_mem_closure hbClosure hbNotSet
    have hpCa : PrincipalExtension.new α ∈ Ca := by
      by_contra hpCa
      have haOldClosure : Sum.inl a ∈ U'.closure (Sum.inl '' Z) := by
        have haCircuitClosure := hCa.mem_closure_sdiff_singleton_of_mem haCa
        have hsub : Ca \ {Sum.inl a} ⊆ Sum.inl '' Z := by
          intro z hz
          have hzSub := hCaSub hz.1
          rcases hzSub with hzEq | hzBase
          · exact (hz.2 hzEq).elim
          · rcases hzBase with hzNew | hzOld
            · exact (hpCa (hzNew ▸ hz.1)).elim
            · exact hzOld
        exact U'.closure_subset_closure hsub haCircuitClosure
      exact haNotClosureZ
        ((PrincipalExtension.inl_mem_matroid_closure_image_inl_iff
          U A hUE hA Z a).mp haOldClosure)
    have hpCb : PrincipalExtension.new α ∈ Cb := by
      by_contra hpCb
      have hbOldClosure : Sum.inl b ∈ U'.closure (Sum.inl '' Z) := by
        have hbCircuitClosure := hCb.mem_closure_sdiff_singleton_of_mem hbCb
        have hsub : Cb \ {Sum.inl b} ⊆ Sum.inl '' Z := by
          intro z hz
          have hzSub := hCbSub hz.1
          rcases hzSub with hzEq | hzBase
          · exact (hz.2 hzEq).elim
          · rcases hzBase with hzNew | hzOld
            · exact (hpCb (hzNew ▸ hz.1)).elim
            · exact hzOld
        exact U'.closure_subset_closure hsub hbCircuitClosure
      exact hbNotClosureZ
        ((PrincipalExtension.inl_mem_matroid_closure_image_inl_iff
          U A hUE hA Z b).mp hbOldClosure)
    have haNotCb : Sum.inl a ∉ Cb := by
      intro haCb
      have haSub := hCbSub haCb
      rcases haSub with hab' | haBase
      · exact hab (Sum.inl_injective hab')
      · rcases haBase with haNew | haOld
        · simp [PrincipalExtension.new] at haNew
        · obtain ⟨x, hxZ, hxa⟩ := haOld
          have : x = a := Sum.inl_injective hxa
          subst x
          exact haNotClosureZ (U.subset_closure _ sdiff_subset hxZ)
    obtain ⟨C, hCSub, hC, haC⟩ :=
      hCa.strong_elimination hCb hpCa hpCb haCa haNotCb
    have haOldClosure : Sum.inl a ∈
        U'.closure (Sum.inl '' insert b Z) := by
      have haCircuitClosure := hC.mem_closure_sdiff_singleton_of_mem haC
      have hsub : C \ {Sum.inl a} ⊆ Sum.inl '' insert b Z := by
        intro z hz
        have hzSub := hCSub hz.1
        have hzNotNew := hzSub.2
        rcases hzSub.1 with hzCa | hzCb
        · have hzCaSub := hCaSub hzCa
          rcases hzCaSub with hzEq | hzBase
          · exact (hz.2 hzEq).elim
          · rcases hzBase with hzNew | hzOld
            · exact (hzNotNew hzNew).elim
            · obtain ⟨x, hxZ, rfl⟩ := hzOld
              exact ⟨x, Or.inr hxZ, rfl⟩
        · have hzCbSub := hCbSub hzCb
          rcases hzCbSub with hzEq | hzBase
          · exact ⟨b, Or.inl rfl, hzEq.symm⟩
          · rcases hzBase with hzNew | hzOld
            · exact (hzNotNew hzNew).elim
            · obtain ⟨x, hxZ, rfl⟩ := hzOld
              exact ⟨x, Or.inr hxZ, rfl⟩
      exact U'.closure_subset_closure hsub haCircuitClosure
    exact haNotClosureInsertB
      ((PrincipalExtension.inl_mem_matroid_closure_image_inl_iff
        U A hUE hA (insert b Z) a).mp haOldClosure)
  have hLsub : L ⊆ Sum.inl '' (X ∪ Y) :=
    hLmin.2 hNonspanning hImageSub
  intro x hxK
  have hxL : Sum.inl x ∈ L := by
    rw [← hshape]
    exact ⟨x, hxK, rfl⟩
  have := hLsub hxL
  simpa using this

private theorem exists_opposite_ne_of_orthogonal_of_same
    {β : Type*} {C D : SignedSubset β} {p : β}
    (horth : C.Orthogonal D) (hsame : C.SameSignAt D p) :
    ∃ q, q ≠ p ∧ C.OppositeAt D q := by
  rcases horth with hdisjoint | ⟨u, hu, v, hv, _, hvOpp⟩
  · exact (Set.disjoint_left.1 hdisjoint
      hsame.mem_support_left hsame.mem_support_right).elim
  · exact ⟨v, fun hvp ↦ hsame.not_oppositeAt (hvp ▸ hvOpp), hvOpp⟩

private theorem exists_same_ne_of_orthogonal_of_opposite
    {β : Type*} {C D : SignedSubset β} {p : β}
    (horth : C.Orthogonal D) (hopp : C.OppositeAt D p) :
    ∃ q, q ≠ p ∧ C.SameSignAt D q := by
  rcases horth with hdisjoint | ⟨u, hu, _, _, huSame, _⟩
  · exact (Set.disjoint_left.1 hdisjoint
      hopp.mem_support_left hopp.mem_support_right).elim
  · exact ⟨u, fun hup ↦ huSame.not_oppositeAt (hup ▸ hopp), huSame⟩

private theorem sameSignAt_compose_left {X Y : SignedSubset α} {x : α}
    (hx : x ∈ X.support) : X.SameSignAt (X.compose Y) x := by
  rcases hx with hx | hx
  · exact Or.inl ⟨hx, Or.inl hx⟩
  · exact Or.inr ⟨hx, Or.inl hx⟩

private theorem sameSignAt_compose_right_of_conformal
    {X Y : SignedSubset α} {x : α}
    (hconformal : ∀ z, z ∈ X.support ∩ Y.support →
      X.SameSignAt Y z) (hxY : x ∈ Y.support) :
    Y.SameSignAt (X.compose Y) x := by
  by_cases hxX : x ∈ X.support
  · exact (SignedSubset.sameSignAt_comm.mp
      (hconformal x ⟨hxX, hxY⟩)).trans
        (sameSignAt_compose_left hxX)
  · rcases hxY with hxY | hxY
    · exact Or.inl ⟨hxY, Or.inr ⟨hxY, hxX⟩⟩
    · exact Or.inr ⟨hxY, Or.inr ⟨hxY, hxX⟩⟩

private theorem lexLift_relation_map_of_same_old
    (order : List α) {C : SignedSubset (α ⊕ Unit)}
    {D T : SignedSubset α} {x : α} (hDT : D.SameSignAt T x) :
    (C.SameSignAt (lexLift order D) (canonicalOld α x) →
        C.SameSignAt (T.map (canonicalOld α)) (canonicalOld α x)) ∧
      (C.OppositeAt (lexLift order D) (canonicalOld α x) →
        C.OppositeAt (T.map (canonicalOld α)) (canonicalOld α x)) := by
  have hLiftMap : (lexLift order D).SameSignAt
      (T.map (canonicalOld α)) (canonicalOld α x) := by
    rcases hDT with hDT | hDT
    · exact Or.inl ⟨
        (canonicalOld_mem_lexLift_positive_iff order D x).mpr hDT.1,
        ⟨x, hDT.2, rfl⟩⟩
    · exact Or.inr ⟨
        (canonicalOld_mem_lexLift_negative_iff order D x).mpr hDT.1,
        ⟨x, hDT.2, rfl⟩⟩
  exact ⟨fun h ↦ h.trans hLiftMap,
    fun h ↦ h.trans_sameSignAt hLiftMap⟩

/-- Eliminating the new coordinate from two conformal old covectors with
opposite localization signs preserves orthogonality to a circuit containing
the new coordinate. -/
private theorem orthogonal_map_compose_of_opposite_lexLifts
    (order : List α) {C : SignedSubset (α ⊕ Unit)}
    {X Y : SignedSubset α}
    (hpC : canonicalNew α ∈ C.support)
    (hCX : C.Orthogonal (lexLift order X))
    (hCY : C.Orthogonal (lexLift order Y))
    (hpXY : (lexLift order X).OppositeAt
      (lexLift order Y) (canonicalNew α))
    (hconformal : ∀ x, x ∈ X.support ∩ Y.support →
      X.SameSignAt Y x) :
    C.Orthogonal ((X.compose Y).map (canonicalOld α)) := by
  have hpX : canonicalNew α ∈ (lexLift order X).support :=
    hpXY.mem_support_left
  have hpY : canonicalNew α ∈ (lexLift order Y).support :=
    hpXY.mem_support_right
  rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem
      ⟨hpC, hpX⟩ with hpCXsame | hpCXopp
  · have hpCYopp : C.OppositeAt (lexLift order Y) (canonicalNew α) := by
      have hYCopp : (lexLift order Y).OppositeAt C (canonicalNew α) :=
        (SignedSubset.oppositeAt_comm.mp hpXY).trans_sameSignAt
          (SignedSubset.sameSignAt_comm.mp hpCXsame)
      exact SignedSubset.oppositeAt_comm.mp hYCopp
    obtain ⟨q, hqp, hqOpp⟩ :=
      exists_opposite_ne_of_orthogonal_of_same hCX hpCXsame
    obtain ⟨r, hrp, hrSame⟩ :=
      exists_same_ne_of_orthogonal_of_opposite hCY hpCYopp
    rcases q with q | u
    · rcases r with r | v
      · have hqX : q ∈ X.support :=
          (canonicalOld_mem_lexLift_support_iff order X q).mp
            hqOpp.mem_support_right
        have hqOppMap :=
          (lexLift_relation_map_of_same_old order
            (sameSignAt_compose_left (Y := Y) hqX)).2 hqOpp
        have hrY : r ∈ Y.support :=
          (canonicalOld_mem_lexLift_support_iff order Y r).mp
            hrSame.mem_support_right
        have hrSameMap :=
          (lexLift_relation_map_of_same_old order
            (sameSignAt_compose_right_of_conformal hconformal hrY)).1 hrSame
        exact SignedSubset.orthogonal_of_sameSignAt_of_oppositeAt
          ⟨hrSameMap.mem_support_left, hrSameMap.mem_support_right⟩
          ⟨hqOppMap.mem_support_left, hqOppMap.mem_support_right⟩
          hrSameMap hqOppMap
      · obtain rfl : v = () := Subsingleton.elim _ _
        exact (hrp rfl).elim
    · obtain rfl : u = () := Subsingleton.elim _ _
      exact (hqp rfl).elim

  · have hpCYsame : C.SameSignAt (lexLift order Y) (canonicalNew α) :=
      hpCXopp.sameSignAt_of_oppositeAt
        (SignedSubset.oppositeAt_comm.mp hpXY)
    obtain ⟨q, hqp, hqSame⟩ :=
      exists_same_ne_of_orthogonal_of_opposite hCX hpCXopp
    obtain ⟨r, hrp, hrOpp⟩ :=
      exists_opposite_ne_of_orthogonal_of_same hCY hpCYsame
    rcases q with q | u
    · rcases r with r | v
      · have hqX : q ∈ X.support :=
          (canonicalOld_mem_lexLift_support_iff order X q).mp
            hqSame.mem_support_right
        have hqSameMap :=
          (lexLift_relation_map_of_same_old order
            (sameSignAt_compose_left (Y := Y) hqX)).1 hqSame
        have hrY : r ∈ Y.support :=
          (canonicalOld_mem_lexLift_support_iff order Y r).mp
            hrOpp.mem_support_right
        have hrOppMap :=
          (lexLift_relation_map_of_same_old order
            (sameSignAt_compose_right_of_conformal hconformal hrY)).2 hrOpp
        exact SignedSubset.orthogonal_of_sameSignAt_of_oppositeAt
          ⟨hqSameMap.mem_support_left, hqSameMap.mem_support_right⟩
          ⟨hrOppMap.mem_support_left, hrOppMap.mem_support_right⟩
          hqSameMap hrOppMap
      · obtain rfl : v = () := Subsingleton.elim _ _
        exact (hrp rfl).elim
    · obtain rfl : u = () := Subsingleton.elim _ _
      exact (hqp rfl).elim

/-- Reorient a cocircuit, if necessary, so that its lexicographic lift has
the sign opposite to a prescribed nonzero lifted sign. -/
private theorem exists_reoriented_cocircuit_opposite_lexLift
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α) {X E : SignedSubset α}
    (hE : M.IsCocircuit E)
    (hpX : canonicalNew α ∈ (lexLift order X).support)
    {i : Fin order.length} (hfirst : LexFirstSupported order E i) :
    ∃ Y : SignedSubset α,
      M.IsCocircuit Y ∧ Y.support = E.support ∧
        LexFirstSupported order Y i ∧
        (lexLift order X).OppositeAt
          (lexLift order Y) (canonicalNew α) := by
  classical
  have newPositive {D : SignedSubset α} {j : Fin order.length}
      (hfirstD : LexFirstSupported order D j)
      (hpos : order[j] ∈ D.positive) :
      canonicalNew α ∈ (lexLift order D).positive := by
    exact Or.inr ⟨rfl, ⟨j, hfirstD, hpos⟩⟩
  have newNegative {D : SignedSubset α} {j : Fin order.length}
      (hfirstD : LexFirstSupported order D j)
      (hneg : order[j] ∈ D.negative) :
      canonicalNew α ∈ (lexLift order D).negative := by
    exact Or.inr ⟨rfl, ⟨j, hfirstD, hneg⟩⟩
  rcases hpX with hpXpos | hpXneg <;>
    rcases hfirst.1 with haEpos | haEneg
  · let Y : SignedSubset α := -E
    have hfirstY : LexFirstSupported order Y i := by
      simpa [Y, LexFirstSupported] using hfirst
    refine ⟨Y, M.neg_isCocircuit hE, by simp [Y], hfirstY, Or.inl ⟨hpXpos, ?_⟩⟩
    apply newNegative hfirstY
    simpa [Y] using haEpos
  · refine ⟨E, hE, rfl, hfirst, Or.inl ⟨hpXpos,
      newNegative hfirst haEneg⟩⟩
  · refine ⟨E, hE, rfl, hfirst, Or.inr ⟨hpXneg,
      newPositive hfirst haEpos⟩⟩
  · let Y : SignedSubset α := -E
    have hfirstY : LexFirstSupported order Y i := by
      simpa [Y, LexFirstSupported] using hfirst
    refine ⟨Y, M.neg_isCocircuit hE, by simp [Y], hfirstY, Or.inr ⟨hpXneg, ?_⟩⟩
    apply newPositive hfirstY
    simpa [Y] using haEneg

/-- Todd elimination turns any cocircuit supporting `a` into a cocircuit
conformal with a cocircuit vanishing at `a`, without losing `a` or leaving the
union of the two supports. -/
private theorem exists_conformal_cocircuit_through
    [Fintype α] (M : Data α) {X E : SignedSubset α}
    (hX : M.IsCocircuit X) (hE : M.IsCocircuit E)
    {a : α} (haX : a ∉ X.support) (haE : a ∈ E.support) :
    ∃ Y : SignedSubset α,
      M.IsCocircuit Y ∧ a ∈ Y.support ∧
        Y.support ⊆ X.support ∪ E.support ∧
        Y.SameSignAt E a ∧
        ∀ z, z ∈ X.support ∩ Y.support → X.SameSignAt Y z := by
  classical
  by_cases hopp : ∃ z ∈ X.support ∩ E.support, X.OppositeAt E z
  · have hXdual : M.dual.IsCircuit X := hX
    have hEdual : M.dual.IsCircuit E := hE
    obtain ⟨Y, hYdual, hTodd⟩ :=
      todd M.dual hXdual hEdual ⟨haE, haX⟩ hopp
    have hY : M.IsCocircuit Y := hYdual
    have hYsub : Y.support ⊆ X.support ∪ E.support := by
      intro z hz
      rcases hz with hz | hz
      · rcases (hTodd.1 hz).1 with hzX | hzE
        · exact Or.inl (Or.inl hzX)
        · exact Or.inr (Or.inl hzE)
      · rcases (hTodd.2.1 hz).1 with hzX | hzE
        · exact Or.inl (Or.inr hzX)
        · exact Or.inr (Or.inr hzE)
    refine ⟨Y, hY, hTodd.2.2.1, hYsub,
      hTodd.2.2.2, ?_⟩
    intro z hz
    rcases hz.2 with hzYpos | hzYneg
    · have hzNotXneg := (hTodd.1 hzYpos).2
      rcases hz.1 with hzXpos | hzXneg
      · exact Or.inl ⟨hzXpos, hzYpos⟩
      · exact (hzNotXneg hzXneg).elim
    · have hzNotXpos := (hTodd.2.1 hzYneg).2
      rcases hz.1 with hzXpos | hzXneg
      · exact (hzNotXpos hzXpos).elim
      · exact Or.inr ⟨hzXneg, hzYneg⟩
  · refine ⟨E, hE, haE, subset_union_right, ?_, ?_⟩
    · rcases haE with haE | haE
      · exact Or.inl ⟨haE, haE⟩
      · exact Or.inr ⟨haE, haE⟩
    · intro z hz
      rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem hz with hsame | hopp'
      · exact hsame
      · exact (hopp ⟨z, hz, hopp'⟩).elim

/-- Every genuinely new cocircuit support avoiding the extension point admits
the required compatible signing.  This is the completed rank-two/coline step
for positive lexicographic localization. -/
theorem hasStrictSecondaryCocircuitSignings
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α)) :
    HasStrictSecondaryCocircuitSignings M order hindep := by
  classical
  intro L hL hpL hstrict
  let U : Matroid α := M.underlying
  let A : Set α := order.toFinset
  let U' : Matroid (α ⊕ Unit) := principalLexMatroid M order hindep
  let K : Set α := PrincipalExtension.oldPart L
  let H : Set α := U.E \ K
  have hUE : U.E = Set.univ := M.underlying_spec.1
  have hA : U.Indep A := M.isIndependent_iff_underlying_indep.mp hindep
  have hL' : (PrincipalExtension.matroid U A hUE hA).IsCocircuit L := by
    simpa [U, A, principalLexMatroid] using hL
  have hpL' : PrincipalExtension.new α ∉ L := by
    simpa [canonicalNew, PrincipalExtension.new] using hpL
  have hshape : Sum.inl '' K = L :=
    PrincipalExtension.image_oldPart_eq_of_notMem L hpL'
  have hstrict' : ¬ U.IsCocircuit K := by
    simpa [U, K] using hstrict
  have hmeet : (K ∩ A).Nonempty := by
    by_contra hnot
    have hdisjoint : Disjoint K A := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hnot
    exact hstrict'
      (PrincipalExtension.oldPart_isCocircuit_of_isCocircuit_of_new_not_mem_of_disjoint
        U A hUE hA hL' hpL' (by simpa [K] using hdisjoint))
  let P : SignedSubset α :=
    { positive := K
      negative := ∅
      disjoint := Set.disjoint_empty K }
  have hPsupport : P.support = K := by simp [P, SignedSubset.support]
  have hOrderP : ∃ a ∈ order, a ∈ P.support := by
    obtain ⟨a, haK, haA⟩ := hmeet
    exact ⟨a, List.mem_toFinset.mp haA, hPsupport.symm ▸ haK⟩
  obtain ⟨i, hfirstP⟩ := exists_lexFirstSupported_iff.mpr hOrderP
  let a : α := order[i]
  have haK : a ∈ K := by
    simpa [a, hPsupport] using hfirstP.1
  have hbeforeK : ∀ j : Fin order.length, j < i → order[j] ∉ K := by
    intro j hji
    simpa [hPsupport] using hfirstP.2 j hji
  obtain ⟨hHnonspanning, hHclosed, hInsertNonspanning⟩ :=
    strict_old_compl_properties U A hUE hA hL' hpL' hstrict'
  have hHnonspanning' : ¬ U.Spanning H := by simpa [H, K] using hHnonspanning
  have hHclosed' : U.closure H = H := by simpa [H, K] using hHclosed
  have hInsertNonspanning' : ¬ U.Spanning (insert a H) := by
    simpa [H, K] using hInsertNonspanning a haK
  have hInsertGround : insert a H ⊆ U.E := by
    exact insert_subset (by simp [hUE]) sdiff_subset
  obtain ⟨Xset, hXset, hXsetSub⟩ :=
    exists_isCocircuit_subset_compl_of_not_spanning
      hInsertGround hInsertNonspanning'
  have hXsetK : Xset ⊆ K := by
    intro x hxX
    have hx := hXsetSub hxX
    refine by_contra fun hxK ↦ hx.2 ?_
    exact Or.inr ⟨hx.1, hxK⟩
  have haXset : a ∉ Xset := by
    intro haX
    exact (hXsetSub haX).2 (Or.inl rfl)
  obtain ⟨X, hX, hXsupport⟩ := M.exists_isCocircuit_support_eq hXset
  have hXK : X.support ⊆ K := by simpa [hXsupport] using hXsetK
  have haX : a ∉ X.support := by simpa [hXsupport] using haXset
  have hXmeet : (X.support ∩ A).Nonempty := by
    by_contra hnot
    have hXA : Disjoint X.support A := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hnot
    have hXext : (PrincipalExtension.matroid U A hUE hA).IsCocircuit
        (Sum.inl '' X.support) :=
      PrincipalExtension.matroid_isCocircuit_image_inl_of_disjoint
        U A hUE hA (by simpa [U] using M.isCocircuit_support hX)
          (by simpa [A] using hXA)
    have hXextSub : Sum.inl '' X.support ⊆ L := by
      rw [← hshape]
      exact Set.image_mono hXK
    have hEq : Sum.inl '' X.support = L :=
      hXext.eq_of_subset_isCircuit hL' hXextSub
    have haL : Sum.inl a ∈ L := by
      rw [← hshape]
      exact ⟨a, haK, rfl⟩
    have : Sum.inl a ∈ Sum.inl '' X.support := hEq ▸ haL
    exact haX (by simpa using this)
  have hpX : canonicalNew α ∈ (lexLift order X).support := by
    apply (canonicalNew_mem_lexLift_support_iff order X).mpr
    obtain ⟨x, hxX, hxA⟩ := hXmeet
    exact ⟨x, List.mem_toFinset.mp hxA, hxX⟩
  obtain ⟨I, hIH⟩ := U.exists_isBasis H (by simp [H])
  have haE : a ∈ U.E := by simp [hUE]
  have haNotH : a ∉ H := fun haH ↦ haH.2 haK
  have haNotClosureH : a ∉ U.closure H := by simpa [hHclosed'] using haNotH
  have haNotI : a ∉ I := fun haI ↦ haNotH (hIH.subset haI)
  have haNotClosureI : a ∉ U.closure I := by
    rwa [hIH.closure_eq_closure]
  have hIa : U.Indep (insert a I) :=
    (hIH.indep.notMem_closure_iff_of_notMem haNotI haE).mp haNotClosureI
  have hIaM : M.IsIndependent (insert a I) :=
    M.isIndependent_iff_underlying_indep.mpr (by simpa [U] using hIa)
  obtain ⟨E, hE, hEinter⟩ :=
    OrientedMatroid.Data.IsIndependent.exists_isCocircuit_support_inter_eq_singleton
      M hIaM (Set.mem_insert a I)
  have haE_support : a ∈ E.support := by
    have : a ∈ E.support ∩ insert a I := by
      rw [hEinter]
      exact Set.mem_singleton a
    exact this.1
  have hIEcompl : I ⊆ U.E \ E.support := by
    intro x hxI
    refine ⟨hIH.indep.subset_ground hxI, ?_⟩
    intro hxE
    have hxEq : x = a := by
      have : x ∈ E.support ∩ insert a I :=
        ⟨hxE, Set.mem_insert_of_mem a hxI⟩
      simpa [hEinter] using this
    exact haNotI (hxEq ▸ hxI)
  have hEK : E.support ⊆ K := by
    intro x hxE
    have hxGround : x ∈ U.E := by
      simpa [U] using (M.isCocircuit_support hE).subset_ground hxE
    refine by_contra fun hxK ↦ ?_
    have hxH : x ∈ H := ⟨hxGround, hxK⟩
    have hxClosureI : x ∈ U.closure I := hIH.subset_closure hxH
    have hxClosureCompl : x ∈ U.closure (U.E \ E.support) :=
      U.closure_subset_closure hIEcompl hxClosureI
    have hEordinary : U.IsCocircuit E.support := by
      simpa [U] using M.isCocircuit_support hE
    rw [cocircuit_compl_closure_eq hEordinary] at hxClosureCompl
    exact hxClosureCompl.2 hxE
  have hfirstE : LexFirstSupported order E i := by
    constructor
    · simpa [a] using haE_support
    · intro j hji
      exact fun hjE ↦ hbeforeK j hji (hEK hjE)
  obtain ⟨E', hE', hE'support, hfirstE', hpXE'⟩ :=
    exists_reoriented_cocircuit_opposite_lexLift
      M order hE hpX hfirstE
  have hE'K : E'.support ⊆ K := by simpa [hE'support] using hEK
  have haE' : a ∈ E'.support := hfirstE'.1
  obtain ⟨Y, hY, haY, hYsub, hYsameE', hconformal⟩ :=
    exists_conformal_cocircuit_through M hX hE' haX haE'
  have hYK : Y.support ⊆ K :=
    hYsub.trans (union_subset hXK hE'K)
  have hpXY : (lexLift order X).OppositeAt
      (lexLift order Y) (canonicalNew α) := by
    have hfirstY : LexFirstSupported order Y i := by
      constructor
      · exact haY
      · intro j hji
        exact fun hjY ↦ hbeforeK j hji (hYK hjY)
    have hEYsame : E'.SameSignAt Y a :=
      SignedSubset.sameSignAt_comm.mp hYsameE'
    have hLiftSame : (lexLift order E').SameSignAt
        (lexLift order Y) (canonicalNew α) := by
      rcases hEYsame with hEYsame | hEYsame
      · exact Or.inl ⟨
          Or.inr ⟨rfl, ⟨i, hfirstE', by simpa [a] using hEYsame.1⟩⟩,
          Or.inr ⟨rfl, ⟨i, hfirstY, by simpa [a] using hEYsame.2⟩⟩⟩
      · exact Or.inr ⟨
          Or.inr ⟨rfl, ⟨i, hfirstE', by simpa [a] using hEYsame.1⟩⟩,
          Or.inr ⟨rfl, ⟨i, hfirstY, by simpa [a] using hEYsame.2⟩⟩⟩
    exact hpXE'.trans_sameSignAt hLiftSame
  have hUnion : X.support ∪ Y.support = K := by
    apply cocircuit_union_eq_strict_oldPart U A hUE hA hL' hpL'
      (by simpa [U] using M.isCocircuit_support hX)
      (by simpa [U] using M.isCocircuit_support hY)
      hXK hYK haX haY
  let Dold : SignedSubset α := X.compose Y
  let D : SignedSubset (α ⊕ Unit) := Dold.map (canonicalOld α)
  have hDoldCovector : M.IsCovector Dold := by
    exact OrientedMatroid.Data.IsCovector.compose M hX.2.1 hY.2.1
  refine ⟨D, ?_, ?_⟩
  · constructor
    ·
      change (principalLexMatroid M order hindep).IsCocircuit
        ((Dold.map (canonicalOld α)).support)
      rw [SignedSubset.support_map]
      change (principalLexMatroid M order hindep).IsCocircuit
        (Sum.inl '' (X.compose Y).support)
      rw [SignedSubset.support_compose, hUnion, hshape]
      exact hL
    · intro C hC
      rcases hC with ⟨C₀, hC₀, rfl⟩ | ⟨B, hminimal, rfl | rfl⟩
      · exact (hDoldCovector hC₀).map (canonicalOld α)
      · exact orthogonal_map_compose_of_opposite_lexLifts order
          (Or.inl (lexCircuit_new_positive M order B hminimal.1))
          (lexCircuit_orthogonal_lexLift M order B hminimal.1 hX.2.1)
          (lexCircuit_orthogonal_lexLift M order B hminimal.1 hY.2.1)
          hpXY hconformal
      · rw [SignedSubset.orthogonal_comm,
          SignedSubset.orthogonal_neg_right_iff,
          SignedSubset.orthogonal_comm]
        exact orthogonal_map_compose_of_opposite_lexLifts order
          (Or.inl (lexCircuit_new_positive M order B hminimal.1))
          (lexCircuit_orthogonal_lexLift M order B hminimal.1 hX.2.1)
          (lexCircuit_orthogonal_lexLift M order B hminimal.1 hY.2.1)
          hpXY hconformal
  · change ((X.compose Y).map (canonicalOld α)).support = L
    rw [SignedSubset.support_map]
    change Sum.inl '' (X.compose Y).support = L
    rw [SignedSubset.support_compose, hUnion]
    simpa [canonicalOld] using hshape

end OrientedMatroid
end BeyondSperner
