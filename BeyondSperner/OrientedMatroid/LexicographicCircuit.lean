import BeyondSperner.OrientedMatroid.LexicographicLocalization
import BeyondSperner.OrientedMatroid.PrincipalExtension

/-!
# Circuits for a positive lexicographic extension

This file constructs the signed old part of every circuit containing the new
point.  The construction is intrinsic to the old oriented matroid: extend the
old part of the circuit to a basis, take the signed fundamental dependence of
each lexicographic coordinate on that basis, and retain at every basis
coordinate the first nonzero sign.

The support lemmas below are independent of the still-missing extension
existence theorem.  In particular, they connect the signed construction to the
exact ordinary circuit classification of `PrincipalExtension.matroid`.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid

variable {α : Type*}

/-- The signed coefficient vector of an element relative to an oriented basis.
For a basis element it is the negative unit vector.  For an external element
it is its positively oriented fundamental circuit with the external coordinate
erased. -/
noncomputable def fundamentalCoefficient [Finite α]
    (M : Data α) (G : Set α) (hG : M.IsBasis G) (a : α) :
    SignedSubset α := by
  classical
  exact if ha : a ∈ G then SignedSubset.negativeSingleton a
    else (M.signedFundCircuit G hG a).erase a

@[simp]
theorem fundamentalCoefficient_support_of_mem [Finite α]
    (M : Data α) {G : Set α} (hG : M.IsBasis G) {a : α}
    (ha : a ∈ G) :
    (fundamentalCoefficient M G hG a).support = {a} := by
  simp [fundamentalCoefficient, ha]

@[simp]
theorem fundamentalCoefficient_support_of_not_mem [Finite α]
    (M : Data α) {G : Set α} (hG : M.IsBasis G) {a : α}
    (ha : a ∉ G) :
    (fundamentalCoefficient M G hG a).support =
      M.underlying.fundCircuit a G \ {a} := by
  simp [fundamentalCoefficient, ha,
    SignedSubset.support_erase, M.signedFundCircuit_support hG ha]

/-- If an independent `B` is contained in the chosen basis and spans `a`, all
nonzero fundamental coefficients of `a` lie in `B`. -/
theorem fundamentalCoefficient_support_subset [Fintype α]
    (M : Data α) {B G : Set α} (hB : M.underlying.Indep B)
    (hG : M.IsBasis G) (hBG : B ⊆ G) {a : α}
    (haB : a ∈ M.underlying.closure B) :
    (fundamentalCoefficient M G hG a).support ⊆ B := by
  classical
  have hGbase : M.underlying.IsBase G :=
    M.isBasis_iff_underlying_isBase.mp hG
  by_cases haG : a ∈ G
  · rw [fundamentalCoefficient_support_of_mem M hG haG]
    have haB' : a ∈ B := by
      have haInter : a ∈ M.underlying.closure B ∩ G := ⟨haB, haG⟩
      rw [hGbase.indep.closure_inter_eq_self_of_subset hBG] at haInter
      exact haInter
    simpa using haB'
  · rw [fundamentalCoefficient_support_of_not_mem M hG haG]
    have haNotB : a ∉ B := fun ha ↦ haG (hBG ha)
    have hsmall : M.underlying.IsCircuit
        (M.underlying.fundCircuit a B) :=
      hB.fundCircuit_isCircuit haB haNotB
    have hsmallSub : M.underlying.fundCircuit a B ⊆ insert a G :=
      (M.underlying.fundCircuit_subset_insert a B).trans
        (insert_subset_insert hBG)
    have heq : M.underlying.fundCircuit a B =
        M.underlying.fundCircuit a G :=
      hsmall.eq_fundCircuit_of_subset hGbase.indep hsmallSub
    intro x hx
    have hxSmall : x ∈ M.underlying.fundCircuit a B := heq ▸ hx.1
    rcases M.underlying.fundCircuit_subset_insert a B hxSmall with hxa | hxB
    · exact (hx.2 hxa).elim
    · exact hxB

/-- If deleting `b` destroys the spanning of `a`, then the fundamental
coefficient of `a` is nonzero at `b`. -/
theorem mem_fundamentalCoefficient_support_of_not_mem_closure [Fintype α]
    (M : Data α) {B G : Set α} (hB : M.underlying.Indep B)
    (hG : M.IsBasis G) (hBG : B ⊆ G) {a b : α} (hbB : b ∈ B)
    (haB : a ∈ M.underlying.closure B)
    (haRemove : a ∉ M.underlying.closure (B \ {b})) :
    b ∈ (fundamentalCoefficient M G hG a).support := by
  classical
  have hGbase : M.underlying.IsBase G :=
    M.isBasis_iff_underlying_isBase.mp hG
  by_cases haG : a ∈ G
  · rw [fundamentalCoefficient_support_of_mem M hG haG]
    have haInB : a ∈ B := by
      have haInter : a ∈ M.underlying.closure B ∩ G := ⟨haB, haG⟩
      rw [hGbase.indep.closure_inter_eq_self_of_subset hBG] at haInter
      exact haInter
    have hab : a = b := by
      by_contra hne
      apply haRemove
      exact M.underlying.subset_closure (B \ {b})
        (hB.sdiff _).subset_ground ⟨haInB, by simpa using hne⟩
    simp [hab]
  · rw [fundamentalCoefficient_support_of_not_mem M hG haG]
    have haNotB : a ∉ B := fun ha ↦ haG (hBG ha)
    have hab : a ≠ b := fun h ↦ haG (h ▸ hBG hbB)
    have hsmall : M.underlying.IsCircuit
        (M.underlying.fundCircuit a B) :=
      hB.fundCircuit_isCircuit haB haNotB
    have hsmallSub : M.underlying.fundCircuit a B ⊆ insert a G :=
      (M.underlying.fundCircuit_subset_insert a B).trans
        (insert_subset_insert hBG)
    have heq : M.underlying.fundCircuit a B =
        M.underlying.fundCircuit a G :=
      hsmall.eq_fundCircuit_of_subset hGbase.indep hsmallSub
    have haGround : a ∈ M.underlying.E :=
      Matroid.mem_ground_of_mem_closure haB
    have haNotRemove : a ∉ B \ {b} := by
      exact fun ha ↦ haNotB ha.1
    have hInsert : M.underlying.Indep (insert a (B \ {b})) :=
      ((hB.sdiff _).notMem_closure_iff_of_notMem
        haNotRemove haGround).mp haRemove
    have hFundSmall : b ∈ M.underlying.fundCircuit a B := by
      apply (hB.mem_fundCircuit_iff haB haNotB).mpr
      rw [← insert_sdiff_singleton_comm hab B]
      exact hInsert
    exact ⟨heq ▸ hFundSmall, by simpa using hab.symm⟩

/-- The old signed part of the lexicographic circuit determined by `B` and a
basis `G ⊇ B`. -/
noncomputable def lexCircuitOld [Finite α]
    (M : Data α) (order : List α) (G : Set α) (hG : M.IsBasis G) :
    SignedSubset α :=
  SignedSubset.priorityCompose
    (order.map (fundamentalCoefficient M G hG))

/-- If every lexicographic coordinate is spanned by `B`, the old
lexicographic circuit has no support outside `B`. -/
theorem lexCircuitOld_support_subset [Fintype α] [DecidableEq α]
    (M : Data α) {order : List α} {B G : Set α}
    (hB : M.underlying.Indep B) (hG : M.IsBasis G) (hBG : B ⊆ G)
    (hspan : (order.toFinset : Set α) ⊆ M.underlying.closure B) :
    (lexCircuitOld M order G hG).support ⊆ B := by
  apply SignedSubset.priorityCompose_support_subset
  intro C hC
  obtain ⟨a, haOrder, rfl⟩ := List.mem_map.mp hC
  apply fundamentalCoefficient_support_subset M hB hG hBG
  exact hspan (List.mem_toFinset.mpr haOrder)

/-- Minimal spanning is exactly what is needed for the priority fundamental
coefficients to cover every element of `B`. -/
theorem lexCircuitOld_support_eq [Fintype α] [DecidableEq α]
    (M : Data α) {order : List α} {B G : Set α}
    (hG : M.IsBasis G) (hBG : B ⊆ G)
    (hminimal : PrincipalExtension.IsMinimalSpanning M.underlying
      (order.toFinset : Set α) B) :
    (lexCircuitOld M order G hG).support = B := by
  apply Set.Subset.antisymm
  · exact lexCircuitOld_support_subset M hminimal.1 hG hBG hminimal.2.1
  · intro b hbB
    have hnotSubset := hminimal.2.2 b hbB
    obtain ⟨a, haOrder, haRemove⟩ := Set.not_subset.mp hnotSubset
    apply (SignedSubset.mem_priorityCompose_support_iff
      (order.map (fundamentalCoefficient M G hG)) b).mpr
    refine ⟨fundamentalCoefficient M G hG a,
      List.mem_map.mpr ⟨a, List.mem_toFinset.mp haOrder, rfl⟩, ?_⟩
    exact mem_fundamentalCoefficient_support_of_not_mem_closure M
      hminimal.1 hG hBG hbB (hminimal.2.1 haOrder) haRemove

/-- Every ordinary independent set is contained in an oriented basis. -/
theorem exists_isBasis_superset_of_underlying_indep [Fintype α]
    (M : Data α) {B : Set α} (hB : M.underlying.Indep B) :
    ∃ G : Set α, M.IsBasis G ∧ B ⊆ G := by
  obtain ⟨G, hG, hBG⟩ :=
    hB.subset_isBasis_of_subset hB.subset_ground
  exact ⟨G, M.isBasis_iff_underlying_isBase.mpr
    (Matroid.isBasis_ground_iff.mp hG), hBG⟩

/-- A canonical choice of an oriented basis containing an independent set. -/
noncomputable def lexCircuitBasis [Fintype α]
    (M : Data α) (B : Set α) (hB : M.underlying.Indep B) : Set α :=
  Classical.choose (exists_isBasis_superset_of_underlying_indep M hB)

theorem lexCircuitBasis_isBasis [Fintype α]
    (M : Data α) (B : Set α) (hB : M.underlying.Indep B) :
    M.IsBasis (lexCircuitBasis M B hB) :=
  (Classical.choose_spec
    (exists_isBasis_superset_of_underlying_indep M hB)).1

theorem subset_lexCircuitBasis [Fintype α]
    (M : Data α) (B : Set α) (hB : M.underlying.Indep B) :
    B ⊆ lexCircuitBasis M B hB :=
  (Classical.choose_spec
    (exists_isBasis_superset_of_underlying_indep M hB)).2

/-- Embed an old signed subset and give the canonical new point a positive
sign. -/
def addCanonicalNewPositive (C : SignedSubset α) :
    SignedSubset (α ⊕ Unit) where
  positive := Sum.inl '' C.positive ∪ {canonicalNew α}
  negative := Sum.inl '' C.negative
  disjoint := by
    rw [Set.disjoint_left]
    rintro z (hzOld | hzNew) ⟨x, hxNeg, rfl⟩
    · obtain ⟨y, hyPos, hyx⟩ := hzOld
      exact Set.disjoint_left.1 C.disjoint hyPos
        (Sum.inl_injective hyx ▸ hxNeg)
    · simp [canonicalNew] at hzNew

@[simp]
theorem canonicalNew_mem_addCanonicalNewPositive_positive
    (C : SignedSubset α) :
    canonicalNew α ∈ (addCanonicalNewPositive C).positive := by
  simp [addCanonicalNewPositive]

@[simp]
theorem addCanonicalNewPositive_comap (C : SignedSubset α) :
    (addCanonicalNewPositive C).comap (canonicalOld α) = C := by
  ext x <;> simp [addCanonicalNewPositive, canonicalOld, canonicalNew]

@[simp]
theorem addCanonicalNewPositive_support (C : SignedSubset α) :
    (addCanonicalNewPositive C).support =
      insert (canonicalNew α) (Sum.inl '' C.support) := by
  ext z
  rcases z with x | u
  · simp [SignedSubset.support, addCanonicalNewPositive,
      canonicalNew]
  · obtain rfl : u = () := Subsingleton.elim _ _
    simp [SignedSubset.support, addCanonicalNewPositive,
      canonicalNew]

/-- Adding the positive new point is priority composition with its positive
unit vector. -/
theorem addCanonicalNewPositive_eq_compose (C : SignedSubset α) :
    addCanonicalNewPositive C =
      (SignedSubset.positiveSingleton (canonicalNew α)).compose
        (C.map (canonicalOld α)) := by
  ext z <;>
    simp [addCanonicalNewPositive, SignedSubset.compose,
      canonicalOld, canonicalNew, SignedSubset.support]

/-- Orthogonality is preserved when the positive new point is added on one
side and the other side is embedded entirely on old coordinates. -/
theorem addCanonicalNewPositive_orthogonal_map
    {C D : SignedSubset α} (hCD : C.Orthogonal D) :
    (addCanonicalNewPositive C).Orthogonal
      (D.map (canonicalOld α)) := by
  rw [addCanonicalNewPositive_eq_compose]
  apply SignedSubset.Orthogonal.compose_left
  · left
    rw [SignedSubset.support_positiveSingleton,
      SignedSubset.support_map, Set.disjoint_left]
    rintro z hz ⟨x, _, hx⟩
    have : z = canonicalNew α := by simpa using hz
    subst z
    simp [canonicalOld, canonicalNew] at hx
  · exact hCD.map (canonicalOld α)

/-- When no ordered coordinate is supported, `lexLift` is just the old signed
set embedded into the canonical carrier. -/
theorem lexLift_eq_map_of_disjoint [DecidableEq α]
    (order : List α) (D : SignedSubset α)
    (hdisjoint : Disjoint D.support (order.toFinset : Set α)) :
    lexLift order D = D.map (canonicalOld α) := by
  have hnew : canonicalNew α ∉ (lexLift order D).support :=
    (canonicalNew_not_mem_lexLift_support_iff order D).mpr hdisjoint
  have hsupport : (lexLift order D).support ⊆
      Set.range (canonicalOld α) := by
    intro z hz
    rcases z with x | u
    · exact ⟨x, rfl⟩
    · obtain rfl : u = () := Subsingleton.elim _ _
      exact (hnew hz).elim
  have hmap := SignedSubset.map_comap_of_support_subset_range
    (canonicalOld α) (lexLift order D) hsupport
  simpa using hmap.symm

@[simp]
theorem canonicalOld_mem_lexLift_positive_iff
    (order : List α) (D : SignedSubset α) (x : α) :
    canonicalOld α x ∈ (lexLift order D).positive ↔ x ∈ D.positive := by
  simp [lexLift, canonicalOld, canonicalNew]

@[simp]
theorem canonicalOld_mem_lexLift_negative_iff
    (order : List α) (D : SignedSubset α) (x : α) :
    canonicalOld α x ∈ (lexLift order D).negative ↔ x ∈ D.negative := by
  simp [lexLift, canonicalOld, canonicalNew]

@[simp]
theorem canonicalOld_mem_lexLift_support_iff
    (order : List α) (D : SignedSubset α) (x : α) :
    canonicalOld α x ∈ (lexLift order D).support ↔ x ∈ D.support := by
  simp [SignedSubset.support]

private theorem exists_lexFirstSupported_cons_iff
    (a : α) (tail : List α) (D : SignedSubset α)
    (haD : a ∉ D.support) (P : α → Prop) :
    (∃ i : Fin (a :: tail).length,
      LexFirstSupported (a :: tail) D i ∧ P ((a :: tail)[i])) ↔
    ∃ j : Fin tail.length, LexFirstSupported tail D j ∧ P (tail[j]) := by
  constructor
  · rintro ⟨i, hi, hPi⟩
    refine Fin.cases (motive := fun i ↦
      LexFirstSupported (a :: tail) D i → P ((a :: tail)[i]) →
        ∃ j : Fin tail.length,
          LexFirstSupported tail D j ∧ P (tail[j])) ?_ ?_ i hi hPi
    · intro hfirst _
      exact (haD (by simpa using hfirst.1)).elim
    · intro j hfirst hP
      refine ⟨j, ?_, by simpa using hP⟩
      constructor
      · simpa using hfirst.1
      · intro k hkj hkD
        apply hfirst.2 (Fin.succ k)
        · simpa using hkj
        · simpa using hkD
  · rintro ⟨j, hj, hPj⟩
    refine ⟨Fin.succ j, ?_, by simpa using hPj⟩
    constructor
    · simpa using hj.1
    · intro k
      refine Fin.cases (motive := fun k ↦
        k < Fin.succ j → (a :: tail)[k] ∉ D.support) ?_ ?_ k
      · intro _
        simpa using haD
      · intro l hlj hlD
        apply hj.2 l
        · exact Fin.succ_lt_succ_iff.mp hlj
        · simpa using hlD

/-- A zero head coordinate does not affect the lexicographic lift. -/
theorem lexLift_cons_of_not_mem_support (a : α) (tail : List α)
    (D : SignedSubset α) (haD : a ∉ D.support) :
    lexLift (a :: tail) D = lexLift tail D := by
  classical
  ext z
  · rcases z with x | u
    · change (canonicalOld α x ∈ (lexLift (a :: tail) D).positive) ↔
        canonicalOld α x ∈ (lexLift tail D).positive
      simp
    · obtain rfl : u = () := Subsingleton.elim _ _
      simpa [lexLift, canonicalNew] using
        (exists_lexFirstSupported_cons_iff a tail D haD
          (fun x ↦ x ∈ D.positive))
  · rcases z with x | u
    · change (canonicalOld α x ∈ (lexLift (a :: tail) D).negative) ↔
        canonicalOld α x ∈ (lexLift tail D).negative
      simp
    · obtain rfl : u = () := Subsingleton.elim _ _
      simpa [lexLift, canonicalNew] using
        (exists_lexFirstSupported_cons_iff a tail D haD
          (fun x ↦ x ∈ D.negative))

/-- An old sign vector orthogonal to `D` remains orthogonal to the canonical
lift of `D`; the possible new coordinate cannot meet its embedded support. -/
theorem map_orthogonal_lexLift {C D : SignedSubset α}
    (order : List α) (hCD : C.Orthogonal D) :
    (C.map (canonicalOld α)).Orthogonal (lexLift order D) := by
  rcases hCD with hdisjoint | ⟨u, hu, v, hv, huSame, hvOpp⟩
  · left
    rw [Set.disjoint_left]
    intro z hzC hzD
    rw [SignedSubset.support_map] at hzC
    obtain ⟨x, hxC, rfl⟩ := hzC
    exact Set.disjoint_left.1 hdisjoint hxC
      ((canonicalOld_mem_lexLift_support_iff order D x).mp hzD)
  · right
    refine ⟨canonicalOld α u, ?_, canonicalOld α v, ?_, ?_, ?_⟩
    · rw [SignedSubset.support_map]
      exact ⟨⟨u, hu.1, rfl⟩,
        (canonicalOld_mem_lexLift_support_iff order D u).mpr hu.2⟩
    · rw [SignedSubset.support_map]
      exact ⟨⟨v, hv.1, rfl⟩,
        (canonicalOld_mem_lexLift_support_iff order D v).mpr hv.2⟩
    · rcases huSame with huSame | huSame
      · exact Or.inl ⟨⟨u, huSame.1, rfl⟩,
          (canonicalOld_mem_lexLift_positive_iff order D u).mpr huSame.2⟩
      · exact Or.inr ⟨⟨u, huSame.1, rfl⟩,
          (canonicalOld_mem_lexLift_negative_iff order D u).mpr huSame.2⟩
    · rcases hvOpp with hvOpp | hvOpp
      · exact Or.inl ⟨⟨v, hvOpp.1, rfl⟩,
          (canonicalOld_mem_lexLift_negative_iff order D v).mpr hvOpp.2⟩
      · exact Or.inr ⟨⟨v, hvOpp.1, rfl⟩,
          (canonicalOld_mem_lexLift_positive_iff order D v).mpr hvOpp.2⟩

/-- Adding the new positive coordinate commutes with putting an old sign
vector in front of a priority composition. -/
theorem addCanonicalNewPositive_compose (C R : SignedSubset α) :
    addCanonicalNewPositive (C.compose R) =
      (C.map (canonicalOld α)).compose (addCanonicalNewPositive R) := by
  ext z
  · rcases z with x | u
    · simp [addCanonicalNewPositive, SignedSubset.compose,
        SignedSubset.support, canonicalOld, canonicalNew]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [addCanonicalNewPositive, SignedSubset.compose,
        SignedSubset.support, canonicalOld, canonicalNew]
  · rcases z with x | u
    · simp [addCanonicalNewPositive, SignedSubset.compose,
        SignedSubset.support, canonicalOld, canonicalNew]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [addCanonicalNewPositive, SignedSubset.compose,
        SignedSubset.support, canonicalOld, canonicalNew]

/-- A positive head gives the new coordinate a positive sign. -/
theorem canonicalNew_mem_lexLift_cons_positive
    (a : α) (tail : List α) (D : SignedSubset α)
    (haD : a ∈ D.positive) :
    canonicalNew α ∈ (lexLift (a :: tail) D).positive := by
  classical
  have hfirst : LexFirstSupported (a :: tail) D 0 := by
    constructor
    · exact Or.inl haD
    · intro j hj
      exact (Fin.not_lt_zero j hj).elim
  exact Or.inr ⟨rfl, ⟨0, hfirst, by simpa using haD⟩⟩

/-- A negative head gives the new coordinate a negative sign. -/
theorem canonicalNew_mem_lexLift_cons_negative
    (a : α) (tail : List α) (D : SignedSubset α)
    (haD : a ∈ D.negative) :
    canonicalNew α ∈ (lexLift (a :: tail) D).negative := by
  classical
  have hfirst : LexFirstSupported (a :: tail) D 0 := by
    constructor
    · exact Or.inr haD
    · intro j hj
      exact (Fin.not_lt_zero j hj).elim
  exact Or.inr ⟨rfl, ⟨0, hfirst, by simpa using haD⟩⟩

/-- A same-sign relation at an old coordinate survives putting the first
vector in front, adding the new point, and lexicographically lifting the right
vector. -/
theorem addCompose_sameSignAt_lexLift {F R D : SignedSubset α}
    (order : List α) {b : α} (h : F.SameSignAt D b) :
    (addCanonicalNewPositive (F.compose R)).SameSignAt
      (lexLift order D) (canonicalOld α b) := by
  rcases h with h | h
  · exact Or.inl ⟨Or.inl ⟨b, Or.inl h.1, rfl⟩,
      (canonicalOld_mem_lexLift_positive_iff order D b).mpr h.2⟩
  · exact Or.inr ⟨⟨b, Or.inl h.1, rfl⟩,
      (canonicalOld_mem_lexLift_negative_iff order D b).mpr h.2⟩

/-- The analogous preservation statement for opposite signs. -/
theorem addCompose_oppositeAt_lexLift {F R D : SignedSubset α}
    (order : List α) {b : α} (h : F.OppositeAt D b) :
    (addCanonicalNewPositive (F.compose R)).OppositeAt
      (lexLift order D) (canonicalOld α b) := by
  rcases h with h | h
  · exact Or.inl ⟨Or.inl ⟨b, Or.inl h.1, rfl⟩,
      (canonicalOld_mem_lexLift_negative_iff order D b).mpr h.2⟩
  · exact Or.inr ⟨⟨b, Or.inl h.1, rfl⟩,
      (canonicalOld_mem_lexLift_positive_iff order D b).mpr h.2⟩

/-- A fundamental coefficient is orthogonal to a covector whenever the
coefficient's external coordinate is zero in that covector. -/
theorem fundamentalCoefficient_orthogonal_of_not_mem [Fintype α]
    (M : Data α) {G : Set α} (hG : M.IsBasis G)
    {D : SignedSubset α} (hD : M.IsCovector D) {a : α}
    (haD : a ∉ D.support) :
    (fundamentalCoefficient M G hG a).Orthogonal D := by
  classical
  by_cases haG : a ∈ G
  · left
    rw [fundamentalCoefficient_support_of_mem M hG haG,
      Set.disjoint_left]
    intro x hx hxD
    have hxa : x = a := by simpa using hx
    exact haD (hxa ▸ hxD)
  · rw [fundamentalCoefficient, dif_neg haG]
    apply SignedSubset.orthogonal_erase_left_of_not_mem_right
    · exact hD (M.signedFundCircuit_isCircuit hG haG)
    · exact haD

/-- If the external coordinate is positive in a covector, its fundamental
coefficient has an opposite-sign old coordinate in that covector. -/
theorem exists_fundamentalCoefficient_opposite_of_positive [Fintype α]
    (M : Data α) {G : Set α} (hG : M.IsBasis G)
    {D : SignedSubset α} (hD : M.IsCovector D) {a : α}
    (haD : a ∈ D.positive) :
    ∃ b ∈ (fundamentalCoefficient M G hG a).support ∩ D.support,
      (fundamentalCoefficient M G hG a).OppositeAt D b := by
  classical
  by_cases haG : a ∈ G
  · refine ⟨a, ?_, ?_⟩
    · exact ⟨by simp [fundamentalCoefficient, haG], Or.inl haD⟩
    · exact Or.inr ⟨by simp [fundamentalCoefficient, haG], haD⟩
  · let C : SignedSubset α := M.signedFundCircuit G hG a
    have hC : M.IsCircuit C := by
      simpa [C] using M.signedFundCircuit_isCircuit hG haG
    have haCpos : a ∈ C.positive := by
      simpa [C] using M.signedFundCircuit_external_positive hG haG
    have horth : C.Orthogonal D := hD hC
    have haSame : C.SameSignAt D a := Or.inl ⟨haCpos, haD⟩
    rcases horth with hdisjoint | ⟨u, hu, v, hv, _, hvOpp⟩
    · exact (Set.disjoint_left.1 hdisjoint
        (Or.inl haCpos) (Or.inl haD)).elim
    · have hva : v ≠ a := by
        intro h
        subst v
        exact haSame.not_oppositeAt hvOpp
      refine ⟨v, ?_, ?_⟩
      · constructor
        · rw [fundamentalCoefficient, dif_neg haG,
            SignedSubset.support_erase]
          exact ⟨hv.1, by simpa using hva⟩
        · exact hv.2
      · rw [fundamentalCoefficient, dif_neg haG]
        rcases hvOpp with hvOpp | hvOpp
        · exact Or.inl ⟨⟨hvOpp.1, by simpa using hva⟩, hvOpp.2⟩
        · exact Or.inr ⟨⟨hvOpp.1, by simpa using hva⟩, hvOpp.2⟩

/-- If the external coordinate is negative in a covector, its fundamental
coefficient has a same-sign old coordinate in that covector. -/
theorem exists_fundamentalCoefficient_same_of_negative [Fintype α]
    (M : Data α) {G : Set α} (hG : M.IsBasis G)
    {D : SignedSubset α} (hD : M.IsCovector D) {a : α}
    (haD : a ∈ D.negative) :
    ∃ b ∈ (fundamentalCoefficient M G hG a).support ∩ D.support,
      (fundamentalCoefficient M G hG a).SameSignAt D b := by
  classical
  by_cases haG : a ∈ G
  · refine ⟨a, ?_, ?_⟩
    · exact ⟨by simp [fundamentalCoefficient, haG], Or.inr haD⟩
    · exact Or.inr ⟨by simp [fundamentalCoefficient, haG], haD⟩
  · let C : SignedSubset α := M.signedFundCircuit G hG a
    have hC : M.IsCircuit C := by
      simpa [C] using M.signedFundCircuit_isCircuit hG haG
    have haCpos : a ∈ C.positive := by
      simpa [C] using M.signedFundCircuit_external_positive hG haG
    have horth : C.Orthogonal D := hD hC
    have haOpp : C.OppositeAt D a := Or.inl ⟨haCpos, haD⟩
    rcases horth with hdisjoint | ⟨u, hu, v, hv, huSame, _⟩
    · exact (Set.disjoint_left.1 hdisjoint
        (Or.inl haCpos) (Or.inr haD)).elim
    · have hua : u ≠ a := by
        intro h
        subst u
        exact huSame.not_oppositeAt haOpp
      refine ⟨u, ?_, ?_⟩
      · constructor
        · rw [fundamentalCoefficient, dif_neg haG,
            SignedSubset.support_erase]
          exact ⟨hu.1, by simpa using hua⟩
        · exact hu.2
      · rw [fundamentalCoefficient, dif_neg haG]
        rcases huSame with huSame | huSame
        · exact Or.inl ⟨⟨huSame.1, by simpa using hua⟩, huSame.2⟩
        · exact Or.inr ⟨⟨huSame.1, by simpa using hua⟩, huSame.2⟩

/-- The nonzero-head step of lexicographic orthogonality.  The positive new
coordinate supplies one sign relation; the fundamental coefficient supplies
the opposite relation on an old coordinate. -/
theorem addFundamentalHead_orthogonal_lexLift [Fintype α]
    (M : Data α) {G : Set α} (hG : M.IsBasis G)
    (a : α) (tail : List α) {D : SignedSubset α}
    (hD : M.IsCovector D) (R : SignedSubset α)
    (haD : a ∈ D.support) :
    (addCanonicalNewPositive
      ((fundamentalCoefficient M G hG a).compose R)).Orthogonal
        (lexLift (a :: tail) D) := by
  rcases haD with haDpos | haDneg
  · obtain ⟨b, _, hbOpp⟩ :=
      exists_fundamentalCoefficient_opposite_of_positive M hG hD haDpos
    have hpSame :
        (addCanonicalNewPositive
          ((fundamentalCoefficient M G hG a).compose R)).SameSignAt
            (lexLift (a :: tail) D) (canonicalNew α) :=
      Or.inl ⟨canonicalNew_mem_addCanonicalNewPositive_positive _,
        canonicalNew_mem_lexLift_cons_positive a tail D haDpos⟩
    have hbOpp' := addCompose_oppositeAt_lexLift
      (a :: tail) (R := R) hbOpp
    right
    exact ⟨canonicalNew α,
      ⟨hpSame.mem_support_left, hpSame.mem_support_right⟩,
      canonicalOld α b,
      ⟨hbOpp'.mem_support_left, hbOpp'.mem_support_right⟩,
      hpSame, hbOpp'⟩
  · obtain ⟨b, _, hbSame⟩ :=
      exists_fundamentalCoefficient_same_of_negative M hG hD haDneg
    have hpOpp :
        (addCanonicalNewPositive
          ((fundamentalCoefficient M G hG a).compose R)).OppositeAt
            (lexLift (a :: tail) D) (canonicalNew α) :=
      Or.inl ⟨canonicalNew_mem_addCanonicalNewPositive_positive _,
        canonicalNew_mem_lexLift_cons_negative a tail D haDneg⟩
    have hbSame' := addCompose_sameSignAt_lexLift
      (a :: tail) (R := R) hbSame
    right
    exact ⟨canonicalOld α b,
      ⟨hbSame'.mem_support_left, hbSame'.mem_support_right⟩,
      canonicalNew α,
      ⟨hpOpp.mem_support_left, hpOpp.mem_support_right⟩,
      hbSame', hpOpp⟩

/-- The signed circuit candidate is orthogonal to the lexicographic lift of
every old covector. -/
theorem addLexCircuitOld_orthogonal_lexLift
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α) {G : Set α} (hG : M.IsBasis G)
    {D : SignedSubset α} (hD : M.IsCovector D) :
    (addCanonicalNewPositive (lexCircuitOld M order G hG)).Orthogonal
      (lexLift order D) := by
  induction order with
  | nil =>
      rw [lexLift_eq_map_of_disjoint [] D (by simp)]
      apply addCanonicalNewPositive_orthogonal_map
      left
      simp [lexCircuitOld]
  | cons a tail ih =>
      simp only [lexCircuitOld, List.map_cons,
        SignedSubset.priorityCompose_cons]
      by_cases haD : a ∈ D.support
      · exact addFundamentalHead_orthogonal_lexLift
          M hG a tail hD _ haD
      · rw [lexLift_cons_of_not_mem_support a tail D haD,
          addCanonicalNewPositive_compose]
        apply SignedSubset.Orthogonal.compose_left
        · apply map_orthogonal_lexLift tail
          exact fundamentalCoefficient_orthogonal_of_not_mem M hG hD haD
        · simpa [lexCircuitOld] using ih

/-- If a covector vanishes on the whole lexicographic list, it is orthogonal
to the old part of every lexicographic circuit candidate. -/
theorem lexCircuitOld_orthogonal_of_disjoint [Fintype α]
    [DecidableEq α] (M : Data α) (order : List α)
    {G : Set α} (hG : M.IsBasis G) {D : SignedSubset α}
    (hD : M.IsCovector D)
    (hdisjoint : Disjoint D.support (order.toFinset : Set α)) :
    (lexCircuitOld M order G hG).Orthogonal D := by
  apply SignedSubset.Orthogonal.priorityCompose_left
  intro C hC
  obtain ⟨a, haOrder, rfl⟩ := List.mem_map.mp hC
  apply fundamentalCoefficient_orthogonal_of_not_mem M hG hD
  intro haD
  exact Set.disjoint_left.1 hdisjoint haD
    (List.mem_toFinset.mpr haOrder)

/-- The canonical signed candidate on a principal-extension circuit containing
the new point. -/
noncomputable def lexCircuit [Fintype α]
    (M : Data α) (order : List α) (B : Set α)
    (hB : M.underlying.Indep B) : SignedSubset (α ⊕ Unit) :=
  addCanonicalNewPositive
    (lexCircuitOld M order (lexCircuitBasis M B hB)
      (lexCircuitBasis_isBasis M B hB))

@[simp]
theorem lexCircuit_new_positive [Fintype α]
    (M : Data α) (order : List α) (B : Set α)
    (hB : M.underlying.Indep B) :
    canonicalNew α ∈ (lexCircuit M order B hB).positive := by
  simp [lexCircuit]

/-- The canonical principal-extension circuit candidate is orthogonal to the
lexicographic lift of every old covector. -/
theorem lexCircuit_orthogonal_lexLift
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α) (B : Set α)
    (hB : M.underlying.Indep B) {D : SignedSubset α}
    (hD : M.IsCovector D) :
    (lexCircuit M order B hB).Orthogonal (lexLift order D) := by
  exact addLexCircuitOld_orthogonal_lexLift M order
    (lexCircuitBasis_isBasis M B hB) hD

/-- The candidate circuit is orthogonal to the canonical lift of every old
covector whose support misses the lexicographic list. -/
theorem lexCircuit_orthogonal_lexLift_of_disjoint
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α) (B : Set α)
    (hB : M.underlying.Indep B) {D : SignedSubset α}
    (hD : M.IsCovector D)
    (hdisjoint : Disjoint D.support (order.toFinset : Set α)) :
    (lexCircuit M order B hB).Orthogonal (lexLift order D) := by
  rw [lexLift_eq_map_of_disjoint order D hdisjoint]
  apply addCanonicalNewPositive_orthogonal_map
  exact lexCircuitOld_orthogonal_of_disjoint M order
    (lexCircuitBasis_isBasis M B hB) hD hdisjoint

/-- The signed candidate has exactly the ordinary support classified by the
principal-extension circuit theorem. -/
theorem lexCircuit_support [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α) (B : Set α)
    (hminimal : PrincipalExtension.IsMinimalSpanning M.underlying
      (order.toFinset : Set α) B) :
    (lexCircuit M order B hminimal.1).support =
      insert (canonicalNew α) (Sum.inl '' B) := by
  rw [lexCircuit, addCanonicalNewPositive_support,
    lexCircuitOld_support_eq M
      (lexCircuitBasis_isBasis M B hminimal.1)
      (subset_lexCircuitBasis M B hminimal.1) hminimal]

/-- Consequently the candidate support is an ordinary circuit of the finite
principal extension. -/
theorem principalExtension_isCircuit_lexCircuit_support
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (B : Set α)
    (hminimal : PrincipalExtension.IsMinimalSpanning M.underlying
      (order.toFinset : Set α) B) :
    (PrincipalExtension.matroid M.underlying
      (order.toFinset : Set α) M.underlying_spec.1
      (M.isIndependent_iff_underlying_indep.mp hindep)).IsCircuit
        (lexCircuit M order B hminimal.1).support := by
  rw [lexCircuit_support M order B hminimal]
  exact (PrincipalExtension.matroid_isCircuit_insert_new_image_inl_iff
    M.underlying (order.toFinset : Set α) M.underlying_spec.1
      (M.isIndependent_iff_underlying_indep.mp hindep)).mpr hminimal

/-- The ordinary principal matroid underlying the desired lexicographic
extension. -/
noncomputable def principalLexMatroid [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α)) :
    Matroid (α ⊕ Unit) :=
  PrincipalExtension.matroid M.underlying (order.toFinset : Set α)
    M.underlying_spec.1 (M.isIndependent_iff_underlying_indep.mp hindep)

/-- Exact signed circuit candidates: embedded old circuits, together with the
two orientations of every circuit containing the new point. -/
def lexSignedCircuits [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α) : Set (SignedSubset (α ⊕ Unit)) :=
  {X | (∃ C : SignedSubset α,
      M.IsCircuit C ∧ X = C.map (canonicalOld α)) ∨
    ∃ (B : Set α)
      (hminimal : PrincipalExtension.IsMinimalSpanning M.underlying
        (order.toFinset : Set α) B),
      X = lexCircuit M order B hminimal.1 ∨
        X = -(lexCircuit M order B hminimal.1)}

theorem lexSignedCircuits_neg [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α) {X : SignedSubset (α ⊕ Unit)}
    (hX : X ∈ lexSignedCircuits M order) :
    -X ∈ lexSignedCircuits M order := by
  rcases hX with ⟨C, hC, rfl⟩ | ⟨B, hminimal, hX | hX⟩
  · exact Or.inl ⟨-C, M.neg_isCircuit hC, by simp⟩
  · exact Or.inr ⟨B, hminimal, Or.inr (by simp [hX])⟩
  · exact Or.inr ⟨B, hminimal, Or.inl (by simp [hX])⟩

/-- Every signed candidate has an ordinary circuit support in the principal
extension. -/
theorem lexSignedCircuits_support_isCircuit
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    {X : SignedSubset (α ⊕ Unit)}
    (hX : X ∈ lexSignedCircuits M order) :
    (principalLexMatroid M order hindep).IsCircuit X.support := by
  unfold principalLexMatroid
  rcases hX with ⟨C, hC, rfl⟩ | ⟨B, hminimal, rfl | rfl⟩
  · rw [SignedSubset.support_map]
    change (PrincipalExtension.matroid M.underlying
      (order.toFinset : Set α) M.underlying_spec.1
      (M.isIndependent_iff_underlying_indep.mp hindep)).IsCircuit
        (Sum.inl '' C.support)
    rw [PrincipalExtension.matroid_isCircuit_image_inl_iff]
    exact (M.underlying_spec.2 C.support).mpr ⟨C, hC, rfl⟩
  · exact principalExtension_isCircuit_lexCircuit_support
      M order hindep B hminimal
  · simpa using principalExtension_isCircuit_lexCircuit_support
      M order hindep B hminimal

/-- Conversely every ordinary circuit support of the principal extension has
one of the signed candidates. -/
theorem exists_lexSignedCircuit_support
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    {K : Set (α ⊕ Unit)}
    (hK : (principalLexMatroid M order hindep).IsCircuit K) :
    ∃ X : SignedSubset (α ⊕ Unit),
      X ∈ lexSignedCircuits M order ∧ X.support = K := by
  classical
  unfold principalLexMatroid at hK
  by_cases hpK : canonicalNew α ∈ K
  · let B : Set α := PrincipalExtension.oldPart K
    have hshape : insert (PrincipalExtension.new α) (Sum.inl '' B) = K := by
      rw [← Set.union_singleton]
      apply PrincipalExtension.image_oldPart_union_new_of_mem K
      simpa [canonicalNew, PrincipalExtension.new] using hpK
    have hminimal : PrincipalExtension.IsMinimalSpanning M.underlying
        (order.toFinset : Set α) B := by
      apply (PrincipalExtension.matroid_isCircuit_insert_new_image_inl_iff
        M.underlying (order.toFinset : Set α) M.underlying_spec.1
          (M.isIndependent_iff_underlying_indep.mp hindep)).mp
      rwa [hshape]
    refine ⟨lexCircuit M order B hminimal.1,
      Or.inr ⟨B, hminimal, Or.inl rfl⟩, ?_⟩
    rw [lexCircuit_support M order B hminimal]
    simpa [canonicalNew, PrincipalExtension.new] using hshape
  · let B : Set α := PrincipalExtension.oldPart K
    have hshape : Sum.inl '' B = K :=
      PrincipalExtension.image_oldPart_eq_of_notMem K hpK
    have hBoldCircuit : M.underlying.IsCircuit B := by
      apply (PrincipalExtension.matroid_isCircuit_image_inl_iff
        M.underlying (order.toFinset : Set α) M.underlying_spec.1
          (M.isIndependent_iff_underlying_indep.mp hindep)).mp
      rwa [hshape]
    obtain ⟨C, hC, hCsupport⟩ :=
      (M.underlying_spec.2 B).mp hBoldCircuit
    refine ⟨C.map (canonicalOld α), Or.inl ⟨C, hC, rfl⟩, ?_⟩
    rw [SignedSubset.support_map, hCsupport]
    simpa [canonicalOld] using hshape

/-- All circuit candidates are orthogonal to every primary lexicographic
cocircuit lift. -/
theorem lexSignedCircuit_orthogonal_lexLift
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    {X : SignedSubset (α ⊕ Unit)}
    (hX : X ∈ lexSignedCircuits M order)
    {D : SignedSubset α} (hD : M.IsCocircuit D) :
    X.Orthogonal (lexLift order D) := by
  rcases hX with ⟨C, hC, rfl⟩ | ⟨B, hminimal, rfl | rfl⟩
  · exact map_orthogonal_lexLift order (hD.2.1 hC)
  · exact lexCircuit_orthogonal_lexLift M order B hminimal.1 hD.2.1
  · rw [SignedSubset.orthogonal_comm,
      SignedSubset.orthogonal_neg_right_iff,
      SignedSubset.orthogonal_comm]
    exact lexCircuit_orthogonal_lexLift M order B hminimal.1 hD.2.1

/-- If an old signed support meets the ordered set, its lexicographic lift has
the old support together with the new point. -/
theorem lexLift_support_of_nonempty_inter [DecidableEq α]
    (order : List α) (D : SignedSubset α)
    (hinter : (D.support ∩ (order.toFinset : Set α)).Nonempty) :
    (lexLift order D).support =
      insert (canonicalNew α) (Sum.inl '' D.support) := by
  obtain ⟨a, haD, haOrder⟩ := hinter
  have hp : canonicalNew α ∈ (lexLift order D).support :=
    (canonicalNew_mem_lexLift_support_iff order D).mpr
      ⟨a, List.mem_toFinset.mp haOrder, haD⟩
  have holdPart : PrincipalExtension.oldPart (lexLift order D).support =
      D.support := by
    ext x
    exact canonicalOld_mem_lexLift_support_iff order D x
  have hshape := PrincipalExtension.image_oldPart_union_new_of_mem
    (lexLift order D).support hp
  rw [holdPart] at hshape
  simpa [Set.union_singleton, canonicalNew, PrincipalExtension.new] using
    hshape.symm

/-- If the old support misses the ordered set, the lift has only its embedded
old support. -/
theorem lexLift_support_of_disjoint [DecidableEq α]
    (order : List α) (D : SignedSubset α)
    (hdisjoint : Disjoint D.support (order.toFinset : Set α)) :
    (lexLift order D).support = Sum.inl '' D.support := by
  rw [lexLift_eq_map_of_disjoint order D hdisjoint,
    SignedSubset.support_map]
  rfl

/-- The primary cocircuit candidates are precisely the canonical lifts of old
cocircuits. -/
def lexPrimaryCocircuits [DecidableEq α]
    (M : Data α) (order : List α) : Set (SignedSubset (α ⊕ Unit)) :=
  {E | ∃ D : SignedSubset α,
    M.IsCocircuit D ∧ E = lexLift order D}

theorem lexPrimaryCocircuits_neg [DecidableEq α]
    (M : Data α) (order : List α) {E : SignedSubset (α ⊕ Unit)}
    (hE : E ∈ lexPrimaryCocircuits M order) :
    -E ∈ lexPrimaryCocircuits M order := by
  obtain ⟨D, hD, rfl⟩ := hE
  exact ⟨-D, M.neg_isCocircuit hD, by simp⟩

/-- Every primary candidate has an ordinary cocircuit support in the principal
extension. -/
theorem lexPrimaryCocircuit_support_isCocircuit
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    {E : SignedSubset (α ⊕ Unit)}
    (hE : E ∈ lexPrimaryCocircuits M order) :
    (principalLexMatroid M order hindep).IsCocircuit E.support := by
  obtain ⟨D, hD, rfl⟩ := hE
  unfold principalLexMatroid
  by_cases hinter :
      (D.support ∩ (order.toFinset : Set α)).Nonempty
  · rw [lexLift_support_of_nonempty_inter order D hinter]
    apply PrincipalExtension.matroid_isCocircuit_insert_new_image_inl_of_nonempty_inter
    · exact M.isCocircuit_support hD
    · exact hinter
  · have hdisjoint : Disjoint D.support (order.toFinset : Set α) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hinter
    rw [lexLift_support_of_disjoint order D hdisjoint]
    exact PrincipalExtension.matroid_isCocircuit_image_inl_of_disjoint
      M.underlying (order.toFinset : Set α) M.underlying_spec.1
        (M.isIndependent_iff_underlying_indep.mp hindep)
        (M.isCocircuit_support hD) hdisjoint

/-- Every ordinary cocircuit of the principal extension that contains the new
point is covered by a primary lexicographic lift. -/
theorem exists_lexPrimaryCocircuit_support_of_new_mem
    [Fintype α] [DecidableEq α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    {K : Set (α ⊕ Unit)}
    (hK : (principalLexMatroid M order hindep).IsCocircuit K)
    (hpK : canonicalNew α ∈ K) :
    ∃ E : SignedSubset (α ⊕ Unit),
      E ∈ lexPrimaryCocircuits M order ∧ E.support = K := by
  unfold principalLexMatroid at hK
  have hpK' : PrincipalExtension.new α ∈ K := by
    simpa [canonicalNew, PrincipalExtension.new] using hpK
  obtain ⟨hKold, hmeet⟩ :=
    PrincipalExtension.isCocircuit_oldPart_and_nonempty_inter_of_new_mem
      M.underlying (order.toFinset : Set α) M.underlying_spec.1
        (M.isIndependent_iff_underlying_indep.mp hindep) hK hpK'
  obtain ⟨D, hD, hDsupport⟩ :=
    M.exists_isCocircuit_support_eq hKold
  have hmeetD : (D.support ∩ (order.toFinset : Set α)).Nonempty := by
    simpa [hDsupport] using hmeet
  refine ⟨lexLift order D, ⟨D, hD, rfl⟩, ?_⟩
  rw [lexLift_support_of_nonempty_inter order D hmeetD, hDsupport]
  have hshape := PrincipalExtension.image_oldPart_union_new_of_mem K hpK'
  change insert (PrincipalExtension.new α)
    (Sum.inl '' PrincipalExtension.oldPart K) = K
  rw [← Set.union_singleton]
  exact hshape

end OrientedMatroid
end BeyondSperner
