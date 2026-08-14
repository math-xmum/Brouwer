import BeyondSperner.OrientedMatroid.LexicographicSecondary

/-!
# One-point and lexicographic extensions

Formalization of Section 8 and Appendix A.2.  Lexicographic extensions are
characterized by their cocircuits, matching Las Vergnas' definition quoted by Ivanov.  The
existence theorem is constructed in the imported localization, circuit, principal-extension,
secondary-cocircuit, and conditional-assembly modules; it is not postulated here.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid

variable {α β : Type*} [DecidableEq α]

/-- A one-point extension `M + p` of an oriented matroid. -/
structure OnePointExtension (M : Data α) (β : Type*) where
  matroid : Data β
  old : α ↪ β
  new : β
  new_not_old : new ∉ Set.range old
  ground_eq : Set.range old ∪ {new} = Set.univ
  old_isCircuit_iff : ∀ C : SignedSubset α,
    matroid.IsCircuit (C.map old) ↔ M.IsCircuit C

namespace OnePointExtension

variable {M : Data α} (L : OnePointExtension M β)

/-- Image of an old unsigned set in the extension. -/
def oldSet (X : Set α) : Set β := L.old '' X

/-- Add the new element with the same sign as a prescribed old support element. -/
noncomputable def addNewSameSign (D : SignedSubset α) (a : α) : SignedSubset β := by
  classical
  by_cases ha : a ∈ D.positive
  · exact {
      positive := L.old '' D.positive ∪ {L.new}
      negative := L.old '' D.negative
      disjoint := by
        rw [Set.disjoint_left]
        rintro x (hx | hx) ⟨y, hy, rfl⟩
        · obtain ⟨z, hz, hzy⟩ := hx
          exact Set.disjoint_left.1 D.disjoint hz (L.old.injective hzy ▸ hy)
        · exact L.new_not_old ⟨y, by simpa using hx⟩ }
  · exact {
      positive := L.old '' D.positive
      negative := L.old '' D.negative ∪ {L.new}
      disjoint := by
        rw [Set.disjoint_left]
        rintro _ ⟨x, hx, rfl⟩ (hy | hy)
        · obtain ⟨z, hz, hzx⟩ := hy
          exact Set.disjoint_left.1 D.disjoint hx (L.old.injective hzx.symm ▸ hz)
        · exact L.new_not_old ⟨x, by simpa using hy⟩ }

omit [DecidableEq α] in @[simp]
theorem new_mem_addNewSameSign_support (D : SignedSubset α) (a : α) :
    L.new ∈ (L.addNewSameSign D a).support := by
  classical
  by_cases ha : a ∈ D.positive
  · exact Or.inl (by simp [addNewSameSign, ha])
  · exact Or.inr (by simp [addNewSameSign, ha])

omit [DecidableEq α] in @[simp]
theorem addNewSameSign_comap_old (D : SignedSubset α) (a : α) :
    (L.addNewSameSign D a).comap L.old = D := by
  classical
  have hne (x : α) : L.old x ≠ L.new := by
    intro h
    exact L.new_not_old ⟨x, h⟩
  by_cases ha : a ∈ D.positive
  · ext x <;> simp [addNewSameSign, ha, hne, L.old.injective.eq_iff]
  · ext x <;> simp [addNewSameSign, ha, hne, L.old.injective.eq_iff]

omit [DecidableEq α] in theorem old_mem_addNewSameSign_support_iff
    (D : SignedSubset α) (a x : α) :
    L.old x ∈ (L.addNewSameSign D a).support ↔ x ∈ D.support := by
  have h := congrArg SignedSubset.support (L.addNewSameSign_comap_old D a)
  rw [SignedSubset.support_comap] at h
  exact Set.ext_iff.mp h x

omit [DecidableEq α] in theorem addNewSameSign_sameSignWithin
    (D : SignedSubset α) {a : α} (ha : a ∈ D.support) :
    (L.addNewSameSign D a).SameSignWithin L.new (L.old a) := by
  classical
  rcases ha with hapos | haneg
  · exact Or.inl ⟨by simp [addNewSameSign, hapos],
        by simp [addNewSameSign, hapos]⟩
  · have hnotpos : a ∉ D.positive := fun h ↦
      Set.disjoint_left.1 D.disjoint h haneg
    exact Or.inr ⟨by simp [addNewSameSign, hnotpos],
      by simp [addNewSameSign, hnotpos, haneg]⟩

/-- The extension has the same rank when it preserves all bases. -/
def PreservesRank : Prop :=
  ∀ B : Set α, M.IsBasis B ↔ L.matroid.IsBasis (L.oldSet B)

/-- The first member of an ordered list whose image occurs in a signed support. -/
def IsFirstSupported (order : List α) (D : SignedSubset β) (i : Fin order.length) : Prop :=
  L.old order[i] ∈ D.support ∧
    ∀ j : Fin order.length, j < i → L.old order[j] ∉ D.support

/--
Las Vergnas' cocircuit characterization of the lexicographic extension associated with an ordered
independent list `a₁,...,aₖ`.
-/
def IsLexicographicFor (order : List α) : Prop :=
  order.Nodup ∧ M.IsIndependent (order.toFinset : Set α) ∧ L.PreservesRank ∧
    -- Appendix A.2(a).
    (∀ C : SignedSubset α,
      M.IsCocircuit C → Disjoint C.support (order.toFinset : Set α) →
        L.matroid.IsCocircuit (C.map L.old)) ∧
    -- Appendix A.2(b), including the “moreover” clause.
    (∀ D : SignedSubset β,
      L.new ∈ D.support →
      (L.matroid.IsCocircuit D →
        ∃ i : Fin order.length, L.IsFirstSupported order D i) ∧
      (L.matroid.IsCocircuit D ↔
        M.IsCocircuit (D.comap L.old) ∧
          ∃ i : Fin order.length,
            L.IsFirstSupported order D i ∧
              D.SameSignWithin L.new (L.old order[i])))

omit [DecidableEq α] in
/-- A finite ordered list with some supported image has a first supported position. -/
theorem exists_isFirstSupported
    (order : List α) (D : SignedSubset β)
    (hsupported : ∃ a ∈ order, L.old a ∈ D.support) :
    ∃ i : Fin order.length, L.IsFirstSupported order D i := by
  classical
  have hget : ∃ i : Fin order.length, L.old order[i] ∈ D.support :=
    List.exists_mem_iff_get.mp hsupported
  have hnat : ∃ n : ℕ, ∃ hn : n < order.length, L.old order[n] ∈ D.support := by
    obtain ⟨i, hi⟩ := hget
    exact ⟨i, i.isLt, hi⟩
  let n : ℕ := Nat.find hnat
  have hnlt : n < order.length := (Nat.find_spec hnat).choose
  have hnsupported : L.old order[n] ∈ D.support :=
    (Nat.find_spec hnat).choose_spec
  let i : Fin order.length := ⟨n, hnlt⟩
  refine ⟨i, hnsupported, ?_⟩
  intro j hji hj
  have hji' : j.val < i.val := hji
  change j.val < n at hji'
  change j.val < Nat.find hnat at hji'
  exact Nat.find_min hnat hji' ⟨j.isLt, hj⟩

/-- A cocircuit meeting the lexicographic list lifts to a cocircuit containing the new element. -/
theorem exists_liftedCocircuit
    [Finite α] (order : List α) (hlex : L.IsLexicographicFor order)
    {D : SignedSubset α} (hD : M.IsCocircuit D)
    (hDorder : (D.support ∩ (order.toFinset : Set α)).Nonempty) :
    ∃ E : SignedSubset β,
      L.matroid.IsCocircuit E ∧ L.new ∈ E.support ∧ E.comap L.old = D := by
  obtain ⟨a, haD, haorder⟩ := hDorder
  let E₀ : SignedSubset β := D.map L.old
  have hsome : ∃ b ∈ order, L.old b ∈ E₀.support := by
    refine ⟨a, ?_, ?_⟩
    · exact List.mem_toFinset.mp haorder
    · simpa [E₀, SignedSubset.support_map] using haD
  obtain ⟨i, hfirst₀⟩ := L.exists_isFirstSupported order E₀ hsome
  have haiD : order[i] ∈ D.support :=
    by simpa [E₀, SignedSubset.support_map] using hfirst₀.1
  let E : SignedSubset β := L.addNewSameSign D order[i]
  have hnew : L.new ∈ E.support := by simp [E]
  have hfirst : L.IsFirstSupported order E i := by
    refine ⟨(L.old_mem_addNewSameSign_support_iff D order[i] order[i]).mpr haiD, ?_⟩
    intro j hji hj
    apply hfirst₀.2 j hji
    have hjD : order[j] ∈ D.support :=
      (L.old_mem_addNewSameSign_support_iff D order[i] order[j]).mp hj
    simpa [E₀, SignedSubset.support_map] using hjD
  have hsame : E.SameSignWithin L.new (L.old order[i]) := by
    simpa [E] using L.addNewSameSign_sameSignWithin D haiD
  have hcomap : E.comap L.old = D := by simp [E]
  have hEcocircuit : L.matroid.IsCocircuit E := by
    apply ((hlex.2.2.2.2 E hnew).2).mpr
    exact ⟨by simpa [hcomap] using hD, i, hfirst, hsame⟩
  exact ⟨E, hEcocircuit, hnew, hcomap⟩

/-- If an old cocircuit meets the lexicographic list in exactly `a`, it has a lift whose new
element has the same sign as the image of `a`. -/
theorem exists_liftedCocircuit_sameSignWithin
    [Finite α] (order : List α) (hlex : L.IsLexicographicFor order)
    {D : SignedSubset α} (hD : M.IsCocircuit D) {a : α}
    (hinter : D.support ∩ (order.toFinset : Set α) = {a}) :
    ∃ E : SignedSubset β,
      L.matroid.IsCocircuit E ∧ L.new ∈ E.support ∧ E.comap L.old = D ∧
        E.SameSignWithin L.new (L.old a) := by
  have haDorder : a ∈ D.support ∩ (order.toFinset : Set α) := by
    rw [hinter]
    simp
  obtain ⟨E, hE, hnew, hcomap⟩ :=
    L.exists_liftedCocircuit order hlex hD ⟨a, haDorder⟩
  obtain ⟨_, i, hfirst, hsame⟩ := ((hlex.2.2.2.2 E hnew).2).mp hE
  have hiD : order[i] ∈ D.support := by
    have hiComap : order[i] ∈ (E.comap L.old).support := by
      rw [SignedSubset.support_comap]
      exact hfirst.1
    simpa [hcomap] using hiComap
  have hiOrder : order[i] ∈ (order.toFinset : Set α) := by
    exact List.mem_toFinset.mpr (List.get_mem order i)
  have hia : order[i] = a := by
    have : order[i] ∈ D.support ∩ (order.toFinset : Set α) := ⟨hiD, hiOrder⟩
    rw [hinter] at this
    simpa using this
  exact ⟨E, hE, hnew, hcomap, by simpa [hia] using hsame⟩

/-- A cocircuit containing the head of the lexicographic list lifts with the new element carrying
the same sign as that head. -/
theorem exists_liftedCocircuit_sameSignWithin_head
    [Finite α] (a : α) (tail : List α)
    (hlex : L.IsLexicographicFor (a :: tail))
    {D : SignedSubset α} (hD : M.IsCocircuit D) (haD : a ∈ D.support) :
    ∃ E : SignedSubset β,
      L.matroid.IsCocircuit E ∧ L.new ∈ E.support ∧ E.comap L.old = D ∧
        E.SameSignWithin L.new (L.old a) := by
  obtain ⟨E, hE, hnew, hcomap⟩ :=
    L.exists_liftedCocircuit (a :: tail) hlex hD ⟨a, haD, by simp⟩
  obtain ⟨_, i, hfirst, hsame⟩ := ((hlex.2.2.2.2 E hnew).2).mp hE
  have hheadE : L.old a ∈ E.support := by
    have : a ∈ (E.comap L.old).support := by simpa [hcomap] using haD
    rwa [SignedSubset.support_comap] at this
  have hiZero : i.val = 0 := by
    by_contra hi
    have hzeroLt : (0 : Fin (a :: tail).length) < i := by
      exact Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero hi)
    exact hfirst.2 0 hzeroLt (by simpa using hheadE)
  have hia : (a :: tail)[i] = a := by
    have hi : i = (0 : Fin (a :: tail).length) := Fin.ext hiZero
    subst i
    simp
  exact ⟨E, hE, hnew, hcomap, by simpa [hia] using hsame⟩

end OnePointExtension

/-- The conditional one-point extension assembled from the exact circuit
signing and compatible cocircuit signings. -/
noncomputable def assembledLexExtension
    [Fintype α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    OnePointExtension M (α ⊕ Unit) where
  matroid := lexExtensionData M order hindep hsecondary
  old := canonicalOld α
  new := canonicalNew α
  new_not_old := by
    rintro ⟨x, hx⟩
    simp [canonicalOld, canonicalNew] at hx
  ground_eq := by
    ext z
    rcases z with x | u
    · simp [canonicalOld, canonicalNew]
    · obtain rfl : u = () := Subsingleton.elim _ _
      simp [canonicalOld, canonicalNew]
  old_isCircuit_iff := by
    intro C
    change C.map (canonicalOld α) ∈
      (lexExtensionData M order hindep hsecondary).circuits ↔
        M.IsCircuit C
    rw [lexExtensionData_circuits,
      map_mem_lexSignedCircuits_iff]

@[simp]
theorem assembledLexExtension_old
    [Fintype α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    (assembledLexExtension M order hindep hsecondary).old =
      canonicalOld α := rfl

@[simp]
theorem assembledLexExtension_new
    [Fintype α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    (assembledLexExtension M order hindep hsecondary).new =
      canonicalNew α := rfl

@[simp]
theorem assembledLexExtension_isFirstSupported_iff
    [Fintype α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep)
    (D : SignedSubset (α ⊕ Unit)) (i : Fin order.length) :
    (assembledLexExtension M order hindep hsecondary).IsFirstSupported
        order D i ↔
      LexFirstSupported order (D.comap (canonicalOld α)) i := by
  rfl

/-- In the assembled extension, every signed cocircuit containing the new
point is exactly a primary lexicographic lift. -/
theorem assembled_isCocircuit_new_iff_exists_lexLift
    [Fintype α]
    (M : Data α) (order : List α)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep)
    {D : SignedSubset (α ⊕ Unit)}
    (hpD : canonicalNew α ∈ D.support) :
    (assembledLexExtension M order hindep hsecondary).matroid.IsCocircuit D ↔
      ∃ C : SignedSubset α,
        M.IsCocircuit C ∧ D = lexLift order C := by
  let P := lexOrthogonalPair M order hindep hsecondary
  constructor
  · intro hD
    have hDcompat : D ∈ compatibleLexCocircuits M order hindep :=
      (lexExtensionData_isCocircuit_iff_compatible
        M order hindep hsecondary).mp hD
    obtain ⟨E, hEprimary, hEsupport⟩ :=
      exists_lexPrimaryCocircuit_support_of_new_mem
        M order hindep hDcompat.1 hpD
    obtain ⟨C, hC, rfl⟩ := hEprimary
    have hEcompat : lexLift order C ∈
        compatibleLexCocircuits M order hindep :=
      lexPrimaryCocircuit_mem_compatible M order hindep
        ⟨C, hC, rfl⟩
    have hsign := P.swap.eq_or_eq_neg_of_circuit_support_subset
      hDcompat hEcompat (by rw [hEsupport])
    rcases hsign with hEq | hEq
    · exact ⟨C, hC, hEq⟩
    · refine ⟨-C, M.neg_isCocircuit hC, ?_⟩
      simpa using hEq
  · rintro ⟨C, hC, rfl⟩
    apply (lexExtensionData_isCocircuit_iff_compatible
      M order hindep hsecondary).mpr
    exact lexPrimaryCocircuit_mem_compatible M order hindep
      ⟨C, hC, rfl⟩

omit [DecidableEq α] in
/-- A signed set on the canonical carrier is forced to be `lexLift order C`
once its old restriction is `C` and its new sign agrees with the first
supported ordered coordinate. -/
theorem eq_lexLift_of_comap_of_first_same
    (order : List α) (C : SignedSubset α)
    {D : SignedSubset (α ⊕ Unit)} {i : Fin order.length}
    (hcomap : D.comap (canonicalOld α) = C)
    (hfirst : LexFirstSupported order C i)
    (hsame : D.SameSignWithin (canonicalNew α)
      (canonicalOld α order[i])) :
    D = lexLift order C := by
  classical
  have holdPos (x : α) :
      canonicalOld α x ∈ D.positive ↔ x ∈ C.positive := by
    change x ∈ (D.comap (canonicalOld α)).positive ↔ x ∈ C.positive
    rw [hcomap]
  have holdNeg (x : α) :
      canonicalOld α x ∈ D.negative ↔ x ∈ C.negative := by
    change x ∈ (D.comap (canonicalOld α)).negative ↔ x ∈ C.negative
    rw [hcomap]
  have hLiftSame := lexLift_sameSignWithin hfirst
  have hpSame : D.SameSignAt (lexLift order C) (canonicalNew α) := by
    rcases hsame with hDpos | hDneg <;>
      rcases hLiftSame with hEpos | hEneg
    · exact Or.inl ⟨hDpos.1, hEpos.1⟩
    · have hCpos : order[i] ∈ C.positive :=
        (holdPos order[i]).mp hDpos.2
      have hCneg : order[i] ∈ C.negative :=
        (canonicalOld_mem_lexLift_negative_iff order C order[i]).mp hEneg.2
      exact (Set.disjoint_left.1 C.disjoint hCpos hCneg).elim
    · have hCneg : order[i] ∈ C.negative :=
        (holdNeg order[i]).mp hDneg.2
      have hCpos : order[i] ∈ C.positive :=
        (canonicalOld_mem_lexLift_positive_iff order C order[i]).mp hEpos.2
      exact (Set.disjoint_left.1 C.disjoint hCpos hCneg).elim
    · exact Or.inr ⟨hDneg.1, hEneg.1⟩
  apply SignedSubset.ext
  · ext z
    rcases z with x | u
    · exact (holdPos x).trans
        (canonicalOld_mem_lexLift_positive_iff order C x).symm
    · obtain rfl : u = () := Subsingleton.elim _ _
      exact hpSame.positive_iff
  · ext z
    rcases z with x | u
    · exact (holdNeg x).trans
        (canonicalOld_mem_lexLift_negative_iff order C x).symm
    · obtain rfl : u = () := Subsingleton.elim _ _
      exact hpSame.negative_iff

/-- Subject only to the isolated secondary-signing obligation, the assembled
one-point extension satisfies the full cocircuit characterization of a
lexicographic extension. -/
theorem assembledLexExtension_isLexicographicFor
    [Fintype α]
    (M : Data α) (order : List α) (hnodup : order.Nodup)
    (hindep : M.IsIndependent (order.toFinset : Set α))
    (hsecondary : HasSecondaryCocircuitSignings M order hindep) :
    (assembledLexExtension M order hindep hsecondary).IsLexicographicFor
      order := by
  let L := assembledLexExtension M order hindep hsecondary
  refine ⟨hnodup, hindep, ?_, ?_, ?_⟩
  · intro B
    rw [M.isBasis_iff_underlying_isBase,
      L.matroid.isBasis_iff_underlying_isBase]
    rw [show L.matroid.underlying = principalLexMatroid M order hindep by
      exact lexExtensionData_underlying_eq M order hindep hsecondary]
    change M.underlying.IsBase B ↔
      (principalLexMatroid M order hindep).IsBase (Sum.inl '' B)
    unfold principalLexMatroid
    exact (PrincipalExtension.matroid_isBase_image_inl_iff
      M.underlying (order.toFinset : Set α) M.underlying_spec.1
        (M.isIndependent_iff_underlying_indep.mp hindep)).symm
  · intro C hC hdisjoint
    apply (lexExtensionData_isCocircuit_iff_compatible
      M order hindep hsecondary).mpr
    apply lexPrimaryCocircuit_mem_compatible M order hindep
    refine ⟨C, hC, ?_⟩
    exact (lexLift_eq_map_of_disjoint order C hdisjoint).symm
  · intro D hpD
    have hpD' : canonicalNew α ∈ D.support := by
      simpa [L] using hpD
    constructor
    · intro hDcocircuit
      obtain ⟨C, hC, hEq⟩ :=
        (assembled_isCocircuit_new_iff_exists_lexLift
          M order hindep hsecondary hpD').mp hDcocircuit
      subst D
      have hsome :=
        (canonicalNew_mem_lexLift_support_iff order C).mp hpD'
      obtain ⟨i, hi⟩ := exists_lexFirstSupported_iff.mpr hsome
      refine ⟨i, ?_⟩
      simpa [L] using hi
    · constructor
      · intro hDcocircuit
        obtain ⟨C, hC, hEq⟩ :=
          (assembled_isCocircuit_new_iff_exists_lexLift
            M order hindep hsecondary hpD').mp hDcocircuit
        subst D
        have hsome :=
          (canonicalNew_mem_lexLift_support_iff order C).mp hpD'
        obtain ⟨i, hi⟩ := exists_lexFirstSupported_iff.mpr hsome
        refine ⟨?_, i, ?_, ?_⟩
        · simpa [L] using hC
        · simpa [L] using hi
        · simpa [L] using lexLift_sameSignWithin hi
      · rintro ⟨hDold, i, hfirst, hsame⟩
        let C : SignedSubset α := D.comap (canonicalOld α)
        have hfirstC : LexFirstSupported order C i := by
          simpa [L, C] using hfirst
        have hEq : D = lexLift order C :=
          eq_lexLift_of_comap_of_first_same order C rfl hfirstC
            (by simpa [L] using hsame)
        apply (assembled_isCocircuit_new_iff_exists_lexLift
          M order hindep hsecondary hpD').mpr
        exact ⟨C, by simpa [L, C] using hDold, hEq⟩

/-- Existence of a lexicographic extension on the canonical carrier `α ⊕ Unit`. -/
theorem exists_lexicographicExtension
    [Fintype α] (M : Data α) (order : List α) (hnodup : order.Nodup)
    (hindep : M.IsIndependent (order.toFinset : Set α)) :
    ∃ L : OnePointExtension M (α ⊕ Unit), L.IsLexicographicFor order := by
  have hstrict : HasStrictSecondaryCocircuitSignings M order hindep := by
    exact hasStrictSecondaryCocircuitSignings M order hindep
  have hsecondary : HasSecondaryCocircuitSignings M order hindep :=
    hstrict.toHasSecondary M order hindep
  exact ⟨assembledLexExtension M order hindep hsecondary,
    assembledLexExtension_isLexicographicFor
      M order hnodup hindep hsecondary⟩

end OrientedMatroid

end BeyondSperner
