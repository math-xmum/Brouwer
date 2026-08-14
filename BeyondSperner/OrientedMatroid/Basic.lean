import BeyondSperner.OrientedMatroid.WeakStrongElimination
import BeyondSperner.OrientedMatroid.MatroidFromCircuits

/-!
# Oriented matroids by signed circuits

This file builds the ordinary-matroid, convexity, circuit, and cocircuit API on
the weak signed-circuit core.  Strong elimination is imported as a theorem,
not stored as an additional field.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid

variable {α : Type*}

namespace Data

variable (M : Data α)

/-- A set is independent when it contains no circuit support. -/
def IsIndependent (X : Set α) : Prop :=
  ∀ ⦃C : SignedSubset α⦄, M.IsCircuit C → ¬ C.support ⊆ X

/-- A basis is a maximal independent subset, exactly as in Section 5. -/
def IsBasis (B : Set α) : Prop := Maximal M.IsIndependent B

/-- Oriented-matroid convex-hull membership from Section 5. -/
def MemConvexHull (x : α) (X : Set α) : Prop :=
  x ∈ X ∨
    ∃ C : SignedSubset α,
      M.IsCircuit C ∧ C.positive ⊆ X ∧ C.negative = {x}

/-- The convex hull of `X`. -/
def convexHull (X : Set α) : Set α := {x | M.MemConvexHull x X}

@[simp]
theorem mem_convexHull_iff {x : α} {X : Set α} :
    x ∈ M.convexHull X ↔ M.MemConvexHull x X := Iff.rfl

theorem memConvexHull_of_mem {x : α} {X : Set α} (hx : x ∈ X) :
    M.MemConvexHull x X := Or.inl hx

theorem memConvexHull_mono {x : α} {X Y : Set α} (hXY : X ⊆ Y)
    (hx : M.MemConvexHull x X) : M.MemConvexHull x Y := by
  rcases hx with hx | ⟨C, hC, hpos, hneg⟩
  · exact Or.inl (hXY hx)
  · exact Or.inr ⟨C, hC, hpos.trans hXY, hneg⟩

/-- An oriented matroid is acyclic if no circuit has empty negative part. -/
def IsAcyclic : Prop :=
  ∀ ⦃C : SignedSubset α⦄, M.IsCircuit C → C.negative.Nonempty

theorem IsAcyclic.positive_nonempty {M : Data α} (hM : M.IsAcyclic)
    {C : SignedSubset α} (hC : M.IsCircuit C) : C.positive.Nonempty := by
  have hneg : (-C).negative.Nonempty := hM (M.neg_isCircuit hC)
  simpa using hneg

/-- A good basis contains the distinguished element in its oriented convex hull. -/
def IsGoodBasis (b : α) (B : Set α) : Prop :=
  M.IsBasis B ∧ M.MemConvexHull b B

/-- The span/closure definition used in Appendix A.2. -/
def MemSpan (x : α) (X : Set α) : Prop :=
  x ∈ X ∨
    ∃ C : SignedSubset α,
      M.IsCircuit C ∧ x ∈ C.support ∧ C.support \ {x} ⊆ X

/-- A covector is a signed subset orthogonal to every circuit. -/
def IsCovector (D : SignedSubset α) : Prop :=
  ∀ ⦃C : SignedSubset α⦄, M.IsCircuit C → C.Orthogonal D

/-- A cocircuit is a support-minimal nonzero covector. -/
def IsCocircuit (D : SignedSubset α) : Prop :=
  D.support.Nonempty ∧ M.IsCovector D ∧
    ∀ ⦃E : SignedSubset α⦄, E.support.Nonempty → M.IsCovector E →
      E.support ⊆ D.support → D.support ⊆ E.support

theorem neg_isCovector {D : SignedSubset α} (hD : M.IsCovector D) :
    M.IsCovector (-D) := by
  intro C hC
  simpa using hD hC

/-- Covectors are closed under sign-vector composition. -/
theorem IsCovector.compose {D E : SignedSubset α}
    (hD : M.IsCovector D) (hE : M.IsCovector E) :
    M.IsCovector (D.compose E) := by
  intro C hC
  by_cases hinter : Disjoint C.support D.support
  · rcases hE hC with hCE | ⟨u, hu, v, hv, husame, hvopp⟩
    · left
      rw [SignedSubset.support_compose]
      exact hinter.union_right hCE
    · right
      have huD : u ∉ D.support := fun huD ↦
        Set.disjoint_left.1 hinter hu.1 huD
      have hvD : v ∉ D.support := fun hvD ↦
        Set.disjoint_left.1 hinter hv.1 hvD
      have hucomp : u ∈ C.support ∩ (D.compose E).support := by
        rw [SignedSubset.support_compose]
        exact ⟨hu.1, Or.inr hu.2⟩
      have hvcomp : v ∈ C.support ∩ (D.compose E).support := by
        rw [SignedSubset.support_compose]
        exact ⟨hv.1, Or.inr hv.2⟩
      refine ⟨u, hucomp, v, hvcomp, ?_, ?_⟩
      · rcases husame with husame | husame
        · exact Or.inl ⟨husame.1, Or.inr ⟨husame.2, huD⟩⟩
        · exact Or.inr ⟨husame.1, Or.inr ⟨husame.2, huD⟩⟩
      · rcases hvopp with hvopp | hvopp
        · exact Or.inl ⟨hvopp.1, Or.inr ⟨hvopp.2, hvD⟩⟩
        · exact Or.inr ⟨hvopp.1, Or.inr ⟨hvopp.2, hvD⟩⟩
  · rcases hD hC with hCD | ⟨u, hu, v, hv, husame, hvopp⟩
    · exact (hinter hCD).elim
    · right
      have hucomp : u ∈ C.support ∩ (D.compose E).support := by
        rw [SignedSubset.support_compose]
        exact ⟨hu.1, Or.inl hu.2⟩
      have hvcomp : v ∈ C.support ∩ (D.compose E).support := by
        rw [SignedSubset.support_compose]
        exact ⟨hv.1, Or.inl hv.2⟩
      refine ⟨u, hucomp, v, hvcomp, ?_, ?_⟩
      · rcases husame with husame | husame
        · exact Or.inl ⟨husame.1, Or.inl husame.2⟩
        · exact Or.inr ⟨husame.1, Or.inl husame.2⟩
      · rcases hvopp with hvopp | hvopp
        · exact Or.inl ⟨hvopp.1, Or.inl hvopp.2⟩
        · exact Or.inr ⟨hvopp.1, Or.inl hvopp.2⟩

theorem neg_isCocircuit {D : SignedSubset α} (hD : M.IsCocircuit D) :
    M.IsCocircuit (-D) := by
  refine ⟨by simpa using hD.1, M.neg_isCovector hD.2.1, ?_⟩
  intro E hEnonempty hEcovector hEsub
  have hsub : E.support ⊆ D.support := by simpa using hEsub
  have hDsub := hD.2.2 hEnonempty hEcovector hsub
  simpa using hDsub

/-- A mathlib matroid underlies `M` when its circuits are exactly the unsigned supports. -/
def Underlies (U : Matroid α) : Prop :=
  U.E = Set.univ ∧
    ∀ X : Set α, U.IsCircuit X ↔
      ∃ C : SignedSubset α, M.IsCircuit C ∧ C.support = X

/-- The unsigned circuit predicate obtained by forgetting all signs. -/
def IsSupportCircuit (X : Set α) : Prop :=
  ∃ C : SignedSubset α, M.IsCircuit C ∧ C.support = X

private theorem supportCircuit_empty : ¬ M.IsSupportCircuit ∅ := by
  rintro ⟨C, hC, hsupport⟩
  simpa [hsupport] using M.circuit_support_nonempty hC

private theorem supportCircuit_antichain :
    IsAntichain (· ⊆ ·) {X : Set α | M.IsSupportCircuit X} := by
  intro X hX Y hY hXY hsub
  obtain ⟨C, hC, rfl⟩ := hX
  obtain ⟨D, hD, rfl⟩ := hY
  rcases M.eq_or_eq_neg_of_support_subset hC hD hsub with h | h
  · exact hXY (congrArg SignedSubset.support h)
  · apply hXY
    rw [h, SignedSubset.support_neg]

private theorem exists_opposite_orientation
    {C D : SignedSubset α} (hD : M.IsCircuit D) {e : α}
    (heC : e ∈ C.support) (heD : e ∈ D.support) :
    ∃ D' : SignedSubset α,
      M.IsCircuit D' ∧ D'.support = D.support ∧ C.OppositeAt D' e := by
  change e ∈ C.positive ∪ C.negative at heC
  change e ∈ D.positive ∪ D.negative at heD
  rcases heC with heCp | heCn <;> rcases heD with heDp | heDn
  · exact ⟨-D, M.neg_isCircuit hD, by simp,
      Or.inl ⟨heCp, by simpa using heDp⟩⟩
  · exact ⟨D, hD, rfl, Or.inl ⟨heCp, heDn⟩⟩
  · exact ⟨D, hD, rfl, Or.inr ⟨heCn, heDp⟩⟩
  · exact ⟨-D, M.neg_isCircuit hD, by simp,
      Or.inr ⟨heCn, by simpa using heDn⟩⟩

private theorem supportCircuit_elimination
    {X Y : Set α} {e : α}
    (hX : M.IsSupportCircuit X) (hY : M.IsSupportCircuit Y)
    (hXY : X ≠ Y) (heX : e ∈ X) (heY : e ∈ Y) :
    ∃ Z, M.IsSupportCircuit Z ∧ e ∉ Z ∧ Z ⊆ X ∪ Y := by
  obtain ⟨C, hC, hCX⟩ := hX
  obtain ⟨D, hD, hDY⟩ := hY
  have heC : e ∈ C.support := by simpa [hCX] using heX
  have heD : e ∈ D.support := by simpa [hDY] using heY
  obtain ⟨D', hD', hD'support, hopposite⟩ :=
    M.exists_opposite_orientation hD heC heD
  have hne : C ≠ -D' := by
    intro h
    apply hXY
    calc
      X = C.support := hCX.symm
      _ = (-D').support := congrArg SignedSubset.support h
      _ = D'.support := SignedSubset.support_neg D'
      _ = D.support := hD'support
      _ = Y := hDY
  obtain ⟨Z, hZ, hElim⟩ := M.weakElimination hC hD' hne hopposite
  have hZsub : Z.support ⊆ (C.support ∪ D'.support) \ {e} := by
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨hzCD, hze⟩ := hElim.1 hz
      refine ⟨?_, hze⟩
      rcases hzCD with hzC | hzD
      · exact Or.inl (Or.inl hzC)
      · exact Or.inr (Or.inl hzD)
    · obtain ⟨hzCD, hze⟩ := hElim.2 hz
      refine ⟨?_, hze⟩
      rcases hzCD with hzC | hzD
      · exact Or.inl (Or.inr hzC)
      · exact Or.inr (Or.inr hzD)
  refine ⟨Z.support, ⟨Z, hZ, rfl⟩, ?_, ?_⟩
  · intro heZ
    exact (hZsub heZ).2 (Set.mem_singleton e)
  · intro z hz
    have hz' := (hZsub hz).1
    rw [hCX, hD'support, hDY] at hz'
    exact hz'

/-- The finite ordinary circuit system obtained from the supports of oriented circuits. -/
noncomputable def supportCircuitSystem [Finite α] : FiniteCircuitSystem α where
  ground := Set.univ
  IsCircuit := M.IsSupportCircuit
  empty_not_isCircuit := M.supportCircuit_empty
  circuit_antichain := M.supportCircuit_antichain
  circuit_elimination := by
    intro C₁ C₂ e hC₁ hC₂ hne heC₁ heC₂
    exact M.supportCircuit_elimination hC₁ hC₂ hne heC₁ heC₂
  circuit_finite := by
    intro C _
    exact Set.toFinite C
  circuit_subset_ground := by
    intro C _
    exact Set.subset_univ C

/-- The circuit axioms determine a unique underlying ordinary matroid. -/
theorem existsUnique_underlying [Finite α] : ∃! U : Matroid α, M.Underlies U := by
  let S := M.supportCircuitSystem
  refine ⟨S.matroid, ?_, ?_⟩
  · constructor
    · simp [S, supportCircuitSystem]
    · intro X
      change S.matroid.IsCircuit X ↔ M.IsSupportCircuit X
      rw [FiniteCircuitSystem.matroid_isCircuit]
      rfl
  · intro U hU
    apply Matroid.ext_isCircuit
    · simpa [S, supportCircuitSystem] using hU.1
    · intro X _
      rw [hU.2 X]
      change M.IsSupportCircuit X ↔ S.matroid.IsCircuit X
      rw [FiniteCircuitSystem.matroid_isCircuit]
      rfl

/-- The ordinary matroid canonically determined by the signed circuit supports. -/
noncomputable def underlying [Finite α] : Matroid α :=
  Classical.choose M.existsUnique_underlying

theorem underlying_spec [Finite α] : M.Underlies M.underlying :=
  (Classical.choose_spec M.existsUnique_underlying).1

/-- An unsigned circuit of the underlying matroid admits either signed orientation; this version
chooses the orientation in which a prescribed support element is positive. -/
theorem exists_isCircuit_support_eq_positive
    [Finite α] {X : Set α} (hX : M.underlying.IsCircuit X)
    {x : α} (hx : x ∈ X) :
    ∃ C : SignedSubset α,
      M.IsCircuit C ∧ C.support = X ∧ x ∈ C.positive := by
  obtain ⟨C, hC, hsupport⟩ := (M.underlying_spec.2 X).mp hX
  have hxC : x ∈ C.support := hsupport.symm ▸ hx
  rcases hxC with hxpos | hxneg
  · exact ⟨C, hC, hsupport, hxpos⟩
  · refine ⟨-C, M.neg_isCircuit hC, ?_, ?_⟩
    · simpa using hsupport
    · simpa using hxneg

/-- Circuit-free independence agrees with independence in the underlying ordinary matroid. -/
theorem isIndependent_iff_underlying_indep [Finite α] {X : Set α} :
    M.IsIndependent X ↔ M.underlying.Indep X := by
  have hspec := M.underlying_spec
  constructor
  · intro hX
    rw [Matroid.indep_iff_forall_subset_not_isCircuit (by simp [hspec.1])]
    intro C hCX hC
    obtain ⟨S, hS, rfl⟩ := (hspec.2 C).mp hC
    exact hX hS hCX
  · intro hX C hC hCX
    have hUC : M.underlying.IsCircuit C.support :=
      (hspec.2 C.support).mpr ⟨C, hC, rfl⟩
    exact hUC.not_indep (hX.subset hCX)

/-- The circuit definition of a basis agrees with the underlying ordinary matroid. -/
theorem isBasis_iff_underlying_isBase [Finite α] {B : Set α} :
    M.IsBasis B ↔ M.underlying.IsBase B := by
  rw [IsBasis, Matroid.isBase_iff_maximal_indep]
  rw [maximal_subset_iff, maximal_subset_iff]
  constructor
  · rintro ⟨hB, hmax⟩
    refine ⟨M.isIndependent_iff_underlying_indep.mp hB, ?_⟩
    intro X hX hBX
    exact hmax (M.isIndependent_iff_underlying_indep.mpr hX) hBX
  · rintro ⟨hB, hmax⟩
    refine ⟨M.isIndependent_iff_underlying_indep.mpr hB, ?_⟩
    intro X hX hBX
    exact hmax (M.isIndependent_iff_underlying_indep.mp hX) hBX

/-- A signed fundamental circuit, oriented positively at the element outside the basis. -/
theorem exists_fundCircuit_positive
    [Finite α] {B : Set α} (hB : M.IsBasis B)
    {x : α} (hxB : x ∉ B) :
    ∃ C : SignedSubset α,
      M.IsCircuit C ∧
        C.support = M.underlying.fundCircuit x B ∧ x ∈ C.positive := by
  have hBbase : M.underlying.IsBase B :=
    M.isBasis_iff_underlying_isBase.mp hB
  have hxGround : x ∈ M.underlying.E := by
    rw [M.underlying_spec.1]
    trivial
  have hfund : M.underlying.IsCircuit (M.underlying.fundCircuit x B) :=
    hBbase.fundCircuit_isCircuit hxGround hxB
  exact M.exists_isCircuit_support_eq_positive hfund
    (M.underlying.mem_fundCircuit x B)

/-- A canonical choice of signed fundamental circuit, with the external element positive.
It has the empty signed set as an irrelevant fallback when the element already lies in the basis. -/
noncomputable def signedFundCircuit
    [Finite α] (B : Set α) (hB : M.IsBasis B) (x : α) : SignedSubset α := by
  classical
  exact if hx : x ∉ B then Classical.choose (M.exists_fundCircuit_positive hB hx) else ∅

theorem signedFundCircuit_isCircuit
    [Finite α] {B : Set α} (hB : M.IsBasis B) {x : α} (hx : x ∉ B) :
    M.IsCircuit (M.signedFundCircuit B hB x) := by
  simp only [signedFundCircuit, dif_pos hx]
  exact (Classical.choose_spec (M.exists_fundCircuit_positive hB hx)).1

theorem signedFundCircuit_support
    [Finite α] {B : Set α} (hB : M.IsBasis B) {x : α} (hx : x ∉ B) :
    (M.signedFundCircuit B hB x).support = M.underlying.fundCircuit x B := by
  simp only [signedFundCircuit, dif_pos hx]
  exact (Classical.choose_spec (M.exists_fundCircuit_positive hB hx)).2.1

theorem signedFundCircuit_external_positive
    [Finite α] {B : Set α} (hB : M.IsBasis B) {x : α} (hx : x ∉ B) :
    x ∈ (M.signedFundCircuit B hB x).positive := by
  simp only [signedFundCircuit, dif_pos hx]
  exact (Classical.choose_spec (M.exists_fundCircuit_positive hB hx)).2.2

/-- The signed fundamental cocircuit determined by a basis element.  Its sign at the basis element
is negative; at an external element `x`, its sign is read from the sign of the basis element in the
fundamental circuit oriented positively at `x`. -/
noncomputable def fundamentalCocircuit
    [Finite α] (B : Set α) (hB : M.IsBasis B) (e : α) : SignedSubset α where
  positive := {x | x ∈ M.underlying.fundCocircuit e B ∧ x ≠ e ∧
    e ∈ (M.signedFundCircuit B hB x).positive}
  negative := {e} ∪ {x | x ∈ M.underlying.fundCocircuit e B ∧ x ≠ e ∧
    e ∈ (M.signedFundCircuit B hB x).negative}
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hxe, hepos⟩ (rfl | ⟨_, _, heneg⟩)
    · exact hxe rfl
    · exact Set.disjoint_left.1 (M.signedFundCircuit B hB x).disjoint hepos heneg

theorem fundamentalCocircuit_support
    [Finite α] {B : Set α} (hB : M.IsBasis B) {e : α} (heB : e ∈ B) :
    (M.fundamentalCocircuit B hB e).support = M.underlying.fundCocircuit e B := by
  classical
  let K : Set α := M.underlying.fundCocircuit e B
  have hBbase : M.underlying.IsBase B := M.isBasis_iff_underlying_isBase.mp hB
  have hKinter : K ∩ B = {e} := by
    exact M.underlying.fundCocircuit_inter_eq heB
  have heK : e ∈ K := M.underlying.mem_fundCocircuit e B
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · rcases hx with rfl | hx
      · exact heK
      · exact hx.1
  · intro x hxK
    by_cases hxe : x = e
    · subst x
      exact Or.inr (Or.inl rfl)
    have hxB : x ∉ B := by
      intro hxB
      have hxInter : x ∈ K ∩ B := ⟨hxK, hxB⟩
      have : x = e := by simpa [hKinter] using hxInter
      exact hxe this
    have heFund : e ∈ M.underlying.fundCircuit x B :=
      (hBbase.mem_fundCocircuit_iff_mem_fundCircuit).mp hxK
    have heSigned : e ∈ (M.signedFundCircuit B hB x).support := by
      rw [M.signedFundCircuit_support hB hxB]
      exact heFund
    rcases heSigned with hepos | heneg
    · exact Or.inl ⟨hxK, hxe, hepos⟩
    · exact Or.inr (Or.inr ⟨hxK, hxe, heneg⟩)

@[simp]
theorem fundamentalCocircuit_basis_mem_negative
    [Finite α] {B : Set α} (hB : M.IsBasis B) (e : α) :
    e ∈ (M.fundamentalCocircuit B hB e).negative :=
  Or.inl rfl

set_option maxHeartbeats 800000 in
/-- The explicitly signed fundamental cocircuit is orthogonal to every signed circuit. -/
theorem fundamentalCocircuit_isCovector
    [Fintype α] {B : Set α} (hB : M.IsBasis B) {e : α} (heB : e ∈ B) :
    M.IsCovector (M.fundamentalCocircuit B hB e) := by
  classical
  let D : SignedSubset α := M.fundamentalCocircuit B hB e
  let K : Set α := M.underlying.fundCocircuit e B
  have hDsupport : D.support = K := by
    simpa [D, K] using M.fundamentalCocircuit_support hB heB
  have hBbase : M.underlying.IsBase B := M.isBasis_iff_underlying_isBase.mp hB
  have hKcocircuit : M.underlying.IsCocircuit K := by
    exact M.underlying.fundCocircuit_isCocircuit heB hBbase
  have hKinter : K ∩ B = {e} := M.underlying.fundCocircuit_inter_eq heB
  have heK : e ∈ K := M.underlying.mem_fundCocircuit e B
  have hsingletonDiff (S : Set α) :
      ({e} \ S).ncard = if e ∈ S then 0 else 1 := by
    by_cases heS : e ∈ S
    · have hEq : {e} \ S = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hx.2 (hx.1 ▸ heS)
      rw [hEq]
      simp [heS]
    · have hEq : {e} \ S = {e} := by
        apply Set.Subset.antisymm
        · intro x hx
          exact hx.1
        · rintro x rfl
          exact ⟨rfl, heS⟩
      rw [hEq]
      simp [heS]
  let complexity (C : SignedSubset α) : Nat :=
    2 * (C.support ∩ K).ncard + ({e} \ C.support).ncard
  let rec go (C : SignedSubset α) (hC : M.IsCircuit C)
      (hinter : (C.support ∩ K).Nonempty)
      (hall : ∀ x, x ∈ C.support ∩ K → C.SameSignAt D x) : False := by
    have hCU : M.underlying.IsCircuit C.support :=
      (M.underlying_spec.2 C.support).mpr ⟨C, hC, rfl⟩
    have hnontrivial : (C.support ∩ K).Nontrivial :=
      hCU.isCocircuit_inter_nontrivial hKcocircuit hinter
    obtain ⟨x, hxCK, hxe⟩ := hnontrivial.exists_ne e
    have hxB : x ∉ B := by
      intro hxB
      have hxKB : x ∈ K ∩ B := ⟨hxCK.2, hxB⟩
      have : x = e := by simpa [hKinter] using hxKB
      exact hxe this
    let Fcirc : SignedSubset α := M.signedFundCircuit B hB x
    have hFcirc : M.IsCircuit Fcirc := by
      simpa [Fcirc] using M.signedFundCircuit_isCircuit hB hxB
    have hFsupport : Fcirc.support = M.underlying.fundCircuit x B := by
      simpa [Fcirc] using M.signedFundCircuit_support hB hxB
    have hxFpos : x ∈ Fcirc.positive := by
      simpa [Fcirc] using M.signedFundCircuit_external_positive hB hxB
    have hsameX : C.SameSignAt D x := hall x hxCK
    obtain ⟨G, hG, hGsupport, hopposite, heGneg⟩ :
        ∃ G : SignedSubset α,
          M.IsCircuit G ∧ G.support = M.underlying.fundCircuit x B ∧
            C.OppositeAt G x ∧ e ∈ G.negative := by
      rcases hsameX with hsameX | hsameX
      · have heFpos : e ∈ Fcirc.positive := by
          exact hsameX.2.2.2
        refine ⟨-Fcirc, M.neg_isCircuit hFcirc, by simp [hFsupport], ?_, by simpa⟩
        exact Or.inl ⟨hsameX.1, by simpa using hxFpos⟩
      · have hxDneg : x ∈
            {e} ∪ {y | y ∈ K ∧ y ≠ e ∧
              e ∈ (M.signedFundCircuit B hB y).negative} := by
          exact hsameX.2
        rcases hxDneg with hxe' | hxDneg
        · exact (hxe (by simpa using hxe')).elim
        · have heFneg : e ∈ Fcirc.negative := by simpa [Fcirc] using hxDneg.2.2
          exact ⟨Fcirc, hFcirc, hFsupport, Or.inr ⟨hsameX.1, hxFpos⟩, heFneg⟩
    have hGKsub : G.support ∩ K ⊆ {x, e} := by
      intro y hy
      have hyFund : y ∈ M.underlying.fundCircuit x B := hGsupport ▸ hy.1
      rcases M.underlying.fundCircuit_subset_insert x B hyFund with hyx | hyB
      · exact Set.mem_insert_iff.mpr (Or.inl hyx)
      · have hyKB : y ∈ K ∩ B := ⟨hy.2, hyB⟩
        have hye : y = e := by simpa [hKinter] using hyKB
        exact Set.mem_insert_iff.mpr (Or.inr (by simp [hye]))
    by_cases heC : e ∈ C.support
    · have heCK : e ∈ C.support ∩ K := ⟨heC, heK⟩
      have hsameE : C.SameSignAt D e := hall e heCK
      have heCneg : e ∈ C.negative := by
        rcases hsameE with hsameE | hsameE
        · exact (Set.disjoint_left.1 D.disjoint hsameE.2
            (M.fundamentalCocircuit_basis_mem_negative hB e)).elim
        · exact hsameE.1
      have hsurvives : SurvivesFrom C G e :=
        Or.inr ⟨heCneg, fun heGpos ↦ Set.disjoint_left.1 G.disjoint heGpos heGneg⟩
      obtain ⟨Z, hZ, hZelim, heZ⟩ := M.strongElimination hC hG hopposite hsurvives
      have hxNotZ : x ∉ Z.support := by
        intro hxZ
        exact (hZelim.support_subset hxZ).2 (by simp)
      have hinterZ : (Z.support ∩ K).Nonempty := ⟨e, heZ, heK⟩
      have hallZ : ∀ z, z ∈ Z.support ∩ K → Z.SameSignAt D z := by
        intro z hz
        rcases hz.1 with hzpos | hzneg
        · have hzElim := hZelim.1 hzpos
          rcases hzElim.1 with hzCpos | hzGpos
          · rcases hall z ⟨Or.inl hzCpos, hz.2⟩ with hsame | hsame
            · exact Or.inl ⟨hzpos, hsame.2⟩
            · exact (Set.disjoint_left.1 C.disjoint hzCpos hsame.1).elim
          · rcases hGKsub ⟨Or.inl hzGpos, hz.2⟩ with rfl | hze
            · exact (hzElim.2 (by simp)).elim
            · have : z = e := by simpa using hze
              subst z
              exact (Set.disjoint_left.1 G.disjoint hzGpos heGneg).elim
        · have hzElim := hZelim.2 hzneg
          rcases hzElim.1 with hzCneg | hzGneg
          · rcases hall z ⟨Or.inr hzCneg, hz.2⟩ with hsame | hsame
            · exact (Set.disjoint_left.1 C.disjoint hsame.1 hzCneg).elim
            · exact Or.inr ⟨hzneg, hsame.2⟩
          · rcases hGKsub ⟨Or.inr hzGneg, hz.2⟩ with rfl | hze
            · exact (hzElim.2 (by simp)).elim
            · have : z = e := by simpa using hze
              subst z
              exact Or.inr ⟨hzneg, M.fundamentalCocircuit_basis_mem_negative hB e⟩
      have hZKsub : Z.support ∩ K ⊆ (C.support ∩ K) \ {x} := by
        intro z hz
        have hzSub := hZelim.support_subset hz.1
        refine ⟨?_, hzSub.2⟩
        rcases hzSub.1 with hzC | hzG
        · exact ⟨hzC, hz.2⟩
        · rcases hGKsub ⟨hzG, hz.2⟩ with hzx | hze
          · exact (hzSub.2 (by simpa using hzx)).elim
          · have hze' : z = e := by simpa using hze
            subst z
            exact heCK
      have hcardlt : (Z.support ∩ K).ncard < (C.support ∩ K).ncard := by
        have hsub : Z.support ∩ K ⊆ C.support ∩ K := hZKsub.trans Set.sdiff_subset
        exact Set.ncard_lt_ncard
          (hsub.ssubset_of_mem_notMem hxCK (fun hx ↦ hxNotZ hx.1))
      have hmeasure : complexity Z < complexity C := by
        simp only [complexity]
        rw [hsingletonDiff Z.support, hsingletonDiff C.support]
        by_cases heZ' : e ∈ Z.support <;> simp [heC, heZ'] <;> omega
      exact go Z hZ hinterZ hallZ
    · obtain ⟨v, hvCK, hvx⟩ := hnontrivial.exists_ne x
      have hve : v ≠ e := fun hve ↦ heC (hve ▸ hvCK.1)
      have hvNotG : v ∉ G.support := by
        intro hvG
        rcases hGKsub ⟨hvG, hvCK.2⟩ with hvx' | hve'
        · exact hvx (by simpa using hvx')
        · exact hve (by simpa using hve')
      have hsurvives : SurvivesFrom C G v := by
        rcases hvCK.1 with hvpos | hvneg
        · exact Or.inl ⟨hvpos, fun h ↦ hvNotG (Or.inr h)⟩
        · exact Or.inr ⟨hvneg, fun h ↦ hvNotG (Or.inl h)⟩
      obtain ⟨Z, hZ, hZelim, hvZ⟩ := M.strongElimination hC hG hopposite hsurvives
      have hxNotZ : x ∉ Z.support := by
        intro hxZ
        exact (hZelim.support_subset hxZ).2 (by simp)
      have hinterZ : (Z.support ∩ K).Nonempty := ⟨v, hvZ, hvCK.2⟩
      have hallZ : ∀ z, z ∈ Z.support ∩ K → Z.SameSignAt D z := by
        intro z hz
        rcases hz.1 with hzpos | hzneg
        · have hzElim := hZelim.1 hzpos
          rcases hzElim.1 with hzCpos | hzGpos
          · rcases hall z ⟨Or.inl hzCpos, hz.2⟩ with hsame | hsame
            · exact Or.inl ⟨hzpos, hsame.2⟩
            · exact (Set.disjoint_left.1 C.disjoint hzCpos hsame.1).elim
          · rcases hGKsub ⟨Or.inl hzGpos, hz.2⟩ with rfl | hze
            · exact (hzElim.2 (by simp)).elim
            · have : z = e := by simpa using hze
              subst z
              exact (Set.disjoint_left.1 G.disjoint hzGpos heGneg).elim
        · have hzElim := hZelim.2 hzneg
          rcases hzElim.1 with hzCneg | hzGneg
          · rcases hall z ⟨Or.inr hzCneg, hz.2⟩ with hsame | hsame
            · exact (Set.disjoint_left.1 C.disjoint hsame.1 hzCneg).elim
            · exact Or.inr ⟨hzneg, hsame.2⟩
          · rcases hGKsub ⟨Or.inr hzGneg, hz.2⟩ with rfl | hze
            · exact (hzElim.2 (by simp)).elim
            · have : z = e := by simpa using hze
              subst z
              exact Or.inr ⟨hzneg, M.fundamentalCocircuit_basis_mem_negative hB e⟩
      have hZKsub : Z.support ∩ K ⊆ ((C.support ∩ K) \ {x}) ∪ {e} := by
        intro z hz
        have hzSub := hZelim.support_subset hz.1
        rcases hzSub.1 with hzC | hzG
        · exact Or.inl ⟨⟨hzC, hz.2⟩, hzSub.2⟩
        · rcases hGKsub ⟨hzG, hz.2⟩ with hzx | hze
          · exact (hzSub.2 (by simpa using hzx)).elim
          · exact Or.inr (by simpa using hze)
      by_cases heZ : e ∈ Z.support
      · have hcardle : (Z.support ∩ K).ncard ≤ (C.support ∩ K).ncard := by
          calc
            (Z.support ∩ K).ncard ≤
                (((C.support ∩ K) \ {x}) ∪ {e}).ncard :=
              Set.ncard_le_ncard hZKsub (Set.toFinite _)
            _ = (C.support ∩ K).ncard := by
              rw [Set.union_singleton, Set.ncard_insert_of_notMem,
                Set.ncard_sdiff_singleton_add_one hxCK]
              intro heSdiff
              exact heC heSdiff.1.1
        have hmeasure : complexity Z < complexity C := by
          simp only [complexity]
          rw [hsingletonDiff Z.support, hsingletonDiff C.support]
          simp [heC, heZ]
          omega
        exact go Z hZ hinterZ hallZ
      · have hZKsub' : Z.support ∩ K ⊆ (C.support ∩ K) \ {x} := by
          intro z hz
          rcases hZKsub hz with hz | hze
          · exact hz
          · have : z = e := by simpa using hze
            subst z
            exact (heZ hz.1).elim
        have hcardlt : (Z.support ∩ K).ncard < (C.support ∩ K).ncard := by
          have hsub : Z.support ∩ K ⊆ C.support ∩ K := hZKsub'.trans Set.sdiff_subset
          exact Set.ncard_lt_ncard
            (hsub.ssubset_of_mem_notMem hxCK (fun hx ↦ hxNotZ hx.1))
        have hmeasure : complexity Z < complexity C := by
          simp only [complexity]
          rw [hsingletonDiff Z.support, hsingletonDiff C.support]
          simp [heC, heZ]
          omega
        exact go Z hZ hinterZ hallZ
  termination_by
    2 * (C.support ∩ M.underlying.fundCocircuit e B).ncard +
      ({e} \ C.support).ncard
  decreasing_by
    all_goals
      rw [hsingletonDiff Z.support, hsingletonDiff C.support]
      simp [heC, heZ]
      omega
  intro C hC
  by_contra horthogonal
  have hinter : (C.support ∩ D.support).Nonempty := by
    by_contra hempty
    apply horthogonal
    exact Or.inl (Set.disjoint_iff_inter_eq_empty.mpr
      (Set.not_nonempty_iff_eq_empty.mp hempty))
  rcases SignedSubset.uniform_of_not_orthogonal horthogonal hinter with hall | hall
  · apply go C hC
    · simpa [hDsupport] using hinter
    · intro x hx
      apply hall x
      exact ⟨hx.1, hDsupport.symm ▸ hx.2⟩
  · apply go (-C) (M.neg_isCircuit hC)
    · simpa [hDsupport] using hinter
    · intro x hx
      rw [SignedSubset.neg_sameSignAt_iff_oppositeAt]
      apply hall x
      exact ⟨by simpa using hx.1, hDsupport.symm ▸ hx.2⟩

/-- The support of a nonzero covector meets every basis. -/
theorem IsCovector.support_inter_isBasis_nonempty
    [Finite α] {D : SignedSubset α} (hD : M.IsCovector D)
    (hDnonempty : D.support.Nonempty) {B : Set α} (hB : M.IsBasis B) :
    (D.support ∩ B).Nonempty := by
  by_contra hinter
  have hdisjoint : Disjoint D.support B := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp hinter
  obtain ⟨x, hxD⟩ := hDnonempty
  have hxB : x ∉ B := fun hx ↦ Set.disjoint_left.1 hdisjoint hxD hx
  obtain ⟨C, hC, hCsupport, hxCpos⟩ := M.exists_fundCircuit_positive hB hxB
  have hfundSub : M.underlying.fundCircuit x B ⊆ insert x B :=
    M.underlying.fundCircuit_subset_insert x B
  have hsupportInter : C.support ∩ D.support = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyFund : y ∈ M.underlying.fundCircuit x B := hCsupport ▸ hy.1
      rcases hfundSub hyFund with hyx | hyB
      · simp [hyx]
      · exact (Set.disjoint_left.1 hdisjoint hy.2 hyB).elim
    · exact Set.singleton_subset_iff.mpr ⟨Or.inl hxCpos, hxD⟩
  exact SignedSubset.not_orthogonal_of_support_inter_eq_singleton hsupportInter
    (hD hC)

/-- The explicitly signed fundamental cocircuit is support-minimal among nonzero covectors. -/
theorem fundamentalCocircuit_isCocircuit
    [Fintype α] {B : Set α} (hB : M.IsBasis B) {e : α} (heB : e ∈ B) :
    M.IsCocircuit (M.fundamentalCocircuit B hB e) := by
  let D : SignedSubset α := M.fundamentalCocircuit B hB e
  let K : Set α := M.underlying.fundCocircuit e B
  have hsupport : D.support = K := by
    simpa [D, K] using M.fundamentalCocircuit_support hB heB
  have hBbase : M.underlying.IsBase B := M.isBasis_iff_underlying_isBase.mp hB
  have hKcocircuit : M.underlying.IsCocircuit K :=
    M.underlying.fundCocircuit_isCocircuit heB hBbase
  have hKminimal := Matroid.isCocircuit_iff_minimal.mp hKcocircuit
  refine ⟨?_, M.fundamentalCocircuit_isCovector hB heB, ?_⟩
  · rw [hsupport]
    exact hKcocircuit.nonempty
  · intro E hEnonempty hEcovector hEsub
    have hEhits : ∀ B' : Set α, M.underlying.IsBase B' →
        (E.support ∩ B').Nonempty := by
      intro B' hB'
      exact IsCovector.support_inter_isBasis_nonempty M hEcovector hEnonempty
        (M.isBasis_iff_underlying_isBase.mpr hB')
    have hKsubE : K ⊆ E.support := by
      apply hKminimal.2 hEhits
      change E.support ⊆ D.support at hEsub
      rwa [hsupport] at hEsub
    change D.support ⊆ E.support
    rwa [hsupport]

/-- Every element of an independent set has a signed cocircuit meeting that set only there. -/
theorem IsIndependent.exists_isCocircuit_support_inter_eq_singleton
    [Fintype α] {I : Set α} (hI : M.IsIndependent I) {e : α} (heI : e ∈ I) :
    ∃ D : SignedSubset α, M.IsCocircuit D ∧ D.support ∩ I = {e} := by
  have hIU : M.underlying.Indep I := M.isIndependent_iff_underlying_indep.mp hI
  obtain ⟨B, hBbase, hIB⟩ := hIU.exists_isBase_superset
  have hB : M.IsBasis B := M.isBasis_iff_underlying_isBase.mpr hBbase
  let D : SignedSubset α := M.fundamentalCocircuit B hB e
  have heB : e ∈ B := hIB heI
  refine ⟨D, M.fundamentalCocircuit_isCocircuit hB heB, ?_⟩
  have hsupport : D.support = M.underlying.fundCocircuit e B := by
    simpa [D] using M.fundamentalCocircuit_support hB heB
  have hKB : M.underlying.fundCocircuit e B ∩ B = {e} :=
    M.underlying.fundCocircuit_inter_eq heB
  apply Set.Subset.antisymm
  · intro x hx
    have hxKB : x ∈ M.underlying.fundCocircuit e B ∩ B :=
      ⟨hsupport ▸ hx.1, hIB hx.2⟩
    simpa [hKB] using hxKB
  · exact Set.singleton_subset_iff.mpr ⟨hsupport.symm ▸
      M.underlying.mem_fundCocircuit e B, heI⟩

/-- Restrict an oriented matroid along an embedding of a subset of its ground type. -/
noncomputable def restrict {β : Type*} (f : β ↪ α) : Data β where
  circuits := {C | M.IsCircuit (C.map f)}
  support_nonempty := by
    intro C hC
    have hmap := M.circuit_support_nonempty hC
    simpa using hmap
  neg_mem := by
    intro C hC
    simpa using M.neg_isCircuit hC
  eq_or_eq_neg_of_support_subset := by
    intro C D hC hD hsub
    have hsub' : (C.map f).support ⊆ (D.map f).support := by
      simpa using Set.image_mono hsub
    rcases M.eq_or_eq_neg_of_support_subset hC hD hsub' with h | h
    · exact Or.inl (SignedSubset.map_injective f h)
    · exact Or.inr (SignedSubset.map_injective f (by simpa using h))
  weakElimination := by
    intro C D hC hD hne u hu
    have hne' : C.map f ≠ -(D.map f) := by
      intro h
      apply hne
      exact SignedSubset.map_injective f (by simpa using h)
    have hu' : (C.map f).OppositeAt (D.map f) (f u) := by
      rcases hu with hu | hu
      · exact Or.inl ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩
      · exact Or.inr ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩
    obtain ⟨Z, hZ, hZE⟩ := M.weakElimination hC hD hne' hu'
    have hZrange : Z.support ⊆ Set.range f := by
      intro y hy
      rcases hy with hy | hy
      · rcases (hZE.1 hy).1 with hy | hy
        · obtain ⟨x, _, rfl⟩ := hy
          exact ⟨x, rfl⟩
        · obtain ⟨x, _, rfl⟩ := hy
          exact ⟨x, rfl⟩
      · rcases (hZE.2 hy).1 with hy | hy
        · obtain ⟨x, _, rfl⟩ := hy
          exact ⟨x, rfl⟩
        · obtain ⟨x, _, rfl⟩ := hy
          exact ⟨x, rfl⟩
    refine ⟨Z.comap f, ?_, ?_⟩
    · change M.IsCircuit ((Z.comap f).map f)
      simpa [SignedSubset.map_comap_of_support_subset_range f Z hZrange] using hZ
    · constructor
      · intro x hx
        simpa using hZE.1 hx
      · intro x hx
        simpa using hZE.2 hx
theorem restrict_isIndependent_iff {β : Type*} (f : β ↪ α) (X : Set β) :
    (M.restrict f).IsIndependent X ↔ M.IsIndependent (f '' X) := by
  constructor
  · intro hX C hC hCsub
    have hCrange : C.support ⊆ Set.range f :=
      hCsub.trans (Set.image_subset_range f X)
    let C' : SignedSubset β := C.comap f
    have hrecover : C'.map f = C :=
      SignedSubset.map_comap_of_support_subset_range f C hCrange
    have hC' : (M.restrict f).IsCircuit C' := by
      change M.IsCircuit (C'.map f)
      simpa [hrecover] using hC
    apply hX hC'
    intro x hx
    have hfx : f x ∈ C.support := by
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr hx
    obtain ⟨y, hyX, hy⟩ := hCsub hfx
    exact f.injective hy ▸ hyX
  · intro hX C hC hCsub
    change M.IsCircuit (C.map f) at hC
    apply hX hC
    rw [SignedSubset.support_map]
    exact Set.image_mono hCsub

/-- A basis of the ambient oriented matroid contained in an embedding range remains a basis after
restriction to the embedding domain. -/
theorem restrict_isBasis_of_isBasis_image {β : Type*} (f : β ↪ α) (B : Set β)
    (hB : M.IsBasis (f '' B)) :
    (M.restrict f).IsBasis B := by
  constructor
  · exact (M.restrict_isIndependent_iff f B).mpr hB.1
  · intro X hX hBX
    have hXimage : M.IsIndependent (f '' X) :=
      (M.restrict_isIndependent_iff f X).mp hX
    have hImageSub : f '' B ⊆ f '' X := Set.image_mono hBX
    have hBack : f '' X ⊆ f '' B := hB.2 hXimage hImageSub
    intro x hx
    obtain ⟨y, hyB, hy⟩ := hBack ⟨x, hx, rfl⟩
    exact f.injective hy ▸ hyB

/-- Deletion of one element, represented on the subtype of the remaining elements. -/
noncomputable def delete (e : α) : Data {x : α // x ≠ e} :=
  M.restrict (Function.Embedding.subtype _)

end Data

end OrientedMatroid

end BeyondSperner
