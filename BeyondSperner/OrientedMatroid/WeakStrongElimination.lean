import BeyondSperner.OrientedMatroid.Core
import Mathlib.Data.Set.Card

/-!
# Strong circuit elimination from the weak circuit axioms

This module proves the Bland--Las Vergnas / Folkman--Lawrence
weak-to-strong theorem from a genuinely weak signed-circuit interface.

The proof follows the contraction induction used in the standard proof.  The
first layer below establishes that nonzero restrictions of weak circuits after
erasing one coordinate are closed under the weak elimination operation.  The
support-minimal members of this family will be the circuits of the contraction.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid

variable {α : Type*}

/-- The signed-circuit axioms in Ivanov's definition, with weak elimination
as the only elimination field. -/
structure WeakData (α : Type*) where
  circuits : Set (SignedSubset α)
  support_nonempty : ∀ {C}, C ∈ circuits → C.support.Nonempty
  neg_mem : ∀ {C}, C ∈ circuits → -C ∈ circuits
  eq_or_eq_neg_of_support_subset : ∀ {C D}, C ∈ circuits → D ∈ circuits →
    C.support ⊆ D.support → C = D ∨ C = -D
  weakElimination : ∀ {C D}, C ∈ circuits → D ∈ circuits → C ≠ -D →
    ∀ {u}, C.OppositeAt D u →
      ∃ Z : SignedSubset α, Z ∈ circuits ∧ EliminatesAt Z C D u

@[ext]
theorem WeakData.ext_circuits {M N : WeakData α}
    (h : M.circuits = N.circuits) : M = N := by
  cases M
  cases N
  simp_all

namespace WeakData

variable (M : WeakData α)

/-- Membership in the weak signed-circuit family. -/
abbrev IsCircuit (C : SignedSubset α) : Prop := C ∈ M.circuits

theorem neg_isCircuit {C : SignedSubset α} (hC : M.IsCircuit C) :
    M.IsCircuit (-C) :=
  M.neg_mem hC

theorem circuit_support_nonempty {C : SignedSubset α} (hC : M.IsCircuit C) :
    C.support.Nonempty :=
  M.support_nonempty hC

theorem empty_not_isCircuit : ¬ M.IsCircuit (∅ : SignedSubset α) := by
  intro h
  simpa using M.circuit_support_nonempty h

/-- Copy the public weak `Data` interface into the proof-local `WeakData`
interface.  Keeping the proof-local type separate makes it impossible for
this development to acquire future high-level fields by accident. -/
def ofData (N : Data α) : WeakData α where
  circuits := N.circuits
  support_nonempty := N.support_nonempty
  neg_mem := N.neg_mem
  eq_or_eq_neg_of_support_subset := N.eq_or_eq_neg_of_support_subset
  weakElimination := N.weakElimination

@[simp]
theorem ofData_circuits (N : Data α) : (ofData N).circuits = N.circuits := rfl

/-- A nonzero sign vector obtained by erasing `p` from an original circuit.
These are the (not necessarily support-minimal) circuit candidates for a
contraction. -/
def IsErasedCircuit (p : α) (X : SignedSubset α) : Prop :=
  X.support.Nonempty ∧
    ∃ C : SignedSubset α, M.IsCircuit C ∧ X = C.erase p

theorem IsErasedCircuit.support_nonempty {p : α} {X : SignedSubset α}
    (hX : M.IsErasedCircuit p X) : X.support.Nonempty :=
  hX.1

theorem IsErasedCircuit.neg {p : α} {X : SignedSubset α}
    (hX : M.IsErasedCircuit p X) : M.IsErasedCircuit p (-X) := by
  rcases hX with ⟨hXnonempty, C, hC, rfl⟩
  refine ⟨by simpa using hXnonempty, -C, M.neg_isCircuit hC, ?_⟩
  simp

/-- Every erased-circuit candidate omits the erased coordinate. -/
theorem IsErasedCircuit.not_mem_support {p : α} {X : SignedSubset α}
    (hX : M.IsErasedCircuit p X) : p ∉ X.support := by
  rcases hX.2 with ⟨C, _, rfl⟩
  simp

/-- If an original circuit uses `p` and at least one other coordinate, its
erasure is a nonzero contraction candidate. -/
theorem isErasedCircuit_erase {p : α} {C : SignedSubset α}
    (hC : M.IsCircuit C) (hCrest : (C.support \ {p}).Nonempty) :
    M.IsErasedCircuit p (C.erase p) := by
  exact ⟨by simpa using hCrest, C, hC, rfl⟩

/-- The witnesses of two distinct erased candidates cannot be opposite
original circuits. -/
private theorem witness_ne_neg_of_erases_ne_neg
    {p : α} {C D X Y : SignedSubset α}
    (hX : X = C.erase p) (hY : Y = D.erase p) (hne : X ≠ -Y) :
    C ≠ -D := by
  intro hCD
  apply hne
  rw [hX, hY, hCD]
  simp

/-- Weak elimination descends to the family of nonzero erased circuits.  The
only delicate point is that the new erasure cannot be zero: otherwise the
original eliminating circuit would have support contained in one input
circuit, contradicting circuit incomparability because the eliminated
coordinate remains in that input. -/
theorem IsErasedCircuit.weakElimination
    {p : α} {X Y : SignedSubset α}
    (hX : M.IsErasedCircuit p X) (hY : M.IsErasedCircuit p Y)
    (hne : X ≠ -Y) {u : α} (hu : X.OppositeAt Y u) :
    ∃ Z : SignedSubset α,
      M.IsErasedCircuit p Z ∧ EliminatesAt Z X Y u := by
  rcases hX with ⟨hXnonempty, C, hC, rfl⟩
  rcases hY with ⟨hYnonempty, D, hD, rfl⟩
  have hup : u ≠ p := by
    intro hup
    subst u
    exact (by simpa using hu.mem_support_left)
  have huCD : C.OppositeAt D u := by
    rcases hu with hu | hu
    · exact Or.inl ⟨hu.1.1, hu.2.1⟩
    · exact Or.inr ⟨hu.1.1, hu.2.1⟩
  have hCDne : C ≠ -D :=
    witness_ne_neg_of_erases_ne_neg rfl rfl hne
  obtain ⟨W, hW, hWelim⟩ := M.weakElimination hC hD hCDne huCD
  have hWrest : (W.support \ {p}).Nonempty := by
    by_contra hnot
    have hWsubP : W.support ⊆ {p} := by
      intro x hxW
      by_contra hxp
      exact hnot ⟨x, hxW, by simpa using hxp⟩
    have hpInOne : p ∈ C.support ∨ p ∈ D.support := by
      by_contra hpnone
      push Not at hpnone
      obtain ⟨w, hwW⟩ := M.circuit_support_nonempty hW
      have hwp : w = p := by simpa using hWsubP hwW
      subst w
      rcases hwW with hwW | hwW
      · rcases (hWelim.1 hwW).1 with hpC | hpD
        · exact hpnone.1 (Or.inl hpC)
        · exact hpnone.2 (Or.inl hpD)
      · rcases (hWelim.2 hwW).1 with hpC | hpD
        · exact hpnone.1 (Or.inr hpC)
        · exact hpnone.2 (Or.inr hpD)
    rcases hpInOne with hpC | hpD
    · have hWsubC : W.support ⊆ C.support :=
        hWsubP.trans (Set.singleton_subset_iff.mpr hpC)
      rcases M.eq_or_eq_neg_of_support_subset hW hC hWsubC with hEq | hEq
      · have huW : u ∈ W.support := hEq ▸ huCD.mem_support_left
        have hupW := hWsubP huW
        exact hup (by simpa using hupW)
      · have huW : u ∈ W.support := by
          rw [hEq, SignedSubset.support_neg]
          exact huCD.mem_support_left
        have hupW := hWsubP huW
        exact hup (by simpa using hupW)
    · have hWsubD : W.support ⊆ D.support :=
        hWsubP.trans (Set.singleton_subset_iff.mpr hpD)
      rcases M.eq_or_eq_neg_of_support_subset hW hD hWsubD with hEq | hEq
      · have huW : u ∈ W.support := hEq ▸ huCD.mem_support_right
        have hupW := hWsubP huW
        exact hup (by simpa using hupW)
      · have huW : u ∈ W.support := by
          rw [hEq, SignedSubset.support_neg]
          exact huCD.mem_support_right
        have hupW := hWsubP huW
        exact hup (by simpa using hupW)
  let Z := W.erase p
  refine ⟨Z, M.isErasedCircuit_erase hW hWrest, ?_⟩
  constructor
  · intro x hxZ
    have hxp : x ≠ p := by
      exact fun h ↦ hxZ.2 (by simp [h])
    have hxW : x ∈ W.positive := hxZ.1
    have hx := hWelim.1 hxW
    refine ⟨?_, hx.2⟩
    rcases hx.1 with hxC | hxD
    · exact Or.inl ⟨hxC, by simpa using hxp⟩
    · exact Or.inr ⟨hxD, by simpa using hxp⟩
  · intro x hxZ
    have hxp : x ≠ p := by
      exact fun h ↦ hxZ.2 (by simp [h])
    have hxW : x ∈ W.negative := hxZ.1
    have hx := hWelim.2 hxW
    refine ⟨?_, hx.2⟩
    rcases hx.1 with hxC | hxD
    · exact Or.inl ⟨hxC, by simpa using hxp⟩
    · exact Or.inr ⟨hxD, by simpa using hxp⟩

/-- Support-minimal nonzero erasures are the signed circuits of the
contraction by `p`.  Minimality is deliberately phrased only in terms of
support; the proof below shows that weak elimination forces the expected
sign-minimality as well. -/
def IsContractionCircuit (p : α) (X : SignedSubset α) : Prop :=
  M.IsErasedCircuit p X ∧
    ∀ ⦃Y : SignedSubset α⦄, M.IsErasedCircuit p Y →
      Y.support ⊆ X.support → X.support ⊆ Y.support

/-- With nested supports and no sign separation, signed inclusion follows. -/
private theorem le_of_support_subset_of_separation_eq_empty
    {X Y : SignedSubset α} (hsub : X.support ⊆ Y.support)
    (hsep : X.separation Y = ∅) : X ≤ Y := by
  constructor
  · intro x hxX
    rcases hsub (Or.inl hxX) with hxY | hxY
    · exact hxY
    · have : x ∈ X.separation Y := Or.inl ⟨hxX, hxY⟩
      rw [hsep] at this
      exact this.elim
  · intro x hxX
    rcases hsub (Or.inr hxX) with hxY | hxY
    · have : x ∈ X.separation Y := Or.inr ⟨hxX, hxY⟩
      rw [hsep] at this
      exact this.elim
    · exact hxY

/-- If the first input support is contained in the second, weak elimination
strictly reduces the separation from the second input. -/
private theorem separation_subset_of_eliminates_of_support_subset
    {X Y Z : SignedSubset α} {u : α}
    (hZ : EliminatesAt Z X Y u) :
    Y.separation Z ⊆ Y.separation X \ {u} := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rcases hx with hx | hx
    · rcases (hZ.2 hx.2).1 with hxX | hxYneg
      · exact Or.inl ⟨hx.1, hxX⟩
      · exact (Set.disjoint_left.1 Y.disjoint hx.1 hxYneg).elim
    · rcases (hZ.1 hx.2).1 with hxX | hxYpos
      · exact Or.inr ⟨hx.1, hxX⟩
      · exact (Set.disjoint_left.1 Y.disjoint hxYpos hx.1).elim
  · rcases hx with hx | hx
    · exact (hZ.2 hx.2).2
    · exact (hZ.1 hx.2).2

/-- Under the same nesting hypothesis, the support of an elimination is
contained in the larger support with the eliminated point removed. -/
private theorem support_subset_sdiff_of_eliminates_of_support_subset
    {X Y Z : SignedSubset α} {u : α}
    (hXY : X.support ⊆ Y.support) (hZ : EliminatesAt Z X Y u) :
    Z.support ⊆ Y.support \ {u} := by
  have h := hZ.support_subset
  simpa [Set.union_eq_right.mpr hXY] using h

/-- Every nonzero erased circuit contains a conformal support-minimal erased
circuit.  This is Proposition 2.10(1) specialized to the erasure family.

The outer minimization chooses a conformal candidate of smallest support.  If
its support were not globally minimal, an inner minimization on separation,
followed by weak elimination, would produce a smaller separation. -/
theorem exists_isContractionCircuit_le
    [Fintype α] {p : α} {X : SignedSubset α}
    (hX : M.IsErasedCircuit p X) :
    ∃ Y : SignedSubset α, M.IsContractionCircuit p Y ∧ Y ≤ X := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ Y : SignedSubset α,
      M.IsErasedCircuit p Y ∧ Y ≤ X ∧ Y.support.ncard = n
  have hP : ∃ n, P n := by
    exact ⟨X.support.ncard, X, hX, le_rfl, rfl⟩
  let n := Nat.find hP
  obtain ⟨Y, hYerase, hYX, hYcard⟩ := Nat.find_spec hP
  refine ⟨Y, ⟨hYerase, ?_⟩, hYX⟩
  intro Z hZerase hZY
  by_contra hnotYZ
  have hZYstrict : Z.support ⊂ Y.support :=
    hZY.ssubset_of_ne (fun h ↦ hnotYZ h.symm.subset)
  let Q : ℕ → Prop := fun k ↦
    ∃ W : SignedSubset α,
      M.IsErasedCircuit p W ∧ W.support ⊂ Y.support ∧
        (Y.separation W).ncard = k
  have hQ : ∃ k, Q k :=
    ⟨(Y.separation Z).ncard, Z, hZerase, hZYstrict, rfl⟩
  let k := Nat.find hQ
  obtain ⟨W, hWerase, hWY, hsepCard⟩ := Nat.find_spec hQ
  by_cases hsepEmpty : Y.separation W = ∅
  · have hWYle : W ≤ Y :=
      le_of_support_subset_of_separation_eq_empty hWY.subset
        (by simpa [SignedSubset.separation_comm] using hsepEmpty)
    have hWX : W ≤ X := hWYle.trans hYX
    have hWcardLt : W.support.ncard < Y.support.ncard :=
      Set.ncard_lt_ncard hWY
    have hPsmall : P W.support.ncard :=
      ⟨W, hWerase, hWX, rfl⟩
    have hnle : n ≤ W.support.ncard := Nat.find_min' hP hPsmall
    have hnY : n = Y.support.ncard := by simpa [n] using hYcard.symm
    omega
  · obtain ⟨u, huSep⟩ : (Y.separation W).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hsepEmpty
    have huWY : W.OppositeAt Y u := by
      exact SignedSubset.oppositeAt_comm.mp huSep
    have hWneNegY : W ≠ -Y := by
      intro hEq
      have hsupp : W.support = Y.support := by
        rw [hEq, SignedSubset.support_neg]
      exact hWY.ne hsupp
    obtain ⟨T, hTerase, hTelim⟩ :=
      hWerase.weakElimination M hYerase hWneNegY huWY
    have hTYdiff : T.support ⊆ Y.support \ {u} :=
      support_subset_sdiff_of_eliminates_of_support_subset
        hWY.subset hTelim
    have hTY : T.support ⊆ Y.support := hTYdiff.trans Set.sdiff_subset
    have huY : u ∈ Y.support :=
      SignedSubset.OppositeAt.mem_support_left huSep
    have huT : u ∉ T.support := by
      intro hu
      exact (hTYdiff hu).2 rfl
    have hTYstrict : T.support ⊂ Y.support :=
      hTY.ssubset_of_mem_notMem huY huT
    have hsepSub : Y.separation T ⊆ Y.separation W \ {u} := by
      exact separation_subset_of_eliminates_of_support_subset
        hTelim
    have hsepStrict : Y.separation T ⊂ Y.separation W :=
      (hsepSub.trans Set.sdiff_subset).ssubset_of_mem_notMem huSep
        (fun hu ↦ (hsepSub hu).2 rfl)
    have hsepLt : (Y.separation T).ncard < (Y.separation W).ncard :=
      Set.ncard_lt_ncard hsepStrict
    have hQsmall : Q (Y.separation T).ncard :=
      ⟨T, hTerase, hTYstrict, rfl⟩
    have hkle : k ≤ (Y.separation T).ncard := Nat.find_min' hQ hQsmall
    have hkW : k = (Y.separation W).ncard := by
      simpa [k] using hsepCard.symm
    omega

/-- Contraction circuits are closed under global sign reversal. -/
theorem IsContractionCircuit.neg
    {p : α} {X : SignedSubset α} (hX : M.IsContractionCircuit p X) :
    M.IsContractionCircuit p (-X) := by
  refine ⟨hX.1.neg M, ?_⟩
  intro Y hY hsub
  have hsub' : Y.support ⊆ X.support := by simpa using hsub
  have hXsub := hX.2 hY hsub'
  simpa using hXsub

/-- On one contraction support, a single same sign forces equality. -/
private theorem eq_of_isContractionCircuit_of_support_eq_of_sameSignAt
    [Fintype α] {p : α} {X Y : SignedSubset α}
    (hX : M.IsContractionCircuit p X)
    (hY : M.IsContractionCircuit p Y)
    (hsupport : X.support = Y.support) {e : α}
    (heX : e ∈ X.support) (hsame : X.SameSignAt Y e) : X = Y := by
  by_contra hne
  have hopposite : ∃ u ∈ X.support, X.OppositeAt Y u := by
    by_contra hnone
    push Not at hnone
    apply hne
    apply SignedSubset.eq_of_support_eq_of_forall_sameSignAt hsupport
    intro u huX
    rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem
        ⟨huX, hsupport ▸ huX⟩ with huSame | huOpp
    · exact huSame
    · exact (hnone u huX huOpp).elim
  obtain ⟨u, huX, huOpp⟩ := hopposite
  have heSurvives : SurvivesFrom X Y e := by
    rcases hsame with hsame | hsame
    · exact Or.inl ⟨hsame.1, fun heYneg ↦
        Set.disjoint_left.1 Y.disjoint hsame.2 heYneg⟩
    · exact Or.inr ⟨hsame.1, fun heYpos ↦
        Set.disjoint_left.1 Y.disjoint heYpos hsame.2⟩
  have hXneNegY : X ≠ -Y := by
    intro hEq
    have hOppSelf : X.OppositeAt Y e := by
      rw [hEq]
      exact SignedSubset.oppositeAt_comm.mp
        (SignedSubset.oppositeAt_neg_self (hsupport ▸ heX))
    exact hsame.not_oppositeAt hOppSelf
  obtain ⟨Z₀, hZ₀erase, hZ₀elim⟩ :=
    hX.1.weakElimination M hY.1 hXneNegY huOpp
  obtain ⟨Z, hZmin, hZZ₀⟩ :=
    M.exists_isContractionCircuit_le hZ₀erase
  have hZsubDiff : Z.support ⊆ X.support \ {u} := by
    have hZsubZ₀ := SignedSubset.support_mono hZZ₀
    have hZ₀sub := support_subset_sdiff_of_eliminates_of_support_subset
      (X := X) (Y := Y) hsupport.subset hZ₀elim
    have hZ₀subX : Z₀.support ⊆ X.support \ {u} := by
      rw [hsupport]
      exact hZ₀sub
    exact hZsubZ₀.trans hZ₀subX
  have hZsubX : Z.support ⊆ X.support := hZsubDiff.trans Set.sdiff_subset
  have hXsubZ := hX.2 hZmin.1 hZsubX
  have huZ : u ∈ Z.support := hXsubZ huX
  exact (hZsubDiff huZ).2 rfl

/-- Contraction circuit signatures on nested supports agree up to global
sign. -/
theorem eq_or_eq_neg_of_isContractionCircuit_support_subset
    [Fintype α] {p : α} {X Y : SignedSubset α}
    (hX : M.IsContractionCircuit p X)
    (hY : M.IsContractionCircuit p Y)
    (hsub : X.support ⊆ Y.support) : X = Y ∨ X = -Y := by
  have hsupport : X.support = Y.support :=
    Set.Subset.antisymm hsub (hY.2 hX.1 hsub)
  obtain ⟨e, heX⟩ := hX.1.support_nonempty
  have heY : e ∈ Y.support := hsupport ▸ heX
  rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem
      ⟨heX, heY⟩ with hsame | hopp
  · exact Or.inl
      (eq_of_isContractionCircuit_of_support_eq_of_sameSignAt
        M hX hY hsupport heX hsame)
  · right
    apply eq_of_isContractionCircuit_of_support_eq_of_sameSignAt
      M hX (hY.neg M) (by simpa using hsupport) heX
    simpa using hopp

/-- The support-minimal erased circuits form a weak oriented matroid. -/
noncomputable def contract [Fintype α] (p : α) : WeakData α where
  circuits := {X | M.IsContractionCircuit p X}
  support_nonempty := fun hX ↦ hX.1.support_nonempty
  neg_mem := fun hX ↦ hX.neg M
  eq_or_eq_neg_of_support_subset := by
    intro X Y hX hY hsub
    exact M.eq_or_eq_neg_of_isContractionCircuit_support_subset hX hY hsub
  weakElimination := by
    intro X Y hX hY hne u hu
    obtain ⟨Z₀, hZ₀erase, hZ₀elim⟩ :=
      hX.1.weakElimination M hY.1 hne hu
    obtain ⟨Z, hZ, hZZ₀⟩ :=
      M.exists_isContractionCircuit_le hZ₀erase
    refine ⟨Z, hZ, ?_⟩
    constructor
    · intro x hxZ
      exact hZ₀elim.1 (hZZ₀.1 hxZ)
    · intro x hxZ
      exact hZ₀elim.2 (hZZ₀.2 hxZ)

/-- If an original circuit uses `p` and at least one other coordinate, its
erasure is already support-minimal in the contraction.  This is the signed
circuit form of Lemma 2.12 in the standard weak-to-strong proof. -/
theorem erase_isContractionCircuit_of_mem
    {p : α} {C : SignedSubset α} (hC : M.IsCircuit C)
    (hpC : p ∈ C.support) (hrest : (C.support \ {p}).Nonempty) :
    M.IsContractionCircuit p (C.erase p) := by
  refine ⟨M.isErasedCircuit_erase hC hrest, ?_⟩
  intro Y hY hsub
  rcases hY.2 with ⟨D, hD, rfl⟩
  have hDC : D.support ⊆ C.support := by
    intro x hxD
    by_cases hxp : x = p
    · simpa [hxp] using hpC
    · have hxEraseD : x ∈ (D.erase p).support := by
        rw [SignedSubset.support_erase]
        exact ⟨hxD, by simpa using hxp⟩
      have hxEraseC := hsub hxEraseD
      exact (by
        rw [SignedSubset.support_erase] at hxEraseC
        exact hxEraseC.1)
  rcases M.eq_or_eq_neg_of_support_subset hD hC hDC with hEq | hEq
  · simp [hEq]
  · simp [hEq]

/-- Every original circuit has, after erasing `p`, a conformal contraction
circuit which still contains any prescribed surviving coordinate.  This is
the signed-set form of the standard Lemma 2.14. -/
theorem exists_isContractionCircuit_le_preserving
    [Fintype α] {p f : α} {C : SignedSubset α}
    (hC : M.IsCircuit C) (hf : f ∈ (C.erase p).support) :
    ∃ X : SignedSubset α,
      M.IsContractionCircuit p X ∧ X ≤ C.erase p ∧ f ∈ X.support := by
  classical
  have hCrest : (C.support \ {p}).Nonempty := by
    rw [← SignedSubset.support_erase]
    exact ⟨f, hf⟩
  have hCerase : M.IsErasedCircuit p (C.erase p) :=
    M.isErasedCircuit_erase hC hCrest
  obtain ⟨Y, hYmin, hYC⟩ := M.exists_isContractionCircuit_le hCerase
  by_cases hfY : f ∈ Y.support
  · exact ⟨Y, hYmin, hYC, hfY⟩
  have hfC : f ∈ C.support := by
    rw [SignedSubset.support_erase] at hf
    exact hf.1
  have hfp : f ≠ p := by
    rw [SignedSubset.support_erase] at hf
    simpa using hf.2
  have hpC : p ∉ C.support := by
    intro hpC
    have hCmin := M.erase_isContractionCircuit_of_mem hC hpC hCrest
    have hCsubY := hCmin.2 hYmin.1 (SignedSubset.support_mono hYC)
    exact hfY (hCsubY hf)
  rcases hYmin.1.2 with ⟨D, hD, hYD⟩
  have hYsubC : Y.support ⊆ (C.erase p).support :=
    SignedSubset.support_mono hYC
  have hDsub : D.support ⊆ C.support ∪ {p} := by
    intro x hxD
    by_cases hxp : x = p
    · exact Or.inr (by simp [hxp])
    · left
      have hxY : x ∈ Y.support := by
        rw [hYD, SignedSubset.support_erase]
        exact ⟨hxD, by simpa using hxp⟩
      have hxCerase := hYsubC hxY
      rw [SignedSubset.support_erase] at hxCerase
      exact hxCerase.1
  have hpD : p ∈ D.support := by
    by_contra hpD
    have hDC : D.support ⊆ C.support := by
      intro x hxD
      rcases hDsub hxD with hxC | hxp
      · exact hxC
      · have hxp' : x = p := by simpa using hxp
        subst x
        exact (hpD hxD).elim
    rcases M.eq_or_eq_neg_of_support_subset hD hC hDC with hEq | hEq
    · apply hfY
      rw [hYD, hEq]
      exact hf
    · apply hfY
      rw [hYD, hEq]
      simpa [SignedSubset.support_erase] using hf
  have hfD : f ∉ D.support := by
    intro hfD
    apply hfY
    rw [hYD, SignedSubset.support_erase]
    exact ⟨hfD, by simpa using hfp⟩
  let P : ℕ → Prop := fun n ↦
    ∃ R : SignedSubset α,
      M.IsCircuit R ∧ R.support ⊆ C.support ∪ {p} ∧
        R.OppositeAt D p ∧ (C.separation R).ncard = n
  have hP : ∃ n, P n := by
    refine ⟨(C.separation (-D)).ncard, -D, M.neg_isCircuit hD, ?_, ?_, rfl⟩
    · simpa using hDsub
    · exact SignedSubset.oppositeAt_comm.mp
        (SignedSubset.oppositeAt_neg_self hpD)
  let n := Nat.find hP
  obtain ⟨R, hR, hRsub, hRoppD, hsepCard⟩ := Nat.find_spec hP
  have hsepEmpty : C.separation R = ∅ := by
    by_contra hsep
    obtain ⟨u, huSep⟩ : (C.separation R).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hsep
    have hCneNegR : C ≠ -R := by
      intro hEq
      apply hpC
      rw [hEq, SignedSubset.support_neg]
      exact hRoppD.mem_support_left
    obtain ⟨T, hT, hTelim⟩ := M.weakElimination hC hR hCneNegR huSep
    have hTsubU : T.support ⊆ C.support ∪ {p} := by
      intro x hxT
      have hx := (hTelim.support_subset hxT).1
      rcases hx with hxC | hxR
      · exact Or.inl hxC
      · exact hRsub hxR
    have huC : u ∈ C.support :=
      SignedSubset.OppositeAt.mem_support_left huSep
    have huT : u ∉ T.support := by
      intro huT
      exact (hTelim.support_subset huT).2 rfl
    have hpT : p ∈ T.support := by
      by_contra hpT
      have hTC : T.support ⊆ C.support := by
        intro x hxT
        rcases hTsubU hxT with hxC | hxp
        · exact hxC
        · have hxp' : x = p := by simpa using hxp
          subst x
          exact (hpT hxT).elim
      rcases M.eq_or_eq_neg_of_support_subset hT hC hTC with hEq | hEq
      · exact huT (hEq ▸ huC)
      · exact huT (by rw [hEq, SignedSubset.support_neg]; exact huC)
    have hTRsame : T.SameSignAt R p := by
      rcases hpT with hpT | hpT
      · rcases (hTelim.1 hpT).1 with hpCpos | hpRpos
        · exact (hpC (Or.inl hpCpos)).elim
        · exact Or.inl ⟨hpT, hpRpos⟩
      · rcases (hTelim.2 hpT).1 with hpCneg | hpRneg
        · exact (hpC (Or.inr hpCneg)).elim
        · exact Or.inr ⟨hpT, hpRneg⟩
    have hToppD : T.OppositeAt D p := by
      exact SignedSubset.oppositeAt_comm.mp
        ((SignedSubset.oppositeAt_comm.mp hRoppD).trans_sameSignAt
          (SignedSubset.sameSignAt_comm.mp hTRsame))
    have hTelimSwap : EliminatesAt T R C u := by
      simpa only [EliminatesAt, Set.union_comm] using hTelim
    have hsepSub : C.separation T ⊆ C.separation R \ {u} :=
      separation_subset_of_eliminates_of_support_subset
        (X := R) (Y := C) (Z := T) hTelimSwap
    have hsepStrict : C.separation T ⊂ C.separation R :=
      (hsepSub.trans Set.sdiff_subset).ssubset_of_mem_notMem huSep
        (fun hu ↦ (hsepSub hu).2 rfl)
    have hPless : P (C.separation T).ncard :=
      ⟨T, hT, hTsubU, hToppD, rfl⟩
    have hnle : n ≤ (C.separation T).ncard := Nat.find_min' hP hPless
    have hnR : n = (C.separation R).ncard := by
      simpa [n] using hsepCard.symm
    have hlt := Set.ncard_lt_ncard hsepStrict
    omega
  obtain ⟨g, hgY⟩ := hYmin.1.support_nonempty
  have hgp : g ≠ p := by
    exact fun h ↦ hYmin.1.not_mem_support M (h ▸ hgY)
  have hgD : g ∈ D.support := by
    rw [hYD, SignedSubset.support_erase] at hgY
    exact hgY.1
  have hgC : g ∈ C.support := by
    have := hYsubC hgY
    rw [SignedSubset.support_erase] at this
    exact this.1
  have hgDCsame : D.SameSignAt C g := by
    rcases hgY with hgY | hgY
    · have hgDp : g ∈ D.positive := (by
        rw [hYD] at hgY
        exact hgY.1)
      have hgCp : g ∈ C.positive := (hYC.1 hgY).1
      exact Or.inl ⟨hgDp, hgCp⟩
    · have hgDn : g ∈ D.negative := (by
        rw [hYD] at hgY
        exact hgY.1)
      have hgCn : g ∈ C.negative := (hYC.2 hgY).1
      exact Or.inr ⟨hgDn, hgCn⟩
  have hRrest : (R.support \ {p}).Nonempty := by
    by_contra hnot
    have hRsubP : R.support ⊆ {p} := by
      intro x hxR
      by_contra hxp
      exact hnot ⟨x, hxR, by simpa using hxp⟩
    have hRD : R.support ⊆ D.support :=
      hRsubP.trans (Set.singleton_subset_iff.mpr hpD)
    rcases M.eq_or_eq_neg_of_support_subset hR hD hRD with hEq | hEq
    · have hgR : g ∈ R.support := hEq ▸ hgD
      exact hgp (by simpa using hRsubP hgR)
    · have hgR : g ∈ R.support := by
        rw [hEq, SignedSubset.support_neg]
        exact hgD
      exact hgp (by simpa using hRsubP hgR)
  have hRmin : M.IsContractionCircuit p (R.erase p) :=
    M.erase_isContractionCircuit_of_mem hR hRoppD.mem_support_left hRrest
  have hRneNegD : R ≠ -D := by
    intro hEq
    have hgOpp : C.OppositeAt R g := by
      rw [hEq, SignedSubset.oppositeAt_neg_right_iff_sameSignAt]
      exact SignedSubset.sameSignAt_comm.mp hgDCsame
    have : g ∈ C.separation R := hgOpp
    rw [hsepEmpty] at this
    exact this.elim
  have hDneNegR : D ≠ -R := by
    intro hEq
    apply hRneNegD
    rw [hEq]
    simp
  obtain ⟨T, hT, hTelim⟩ :=
    M.weakElimination hD hR hDneNegR
      (SignedSubset.oppositeAt_comm.mp hRoppD)
  have hTsubC : T.support ⊆ C.support := by
    intro x hxT
    have hx := (hTelim.support_subset hxT)
    rcases hx.1 with hxD | hxR
    · rcases hDsub hxD with hxC | hxp
      · exact hxC
      · exact (hx.2 (by simpa using hxp)).elim
    · rcases hRsub hxR with hxC | hxp
      · exact hxC
      · exact (hx.2 (by simpa using hxp)).elim
  have hTeqC : T = C := by
    rcases M.eq_or_eq_neg_of_support_subset hT hC hTsubC with hEq | hEq
    · exact hEq
    · exfalso
      have hgT : g ∈ T.support := by
        rw [hEq, SignedSubset.support_neg]
        exact hgC
      have hTsameC : T.SameSignAt C g := by
        rcases hgT with hgTp | hgTn
        · rcases (hTelim.1 hgTp).1 with hgDp | hgRp
          · exact Or.inl ⟨hgTp, hgDCsame.positive_iff.mp hgDp⟩
          · have hgCp : g ∈ C.positive := by
              rcases hgC with hgCp | hgCn
              · exact hgCp
              · have : g ∈ C.separation R := Or.inr ⟨hgCn, hgRp⟩
                rw [hsepEmpty] at this
                exact this.elim
            exact Or.inl ⟨hgTp, hgCp⟩
        · rcases (hTelim.2 hgTn).1 with hgDn | hgRn
          · exact Or.inr ⟨hgTn, hgDCsame.negative_iff.mp hgDn⟩
          · have hgCn : g ∈ C.negative := by
              rcases hgC with hgCp | hgCn
              · have : g ∈ C.separation R := Or.inl ⟨hgCp, hgRn⟩
                rw [hsepEmpty] at this
                exact this.elim
              · exact hgCn
            exact Or.inr ⟨hgTn, hgCn⟩
      have hToppC : T.OppositeAt C g := by
        rw [hEq]
        exact SignedSubset.oppositeAt_comm.mp
          (SignedSubset.oppositeAt_neg_self hgC)
      exact hTsameC.not_oppositeAt hToppC
  have hfR : f ∈ R.support := by
    rcases hfC with hfCp | hfCn
    · have hfTp : f ∈ T.positive := hTeqC ▸ hfCp
      rcases (hTelim.1 hfTp).1 with hfDp | hfRp
      · exact (hfD (Or.inl hfDp)).elim
      · exact Or.inl hfRp
    · have hfTn : f ∈ T.negative := hTeqC ▸ hfCn
      rcases (hTelim.2 hfTn).1 with hfDn | hfRn
      · exact (hfD (Or.inr hfDn)).elim
      · exact Or.inr hfRn
  have hReraseLe : R.erase p ≤ C.erase p := by
    apply le_of_support_subset_of_separation_eq_empty
    · intro x hxR
      rw [SignedSubset.support_erase] at hxR ⊢
      rcases hRsub hxR.1 with hxC | hxp
      · exact ⟨hxC, fun hxp ↦ hpC (hxp ▸ hxC)⟩
      · exact (hxR.2 (by simpa using hxp)).elim
    · apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hxSep⟩
      have hxCR : x ∈ C.separation R := by
        rcases hxSep with hxSep | hxSep
        · exact Or.inr ⟨hxSep.2.1, hxSep.1.1⟩
        · exact Or.inl ⟨hxSep.2.1, hxSep.1.1⟩
      rw [hsepEmpty] at hxCR
      exact hxCR.elim
  refine ⟨R.erase p, hRmin, hReraseLe, ?_⟩
  rw [SignedSubset.support_erase]
  exact ⟨hfR, by simpa using hfp⟩

/-- A coordinate protected by `SurvivesFrom` cannot be a separation
coordinate. -/
private theorem survives_ne_of_opposite
    {C D : SignedSubset α} {u v : α}
    (hu : C.OppositeAt D u) (hv : SurvivesFrom C D v) : v ≠ u := by
  intro h
  subst v
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact hv.2 hu.2
  · exact (Set.disjoint_left.1 C.disjoint hu.1 hv.1).elim
  · exact (Set.disjoint_left.1 C.disjoint hv.1 hu.1).elim
  · exact hv.2 hu.2

/-- Erasing a different coordinate preserves an opposite-sign witness. -/
private theorem oppositeAt_erase
    {C D : SignedSubset α} {p u : α} (hpu : u ≠ p)
    (hu : C.OppositeAt D u) :
    (C.erase p).OppositeAt (D.erase p) u := by
  rcases hu with hu | hu
  · exact Or.inl ⟨⟨hu.1, by simpa using hpu⟩,
      ⟨hu.2, by simpa using hpu⟩⟩
  · exact Or.inr ⟨⟨hu.1, by simpa using hpu⟩,
      ⟨hu.2, by simpa using hpu⟩⟩

/-- Erasing a different coordinate preserves a protected survivor. -/
private theorem survivesFrom_erase
    {C D : SignedSubset α} {p v : α} (hvp : v ≠ p)
    (hv : SurvivesFrom C D v) :
    SurvivesFrom (C.erase p) (D.erase p) v := by
  rcases hv with hv | hv
  · exact Or.inl ⟨⟨hv.1, by simpa using hvp⟩,
      fun h ↦ hv.2 h.1⟩
  · exact Or.inr ⟨⟨hv.1, by simpa using hvp⟩,
      fun h ↦ hv.2 h.1⟩

/-- Erasure is signed inclusion. -/
private theorem erase_le_self (C : SignedSubset α) (p : α) :
    C.erase p ≤ C :=
  ⟨Set.sdiff_subset, Set.sdiff_subset⟩

/-- Elimination is monotone when its two input sign vectors are enlarged
without changing signs. -/
private theorem EliminatesAt.mono_inputs
    {Z X Y C D : SignedSubset α} {u : α}
    (hZ : EliminatesAt Z X Y u) (hXC : X ≤ C) (hYD : Y ≤ D) :
    EliminatesAt Z C D u := by
  constructor
  · intro x hxZ
    have hx := hZ.1 hxZ
    refine ⟨?_, hx.2⟩
    rcases hx.1 with hxX | hxY
    · exact Or.inl (hXC.1 hxX)
    · exact Or.inr (hYD.1 hxY)
  · intro x hxZ
    have hx := hZ.2 hxZ
    refine ⟨?_, hx.2⟩
    rcases hx.1 with hxX | hxY
    · exact Or.inl (hXC.2 hxX)
    · exact Or.inr (hYD.2 hxY)

/-- Lift an elimination statement for an erasure back to the original sign
vector.  The erased coordinate is harmless when it is absent or agrees with
the second target input. -/
private theorem eliminatesAt_of_erase_eliminates_of_goodAt
    {V C D : SignedSubset α} {p u : α}
    (hpu : u ≠ p) (hV : EliminatesAt (V.erase p) C D u)
    (hgood : p ∉ V.support ∨ V.SameSignAt D p) :
    EliminatesAt V C D u := by
  constructor
  · intro x hxV
    by_cases hxp : x = p
    · subst x
      rcases hgood with hpV | hsame
      · exact (hpV (Or.inl hxV)).elim
      · exact ⟨Or.inr (hsame.positive_iff.mp hxV), by simpa using hpu.symm⟩
    · exact hV.1 ⟨hxV, by simpa using hxp⟩
  · intro x hxV
    by_cases hxp : x = p
    · subst x
      rcases hgood with hpV | hsame
      · exact (hpV (Or.inr hxV)).elim
      · exact ⟨Or.inr (hsame.negative_iff.mp hxV), by simpa using hpu.symm⟩
    · exact hV.2 ⟨hxV, by simpa using hxp⟩

/-- The induction step when the two input circuits have a second separation
coordinate.  Contracting that coordinate strictly decreases the union of
supports; lifting is safe because both signs are allowed at a separation
coordinate. -/
private theorem strongElimination_of_other_separator
    [Fintype α] {n : ℕ} {C D : SignedSubset α} {u v : α}
    (hC : M.IsCircuit C) (hD : M.IsCircuit D)
    (hu : C.OppositeAt D u) (hv : SurvivesFrom C D v)
    (hn : (C.support ∪ D.support).ncard = n)
    (hother : (C.separation D \ {u}).Nonempty)
    (ih : ∀ (N : WeakData α) {A B : SignedSubset α},
      N.IsCircuit A → N.IsCircuit B →
      ∀ {a b : α}, A.OppositeAt B a → SurvivesFrom A B b →
        (A.support ∪ B.support).ncard < n →
        ∃ Z : SignedSubset α,
          N.IsCircuit Z ∧ EliminatesAt Z A B a ∧ b ∈ Z.support) :
    ∃ Z : SignedSubset α,
      M.IsCircuit Z ∧ EliminatesAt Z C D u ∧ v ∈ Z.support := by
  classical
  obtain ⟨p, hpSep, hpuSet⟩ := hother
  have hpu : p ≠ u := by simpa using hpuSet
  have hup : u ≠ p := hpu.symm
  have hpOpp : C.OppositeAt D p := hpSep
  have hCrest : (C.support \ {p}).Nonempty :=
    ⟨u, hu.mem_support_left, by simpa using hup⟩
  have hDrest : (D.support \ {p}).Nonempty :=
    ⟨u, hu.mem_support_right, by simpa using hup⟩
  have hCp : (M.contract p).IsCircuit (C.erase p) :=
    M.erase_isContractionCircuit_of_mem hC hpOpp.mem_support_left hCrest
  have hDp : (M.contract p).IsCircuit (D.erase p) :=
    M.erase_isContractionCircuit_of_mem hD hpOpp.mem_support_right hDrest
  have hvp : v ≠ p := survives_ne_of_opposite hpOpp hv
  have huErase := oppositeAt_erase hup hu
  have hvErase := survivesFrom_erase hvp hv
  have hsub :
      (C.erase p).support ∪ (D.erase p).support ⊆
        C.support ∪ D.support := by
    intro x hx
    rcases hx with hx | hx
    · left
      rw [SignedSubset.support_erase] at hx
      exact hx.1
    · right
      rw [SignedSubset.support_erase] at hx
      exact hx.1
  have hpBig : p ∈ C.support ∪ D.support :=
    Or.inl hpOpp.mem_support_left
  have hpSmall : p ∉ (C.erase p).support ∪ (D.erase p).support := by
    simp
  have hstrict :
      (C.erase p).support ∪ (D.erase p).support ⊂
        C.support ∪ D.support :=
    hsub.ssubset_of_mem_notMem hpBig hpSmall
  have hlt :
      ((C.erase p).support ∪ (D.erase p).support).ncard < n := by
    rw [← hn]
    exact Set.ncard_lt_ncard hstrict
  obtain ⟨Zp, hZp, hZpelim, hvZp⟩ :=
    ih (M.contract p) hCp hDp huErase hvErase hlt
  rcases hZp.1.2 with ⟨Z, hZ, hZpEq⟩
  refine ⟨Z, hZ, ?_, ?_⟩
  · constructor
    · intro x hxZ
      by_cases hxp : x = p
      · subst x
        refine ⟨?_, by simpa using hpu⟩
        rcases hpOpp with hpOpp | hpOpp
        · exact Or.inl hpOpp.1
        · exact Or.inr hpOpp.2
      · have hxZp : x ∈ Zp.positive := by
          rw [hZpEq]
          exact ⟨hxZ, by simpa using hxp⟩
        have hx := hZpelim.1 hxZp
        refine ⟨?_, hx.2⟩
        rcases hx.1 with hxC | hxD
        · exact Or.inl hxC.1
        · exact Or.inr hxD.1
    · intro x hxZ
      by_cases hxp : x = p
      · subst x
        refine ⟨?_, by simpa using hpu⟩
        rcases hpOpp with hpOpp | hpOpp
        · exact Or.inr hpOpp.2
        · exact Or.inl hpOpp.1
      · have hxZp : x ∈ Zp.negative := by
          rw [hZpEq]
          exact ⟨hxZ, by simpa using hxp⟩
        have hx := hZpelim.2 hxZp
        refine ⟨?_, hx.2⟩
        rcases hx.1 with hxC | hxD
        · exact Or.inl hxC.1
        · exact Or.inr hxD.1
  · have hvEraseZ : v ∈ (Z.erase p).support := by
      rw [← hZpEq]
      exact hvZp
    rw [SignedSubset.support_erase] at hvEraseZ
    exact hvEraseZ.1

/-- A sign vector conformal to `C` away from `p` and vanishing at `u` is an
elimination of `u` after `p` is erased. -/
private theorem erase_eliminatesAt_of_erase_le_of_not_mem
    {V C D : SignedSubset α} {p u : α}
    (hVC : V.erase p ≤ C.erase p) (huV : u ∉ V.support) :
    EliminatesAt (V.erase p) C D u := by
  constructor
  · intro x hxV
    refine ⟨Or.inl ((hVC.1 hxV).1), ?_⟩
    exact fun h ↦ huV (h ▸ Or.inl hxV.1)
  · intro x hxV
    refine ⟨Or.inl ((hVC.2 hxV).1), ?_⟩
    exact fun h ↦ huV (h ▸ Or.inr hxV.1)

/-- If `V` obeys an elimination bound except possibly at `p`, `U` obeys
the bound everywhere, and `Z` eliminates `p` between them, then `Z` obeys
the original bound everywhere. -/
private theorem eliminatesAt_of_eliminating_exception
    {Z V U C D : SignedSubset α} {p u : α}
    (hZ : EliminatesAt Z V U p)
    (hV : EliminatesAt (V.erase p) C D u)
    (hU : EliminatesAt U C D u) :
    EliminatesAt Z C D u := by
  constructor
  · intro x hxZ
    have hx := hZ.1 hxZ
    rcases hx.1 with hxV | hxU
    · exact hV.1 ⟨hxV, hx.2⟩
    · exact hU.1 hxU
  · intro x hxZ
    have hx := hZ.2 hxZ
    rcases hx.1 with hxV | hxU
    · exact hV.2 ⟨hxV, hx.2⟩
    · exact hU.2 hxU

/-- Signed inclusion of erasures determines the same sign at every retained
support coordinate. -/
private theorem sameSignAt_of_mem_of_erase_le
    {V C : SignedSubset α} {p x : α} (hxp : x ≠ p)
    (hxV : x ∈ V.support) (hVC : V.erase p ≤ C.erase p) :
    V.SameSignAt C x := by
  rcases hxV with hxV | hxV
  · have hxC := hVC.1 ⟨hxV, by simpa using hxp⟩
    exact Or.inl ⟨hxV, hxC.1⟩
  · have hxC := hVC.2 ⟨hxV, by simpa using hxp⟩
    exact Or.inr ⟨hxV, hxC.1⟩

/-- The difficult induction step: start with an ordinary elimination `U`.
If it loses the protected coordinate, Lemma 2.14 supplies a contraction
circuit preserving it.  Any bad sign at the contracted coordinate is then
removed by a strictly smaller recursive elimination. -/
private theorem strongElimination_of_unique_separator
    [Fintype α] {n : ℕ} {C D : SignedSubset α} {u v : α}
    (hC : M.IsCircuit C) (hD : M.IsCircuit D)
    (hu : C.OppositeAt D u) (hv : SurvivesFrom C D v)
    (hn : (C.support ∪ D.support).ncard = n)
    (_hunique : ¬ (C.separation D \ {u}).Nonempty)
    (ih : ∀ (N : WeakData α) {A B : SignedSubset α},
      N.IsCircuit A → N.IsCircuit B →
      ∀ {a b : α}, A.OppositeAt B a → SurvivesFrom A B b →
        (A.support ∪ B.support).ncard < n →
        ∃ Z : SignedSubset α,
          N.IsCircuit Z ∧ EliminatesAt Z A B a ∧ b ∈ Z.support) :
    ∃ Z : SignedSubset α,
      M.IsCircuit Z ∧ EliminatesAt Z C D u ∧ v ∈ Z.support := by
  classical
  have hCneNegD : C ≠ -D := by
    intro hEq
    have hDEq : D = -C := by
      rw [hEq]
      simp
    have hvC : v ∈ C.support := by
      rcases hv with hv | hv
      · exact Or.inl hv.1
      · exact Or.inr hv.1
    have hvOpp : C.OppositeAt D v := by
      rw [hDEq]
      exact SignedSubset.oppositeAt_neg_self hvC
    exact (survives_ne_of_opposite hvOpp hv) rfl
  obtain ⟨U, hU, hUelim⟩ := M.weakElimination hC hD hCneNegD hu
  by_cases hvU : v ∈ U.support
  · exact ⟨U, hU, hUelim, hvU⟩
  have huU : u ∉ U.support := by
    intro huU
    exact (hUelim.support_subset huU).2 rfl
  have hUnotSubC : ¬ U.support ⊆ C.support := by
    intro hUC
    rcases M.eq_or_eq_neg_of_support_subset hU hC hUC with hEq | hEq
    · exact huU (hEq ▸ hu.mem_support_left)
    · apply huU
      rw [hEq, SignedSubset.support_neg]
      exact hu.mem_support_left
  obtain ⟨p, hpU, hpC⟩ := Set.not_subset.mp hUnotSubC
  have hpu : p ≠ u := by
    intro h
    subst p
    exact hpC hu.mem_support_left
  have hup : u ≠ p := hpu.symm
  have hpUDsame : U.SameSignAt D p := by
    rcases hpU with hpUp | hpUn
    · rcases (hUelim.1 hpUp).1 with hpCp | hpDp
      · exact (hpC (Or.inl hpCp)).elim
      · exact Or.inl ⟨hpUp, hpDp⟩
    · rcases (hUelim.2 hpUn).1 with hpCn | hpDn
      · exact (hpC (Or.inr hpCn)).elim
      · exact Or.inr ⟨hpUn, hpDn⟩
  have hpD : p ∈ D.support := hpUDsame.mem_support_right
  have hvC : v ∈ C.support := by
    rcases hv with hv | hv
    · exact Or.inl hv.1
    · exact Or.inr hv.1
  have hvp : v ≠ p := by
    intro h
    subst v
    exact hpC hvC
  have hvCerase : v ∈ (C.erase p).support := by
    rw [SignedSubset.support_erase]
    exact ⟨hvC, by simpa using hvp⟩
  obtain ⟨X, hX, hXC, hvX⟩ :=
    M.exists_isContractionCircuit_le_preserving hC hvCerase
  rcases hX.1.2 with ⟨V, hV, hXEq⟩
  have hVEraseLe : V.erase p ≤ C.erase p := by
    rw [← hXEq]
    exact hXC
  have hvV : v ∈ V.support := by
    have : v ∈ (V.erase p).support := by
      rw [← hXEq]
      exact hvX
    rw [SignedSubset.support_erase] at this
    exact this.1
  have eliminateException : ∀ {Q : SignedSubset α},
      M.IsCircuit Q → EliminatesAt (Q.erase p) C D u →
      v ∈ Q.support → Q.OppositeAt U p →
      ∃ Z : SignedSubset α,
        M.IsCircuit Z ∧ EliminatesAt Z C D u ∧ v ∈ Z.support := by
    intro Q hQ hQerase hvQ hpQU
    have hvQU : SurvivesFrom Q U v := by
      rcases hvQ with hvQp | hvQn
      · exact Or.inl ⟨hvQp, fun hvUn ↦ hvU (Or.inr hvUn)⟩
      · exact Or.inr ⟨hvQn, fun hvUp ↦ hvU (Or.inl hvUp)⟩
    have hsub : Q.support ∪ U.support ⊆
        (C.support ∪ D.support) \ {u} := by
      intro x hx
      rcases hx with hxQ | hxU
      · by_cases hxp : x = p
        · subst x
          exact ⟨Or.inr hpD, by simpa using hpu⟩
        · have hxErase : x ∈ (Q.erase p).support := by
            rw [SignedSubset.support_erase]
            exact ⟨hxQ, by simpa using hxp⟩
          exact hQerase.support_subset hxErase
      · exact hUelim.support_subset hxU
    have hstrict : Q.support ∪ U.support ⊂
        C.support ∪ D.support :=
      (hsub.trans Set.sdiff_subset).ssubset_of_mem_notMem
        (Or.inl hu.mem_support_left) (fun hu' ↦ (hsub hu').2 rfl)
    have hlt : (Q.support ∪ U.support).ncard < n := by
      rw [← hn]
      exact Set.ncard_lt_ncard hstrict
    obtain ⟨Z, hZ, hZelim, hvZ⟩ :=
      ih M hQ hU hpQU hvQU hlt
    exact ⟨Z, hZ,
      eliminatesAt_of_eliminating_exception hZelim hQerase hUelim, hvZ⟩
  by_cases huV : u ∈ V.support
  · have huVCsame : V.SameSignAt C u :=
      sameSignAt_of_mem_of_erase_le hup huV hVEraseLe
    have huVDopp : V.OppositeAt D u := by
      exact SignedSubset.oppositeAt_comm.mp
        ((SignedSubset.oppositeAt_comm.mp hu).trans_sameSignAt
          (SignedSubset.sameSignAt_comm.mp huVCsame))
    have huXD : X.OppositeAt (D.erase p) u := by
      rw [hXEq]
      exact oppositeAt_erase hup huVDopp
    have hvVCsame : V.SameSignAt C v :=
      sameSignAt_of_mem_of_erase_le hvp hvV hVEraseLe
    have hvVD : SurvivesFrom V D v := by
      rcases hv with hv | hv
      · exact Or.inl ⟨hvVCsame.positive_iff.mpr hv.1, hv.2⟩
      · exact Or.inr ⟨hvVCsame.negative_iff.mpr hv.1, hv.2⟩
    have hvXD : SurvivesFrom X (D.erase p) v := by
      rw [hXEq]
      exact survivesFrom_erase hvp hvVD
    have hDrest : (D.support \ {p}).Nonempty :=
      ⟨u, hu.mem_support_right, by simpa using hup⟩
    have hDp : (M.contract p).IsCircuit (D.erase p) :=
      M.erase_isContractionCircuit_of_mem hD hpD hDrest
    have hsub : X.support ∪ (D.erase p).support ⊆
        C.support ∪ D.support := by
      intro x hx
      rcases hx with hxX | hxD
      · left
        have hxC := SignedSubset.support_mono hXC hxX
        rw [SignedSubset.support_erase] at hxC
        exact hxC.1
      · right
        rw [SignedSubset.support_erase] at hxD
        exact hxD.1
    have hpSmall : p ∉ X.support ∪ (D.erase p).support := by
      rintro (hpX | hpD')
      · exact hX.1.not_mem_support M hpX
      · simp at hpD'
    have hstrict : X.support ∪ (D.erase p).support ⊂
        C.support ∪ D.support :=
      hsub.ssubset_of_mem_notMem (Or.inr hpD) hpSmall
    have hlt : (X.support ∪ (D.erase p).support).ncard < n := by
      rw [← hn]
      exact Set.ncard_lt_ncard hstrict
    obtain ⟨Wp, hWp, hWpelim, hvWp⟩ :=
      ih (M.contract p) hX hDp huXD hvXD hlt
    rcases hWp.1.2 with ⟨W, hW, hWpEq⟩
    have hWEraseElim : EliminatesAt (W.erase p) C D u := by
      rw [← hWpEq]
      exact EliminatesAt.mono_inputs hWpelim
        (hXC.trans (erase_le_self C p)) (erase_le_self D p)
    have hvW : v ∈ W.support := by
      have : v ∈ (W.erase p).support := by
        rw [← hWpEq]
        exact hvWp
      rw [SignedSubset.support_erase] at this
      exact this.1
    by_cases hpW : p ∈ W.support
    · rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem
          ⟨hpW, hpD⟩ with hpSame | hpOpp
      · exact ⟨W, hW,
          eliminatesAt_of_erase_eliminates_of_goodAt hup hWEraseElim
            (Or.inr hpSame), hvW⟩
      · have hpWU : W.OppositeAt U p :=
          hpOpp.trans_sameSignAt (SignedSubset.sameSignAt_comm.mp hpUDsame)
        exact eliminateException hW hWEraseElim hvW hpWU
    · exact ⟨W, hW,
        eliminatesAt_of_erase_eliminates_of_goodAt hup hWEraseElim
          (Or.inl hpW), hvW⟩
  · have hVEraseElim : EliminatesAt (V.erase p) C D u :=
      erase_eliminatesAt_of_erase_le_of_not_mem hVEraseLe huV
    by_cases hpV : p ∈ V.support
    · rcases SignedSubset.sameSignAt_or_oppositeAt_of_mem
          ⟨hpV, hpD⟩ with hpSame | hpOpp
      · exact ⟨V, hV,
          eliminatesAt_of_erase_eliminates_of_goodAt hup hVEraseElim
            (Or.inr hpSame), hvV⟩
      · have hpVU : V.OppositeAt U p :=
          hpOpp.trans_sameSignAt (SignedSubset.sameSignAt_comm.mp hpUDsame)
        exact eliminateException hV hVEraseElim hvV hpVU
    · exact ⟨V, hV,
        eliminatesAt_of_erase_eliminates_of_goodAt hup hVEraseElim
          (Or.inl hpV), hvV⟩

/-- Weak circuit elimination implies the strong circuit-elimination form on
a finite ground type.  The proof is the standard contraction induction, but
all contraction and preservation lemmas used by the induction are proved
above from the weak axioms alone. -/
theorem strongElimination
    [Fintype α] {C D : SignedSubset α}
    (hC : M.IsCircuit C) (hD : M.IsCircuit D)
    {u v : α} (hu : C.OppositeAt D u) (hv : SurvivesFrom C D v) :
    ∃ Z : SignedSubset α,
      M.IsCircuit Z ∧ EliminatesAt Z C D u ∧ v ∈ Z.support := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (N : WeakData α) {A B : SignedSubset α},
      N.IsCircuit A → N.IsCircuit B →
      ∀ {a b : α}, A.OppositeAt B a → SurvivesFrom A B b →
        (A.support ∪ B.support).ncard = n →
        ∃ Z : SignedSubset α,
          N.IsCircuit Z ∧ EliminatesAt Z A B a ∧ b ∈ Z.support
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro N A B hA hB a b ha hb hn
        have ih' : ∀ (N' : WeakData α) {A' B' : SignedSubset α},
            N'.IsCircuit A' → N'.IsCircuit B' →
            ∀ {a' b' : α}, A'.OppositeAt B' a' →
              SurvivesFrom A' B' b' →
              (A'.support ∪ B'.support).ncard < n →
              ∃ Z : SignedSubset α,
                N'.IsCircuit Z ∧ EliminatesAt Z A' B' a' ∧
                  b' ∈ Z.support := by
          intro N' A' B' hA' hB' a' b' ha' hb' hlt
          exact ih _ hlt N' hA' hB' ha' hb' rfl
        by_cases hother : (A.separation B \ {a}).Nonempty
        · exact strongElimination_of_other_separator
            N hA hB ha hb hn hother ih'
        · exact strongElimination_of_unique_separator
            N hA hB ha hb hn hother ih'
  exact hP (C.support ∪ D.support).ncard M hC hD hu hv rfl

/-- Package proof-local weak signed-circuit data as the public `Data`
interface. -/
def toData : OrientedMatroid.Data α where
  circuits := M.circuits
  support_nonempty := M.support_nonempty
  neg_mem := M.neg_mem
  eq_or_eq_neg_of_support_subset := M.eq_or_eq_neg_of_support_subset
  weakElimination := M.weakElimination

@[simp]
theorem toData_circuits : M.toData.circuits = M.circuits := rfl

@[simp]
theorem toData_ofData (N : Data α) : (ofData N).toData = N :=
  Data.ext_circuits rfl

@[simp]
theorem ofData_toData : ofData M.toData = M :=
  WeakData.ext_circuits rfl

end WeakData

namespace Data

/-- Strong circuit elimination is derived from the weak circuit axioms on a
finite ground type.  It is intentionally not a field of `Data`. -/
theorem strongElimination [Finite α] (M : Data α)
    {C D : SignedSubset α} (hC : M.IsCircuit C) (hD : M.IsCircuit D)
    {u v : α} (hu : C.OppositeAt D u) (hv : SurvivesFrom C D v) :
    ∃ Z : SignedSubset α,
      M.IsCircuit Z ∧ EliminatesAt Z C D u ∧ v ∈ Z.support := by
  classical
  let : Fintype α := Fintype.ofFinite α
  exact (WeakData.ofData M).strongElimination hC hD hu hv

/-- Standard exact-sign form of strong circuit elimination: the protected
coordinate remains present with its sign from the first input circuit. -/
theorem strongElimination_sameSign [Finite α] (M : Data α)
    {C D : SignedSubset α} (hC : M.IsCircuit C) (hD : M.IsCircuit D)
    {u v : α} (hu : C.OppositeAt D u) (hv : SurvivesFrom C D v) :
    ∃ Z : SignedSubset α,
      M.IsCircuit Z ∧ EliminatesAt Z C D u ∧ Z.SameSignAt C v := by
  obtain ⟨Z, hZ, hZelim, hvZ⟩ := M.strongElimination hC hD hu hv
  exact ⟨Z, hZ, hZelim,
    hZelim.sameSignAt_of_survivesFrom_of_mem_support hv hvZ⟩

end Data

end OrientedMatroid

end BeyondSperner
