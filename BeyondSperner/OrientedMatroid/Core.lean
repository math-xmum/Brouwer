import BeyondSperner.OrientedMatroid.SignedSubset

/-!
# Core signed-circuit interface

This module contains only the weak signed-circuit axioms.  It is deliberately
independent of the weak-to-strong theorem, so that strong elimination can be
proved from this interface without a circular import or a hidden extra field.
-/

namespace BeyondSperner

open Set

namespace OrientedMatroid

variable {α : Type*}

/-- The support-and-sign containment required of a circuit obtained by
eliminating `u`. -/
def EliminatesAt (Z C D : SignedSubset α) (u : α) : Prop :=
  Z.positive ⊆ (C.positive ∪ D.positive) \ {u} ∧
    Z.negative ⊆ (C.negative ∪ D.negative) \ {u}

/-- `v` has a sign in `C` which is not cancelled by the opposite sign in
`D`. -/
def SurvivesFrom (C D : SignedSubset α) (v : α) : Prop :=
  v ∈ C.positive \ D.negative ∨ v ∈ C.negative \ D.positive

/-- `SurvivesFrom` is exactly the usual strong-elimination condition
`v ∈ supp(C) \ S(C,D)`. -/
theorem survivesFrom_iff_mem_support_sdiff_separation
    {C D : SignedSubset α} {v : α} :
    SurvivesFrom C D v ↔ v ∈ C.support \ C.separation D := by
  constructor
  · rintro (hv | hv)
    · refine ⟨Or.inl hv.1, ?_⟩
      rintro (hsep | hsep)
      · exact hv.2 hsep.2
      · exact Set.disjoint_left.1 C.disjoint hv.1 hsep.1
    · refine ⟨Or.inr hv.1, ?_⟩
      rintro (hsep | hsep)
      · exact Set.disjoint_left.1 C.disjoint hsep.1 hv.1
      · exact hv.2 hsep.2
  · rintro ⟨hvC, hvSep⟩
    rcases hvC with hvCp | hvCn
    · exact Or.inl ⟨hvCp, fun hvDn ↦ hvSep (Or.inl ⟨hvCp, hvDn⟩)⟩
    · exact Or.inr ⟨hvCn, fun hvDp ↦ hvSep (Or.inr ⟨hvCn, hvDp⟩)⟩

/-- Unsigned support containment implied by signed elimination. -/
theorem EliminatesAt.support_subset {Z C D : SignedSubset α} {u : α}
    (h : EliminatesAt Z C D u) :
    Z.support ⊆ (C.support ∪ D.support) \ {u} := by
  intro x hx
  constructor
  · rcases hx with hx | hx
    · rcases (h.1 hx).1 with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (Or.inl hx)
    · rcases (h.2 hx).1 with hx | hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inr (Or.inr hx)
  · rcases hx with hx | hx
    · exact (h.1 hx).2
    · exact (h.2 hx).2

/-- At a protected coordinate, support retention in an elimination forces
the output to carry the original sign from the first circuit. -/
theorem EliminatesAt.sameSignAt_of_survivesFrom_of_mem_support
    {Z C D : SignedSubset α} {u v : α} (hZ : EliminatesAt Z C D u)
    (hv : SurvivesFrom C D v) (hvZ : v ∈ Z.support) :
    Z.SameSignAt C v := by
  rcases hv with hv | hv <;> rcases hvZ with hvZ | hvZ
  · exact Or.inl ⟨hvZ, hv.1⟩
  · rcases (hZ.2 hvZ).1 with hvCn | hvDn
    · exact (Set.disjoint_left.1 C.disjoint hv.1 hvCn).elim
    · exact (hv.2 hvDn).elim
  · rcases (hZ.1 hvZ).1 with hvCp | hvDp
    · exact (Set.disjoint_left.1 C.disjoint hvCp hv.1).elim
    · exact (hv.2 hvDp).elim
  · exact Or.inr ⟨hvZ, hv.1⟩

/-- An oriented matroid presented by signed circuits, using only the weak
circuit-elimination axiom.  Strong elimination is derived for finite ground
types in `WeakStrongElimination`. -/
structure Data (α : Type*) where
  circuits : Set (SignedSubset α)
  support_nonempty : ∀ {C}, C ∈ circuits → C.support.Nonempty
  neg_mem : ∀ {C}, C ∈ circuits → -C ∈ circuits
  eq_or_eq_neg_of_support_subset : ∀ {C D}, C ∈ circuits → D ∈ circuits →
    C.support ⊆ D.support → C = D ∨ C = -D
  weakElimination : ∀ {C D}, C ∈ circuits → D ∈ circuits → C ≠ -D →
    ∀ {u}, C.OppositeAt D u →
      ∃ Z : SignedSubset α, Z ∈ circuits ∧ EliminatesAt Z C D u

/-- Two circuit presentations are equal once their signed-circuit sets agree;
all remaining structure fields are propositions. -/
@[ext]
theorem Data.ext_circuits {M N : Data α} (h : M.circuits = N.circuits) :
    M = N := by
  cases M
  cases N
  simp_all

namespace Data

variable (M : Data α)

/-- Predicate saying that a signed subset is an oriented circuit. -/
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

end Data

end OrientedMatroid

end BeyondSperner
