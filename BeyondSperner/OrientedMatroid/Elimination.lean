import BeyondSperner.OrientedMatroid.Basic

/-!
# Circuit elimination

Statements corresponding to Theorem 5.1 and Corollary 5.2.  Strong
elimination is exposed as the finite weak-to-strong theorem proved in
`WeakStrongElimination`, not as a primitive interface field.
-/

namespace BeyondSperner

namespace OrientedMatroid

open Set

variable {α : Type*} (M : Data α)

/--
Strong circuit elimination, in the form of Ivanov's Theorem 5.1: besides eliminating `u`, the
resulting circuit can be required to retain a prescribed surviving element `v`.
-/
theorem strongElimination
    [Finite α]
    {C D : SignedSubset α} (hC : M.IsCircuit C) (hD : M.IsCircuit D)
    {u v : α} (hu : C.OppositeAt D u) (hv : SurvivesFrom C D v) :
    ∃ Z : SignedSubset α,
      M.IsCircuit Z ∧ EliminatesAt Z C D u ∧ v ∈ Z.support :=
  M.strongElimination hC hD hu hv

/-- Weak elimination (Corollary 5.2), exposed as a theorem-facing API. -/
theorem weakElimination
    {C D : SignedSubset α} (hC : M.IsCircuit C) (hD : M.IsCircuit D)
    (hne : C ≠ -D) {u : α} (hu : C.OppositeAt D u) :
    ∃ Z : SignedSubset α, M.IsCircuit Z ∧ EliminatesAt Z C D u :=
  M.weakElimination hC hD hne hu

end OrientedMatroid

end BeyondSperner
