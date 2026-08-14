import BeyondSperner.Coloring.InwardTangent
import FormalizationInterface.Theorem10_8Intersection

/-!
# Theorem 10.10 through the intersection proof of Theorem 10.8

The existing coordinate proof of Theorem 10.10 consumes an enriched
Theorem 10.8 witness with explicit coefficients.  The public
`IsAffineSolution` interface only records convex-hull membership.  The
mathematical module `InwardTangent` now reconstructs nonnegative weights from
that membership and proves that all artificial reference-vertex weights
vanish.  This external adapter supplies its solution using the paper-route
Theorem 10.8.
-/

namespace BeyondSperner
namespace AffineColoring

open Classical Set

variable {I V E : Type*} [Fintype I] [Fintype V]
  [DecidableEq I] [DecidableEq V] [Nonempty I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] [DecidableEq I] in
/-- The centered origin belongs to the reference simplex. -/
theorem zero_mem_referenceSimplex_of_centered
    (b : AffineBasis I ℝ E) (hb : IsCenteredAffineBasis b) :
    (0 : E) ∈ convexHull ℝ (Set.range b) := by
  rw [b.convexHull_eq_nonneg_coord]
  intro i
  rw [coord_zero_eq_inv_card b hb i]
  exact inv_nonneg.mpr (by positivity)

/-- The core of Theorem 10.10 using the paper-route proof of Theorem 10.8. -/
theorem theorem10_10_core_via_intersection
    (D : SimplexFamily I V)
    (b : AffineBasis I ℝ E) (hb : IsCenteredAffineBasis b)
    (p c : D.Vertex → E)
    (hchain : D.IsChainSimplex)
    (hface : ∀ (C : Finset I) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hinward : IsInwardTangentColoring D b p c) :
    ∃ C : Finset I, ∃ tau : Finset V, ∃ htau : tau ∈ D.complex C,
      C.Nonempty ∧ tau.card = C.card ∧
        (0 : E) ∈ convexHull ℝ
          (affineSimplexColorPoints D c C tau htau : Set E) := by
  apply theorem10_10_core_of_affineSolution D b hb p c hface hinward
  exact theorem10_8_via_intersection D b c 0
    (zero_mem_referenceSimplex_of_centered b hb) hchain

/-- The full Theorem 10.10 through the paper-route proof of Theorem 10.8. -/
theorem theorem10_10_via_intersection
    (D : SimplexFamily I V)
    (b : AffineBasis I ℝ E) (hb : IsCenteredAffineBasis b)
    (p c : D.Vertex → E)
    (hchain : D.IsChainSimplex)
    (hface : ∀ (C : Finset I) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hinward : IsInwardTangentColoring D b p c)
    (hAmbient : ∀ (C : Finset I) (tau : Finset V),
      tau ∈ D.complex C → tau ∈ D.complex Finset.univ)
    (hPure : (D.complex Finset.univ).IsPureOfCardinality (Fintype.card I)) :
    ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
      sigma.card = Fintype.card I ∧
        (0 : E) ∈ convexHull ℝ
          (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set E) := by
  exact theorem10_10_of_core D c
    (theorem10_10_core_via_intersection D b hb p c hchain hface hinward)
    hAmbient hPure

end AffineColoring
end BeyondSperner
