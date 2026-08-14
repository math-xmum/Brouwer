import BeyondSperner.Freudenthal.Applications.VectorHedgehog
import FormalizationInterface.Theorem10_9Intersection
import FormalizationInterface.Theorem10_10Intersection

/-!
# Freudenthal--Scarf applications through the intersection route

This module reuses the concrete face, ambient-inclusion, and purity proofs of
the Freudenthal--Scarf complex while selecting the independent paper-route
proof of Theorem 10.8.
-/

namespace BeyondSperner
namespace IntegerSimplex

open Classical Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The concrete positive-scale Theorem 10.9 through the intersection proof
of Theorem 10.8. -/
theorem freudenthal_theorem10_9_via_intersection
    {N n : ℕ} (hN : 0 < N)
    (b : AffineBasis (Fin (n + 1)) ℝ E)
    (c : ((pointOrders N n).associatedFamily).Vertex → E)
    (hhedgehog : AffineColoring.IsVectorHedgehogColoring
      ((pointOrders N n).associatedFamily) b
      (fun v ↦ affinePointPosition b v.1) c)
    (z : E) (hz : z ∈ convexHull ℝ (Set.range b)) :
    ∃ sigma : Finset (Point N n),
      ∃ hsigma : sigma ∈
          ((pointOrders N n).associatedFamily).complex Finset.univ,
        sigma.card = n + 1 ∧
          z ∈ convexHull ℝ
            (AffineColoring.affineSimplexColorPoints
              ((pointOrders N n).associatedFamily) c Finset.univ sigma hsigma :
                Set E) := by
  let _ : FiniteDimensional ℝ E := b.finiteDimensional
  let D := (pointOrders N n).associatedFamily
  let p : D.Vertex → E := fun v ↦ affinePointPosition b v.1
  have hface : ∀ (C : Finset (Fin (n + 1)))
      (tau : Finset (Point N n)) (_htau : tau ∈ D.complex C)
      (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0 := by
    intro C tau htau v hv i hi
    exact coord_affinePointPosition_eq_zero_of_mem_associatedComplex
      hN b htau hv (Finset.mem_sdiff.mp hi).2
  exact AffineColoring.theorem10_9_via_intersection D b p c
    (pointOrders N n).associatedFamily_isChainSimplex
    hface hhedgehog z hz

/-- The concrete positive-scale Theorem 10.10 through the intersection proof
of Theorem 10.8. -/
theorem freudenthal_theorem10_10_via_intersection
    {N n : ℕ} (hN : 0 < N)
    (b : AffineBasis (Fin (n + 1)) ℝ E)
    (hb : AffineColoring.IsCenteredAffineBasis b)
    (c : ((pointOrders N n).associatedFamily).Vertex → E)
    (hinward : AffineColoring.IsInwardTangentColoring
      ((pointOrders N n).associatedFamily) b
      (fun v ↦ affinePointPosition b v.1) c) :
    ∃ sigma : Finset (Point N n),
      ∃ hsigma : sigma ∈
          ((pointOrders N n).associatedFamily).complex Finset.univ,
        sigma.card = n + 1 ∧
          (0 : E) ∈ convexHull ℝ
            (AffineColoring.affineSimplexColorPoints
              ((pointOrders N n).associatedFamily) c Finset.univ sigma hsigma :
                Set E) := by
  let _ : FiniteDimensional ℝ E := b.finiteDimensional
  let D := (pointOrders N n).associatedFamily
  let p : D.Vertex → E := fun v ↦ affinePointPosition b v.1
  have hface : ∀ (C : Finset (Fin (n + 1)))
      (tau : Finset (Point N n)) (_htau : tau ∈ D.complex C)
      (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0 := by
    intro C tau htau v hv i hi
    exact coord_affinePointPosition_eq_zero_of_mem_associatedComplex
      hN b htau hv (Finset.mem_sdiff.mp hi).2
  have hAmbient : ∀ (C : Finset (Fin (n + 1)))
      (tau : Finset (Point N n)), tau ∈ D.complex C →
        tau ∈ D.complex Finset.univ := by
    intro C tau htau
    exact associatedComplex_subset_full_of_pos hN C htau
  have hPure :
      (D.complex Finset.univ).IsPureOfCardinality
        (Fintype.card (Fin (n + 1))) := by
    change FiniteSimplicialComplex.IsPureOfCardinality
      ((pointOrders N n).associatedComplex Finset.univ)
      (Fintype.card (Fin (n + 1)))
    simpa using associatedComplex_isPureOfCardinality_of_pos
      (N := N) (n := n) hN
  obtain ⟨sigma, hsigma, hcard, hzero⟩ :=
    AffineColoring.theorem10_10_via_intersection D b hb p c
      (pointOrders N n).associatedFamily_isChainSimplex
      hface hinward hAmbient hPure
  refine ⟨sigma, hsigma, ?_, hzero⟩
  simpa using hcard

end IntegerSimplex
end BeyondSperner
