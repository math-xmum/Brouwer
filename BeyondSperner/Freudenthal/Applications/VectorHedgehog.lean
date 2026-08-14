import BeyondSperner.Coloring.VectorHedgehog
import BeyondSperner.Freudenthal.Applications.InwardTangent

/-!
# Theorem 10.9 on the Freudenthal--Scarf triangulation

This file instantiates the vector-hedgehog theorem using the normalized
affine realization of positive-scale integer-simplex vertices.  Lemma 4.7
supplies the only geometric face obligation required by the abstract
Theorem 10.9.
-/

namespace BeyondSperner

open Classical Set

namespace IntegerSimplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full vector-hedgehog theorem for the concrete positive-scale
Freudenthal--Scarf triangulation. -/
theorem freudenthal_theorem10_9
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
  let D := (pointOrders N n).associatedFamily
  let p : D.Vertex → E := fun v ↦ affinePointPosition b v.1
  have hface : ∀ (C : Finset (Fin (n + 1)))
      (tau : Finset (Point N n)) (htau : tau ∈ D.complex C)
      (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0 := by
    intro C tau htau v hv i hi
    exact coord_affinePointPosition_eq_zero_of_mem_associatedComplex
      hN b htau hv (Finset.mem_sdiff.mp hi).2
  exact AffineColoring.theorem10_9 D b p c
    (pointOrders N n).associatedFamily_isChainSimplex
    hface hhedgehog z hz

end IntegerSimplex
end BeyondSperner
