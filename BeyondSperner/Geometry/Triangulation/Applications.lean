import BeyondSperner.Geometry.Triangulation.Nonbranching
import BeyondSperner.Coloring.InwardTangent

/-!
# Section 10 for an arbitrary finite geometric triangulation

This module instantiates Theorems 10.9 and 10.10 on the face family induced
by a finite geometric triangulation.  Face-coordinate compatibility,
ambient inclusion, purity, and local nonbranching are all proved from the
geometric data.
-/

namespace BeyondSperner

open Classical Set

namespace GeometricTriangulation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ E)
variable (T : Data b)

/-- Theorem 10.9 for an arbitrary finite geometric triangulation. -/
theorem geometric_theorem10_9
    (c : (family b T).Vertex → E)
    (hhedgehog : AffineColoring.IsVectorHedgehogColoring
      (family b T) b (fun v ↦ v.1.1) c)
    (z : E) (hz : z ∈ convexHull ℝ (Set.range b)) :
    ∃ sigma : Finset T.Vertex,
      ∃ hsigma : sigma ∈ (family b T).complex Finset.univ,
        sigma.card = n + 1 ∧
          z ∈ convexHull ℝ
            (AffineColoring.affineSimplexColorPoints
              (family b T) c Finset.univ sigma hsigma : Set E) := by
  exact AffineColoring.theorem10_9 (family b T) b
    (fun v ↦ v.1.1) c ((isNonbranching b T).isChainSimplex b T)
    (family_face_coordinate b T) hhedgehog z hz

/-- Theorem 10.10 for an arbitrary finite geometric triangulation.  The
top-simplex extension is supplied by the automatic purity theorem, rather
than by a purity parameter. -/
theorem geometric_theorem10_10
    (hb : AffineColoring.IsCenteredAffineBasis b)
    (c : (family b T).Vertex → E)
    (hinward : AffineColoring.IsInwardTangentColoring
      (family b T) b (fun v ↦ v.1.1) c) :
    ∃ sigma : Finset T.Vertex,
      ∃ hsigma : sigma ∈ (family b T).complex Finset.univ,
        sigma.card = n + 1 ∧
          (0 : E) ∈ convexHull ℝ
          (AffineColoring.affineSimplexColorPoints
              (family b T) c Finset.univ sigma hsigma : Set E) := by
  have hPure :
      ((family b T).complex Finset.univ).IsPureOfCardinality
        (Fintype.card (Fin (n + 1))) := by
    simpa using family_full_isPure_of_data b T
  obtain ⟨sigma, hsigma, hcard, hzero⟩ :=
    AffineColoring.theorem10_10 (family b T) b hb
      (fun v ↦ v.1.1) c ((isNonbranching b T).isChainSimplex b T)
      (family_face_coordinate b T) hinward
      (family_subset_full b T) hPure
  refine ⟨sigma, hsigma, ?_, hzero⟩
  simpa using hcard

end GeometricTriangulation
end BeyondSperner
