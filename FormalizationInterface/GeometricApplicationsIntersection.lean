import BeyondSperner.Geometry.Triangulation.Applications
import FormalizationInterface.Theorem10_9Intersection
import FormalizationInterface.Theorem10_10Intersection

/-!
# Arbitrary geometric triangulations through the intersection route

These wrappers instantiate the already proved geometric triangulation
obligations with the paper-route versions of Theorems 10.9 and 10.10.  They
have the same mathematical conclusions as `geometric_theorem10_9` and
`geometric_theorem10_10`, but their Theorem 10.8 dependency is the independent
intersection/general-position proof.
-/

namespace BeyondSperner
namespace GeometricTriangulation

open Classical Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ E)
variable (T : Data b)

/-- Theorem 10.9 for an arbitrary finite geometric triangulation, routed
through the paper's intersection proof of Theorem 10.8. -/
theorem geometric_theorem10_9_via_intersection
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
  let _ : FiniteDimensional ℝ E := b.finiteDimensional
  exact AffineColoring.theorem10_9_via_intersection (family b T) b
    (fun v ↦ v.1.1) c ((isNonbranching b T).isChainSimplex b T)
    (family_face_coordinate b T) hhedgehog z hz

/-- Theorem 10.10 for an arbitrary finite geometric triangulation, routed
through the paper's intersection proof of Theorem 10.8. -/
theorem geometric_theorem10_10_via_intersection
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
  let _ : FiniteDimensional ℝ E := b.finiteDimensional
  have hPure :
      ((family b T).complex Finset.univ).IsPureOfCardinality
        (Fintype.card (Fin (n + 1))) := by
    simpa using family_full_isPure_of_data b T
  obtain ⟨sigma, hsigma, hcard, hzero⟩ :=
    AffineColoring.theorem10_10_via_intersection (family b T) b hb
      (fun v ↦ v.1.1) c ((isNonbranching b T).isChainSimplex b T)
      (family_face_coordinate b T) hinward
      (family_subset_full b T) hPure
  refine ⟨sigma, hsigma, ?_, hzero⟩
  simpa using hcard

end GeometricTriangulation
end BeyondSperner
