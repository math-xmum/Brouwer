import BeyondSperner.Coloring.Affine
import BeyondSperner.Simplicial.ChainSimplex

/-!
# Affine realization of an envelope simplex

This file gives a literal envelope-complex form of the covering conclusion
appearing in Lemma 10.7 of Ivanov's paper.  The conclusion is obtained here
from the independently formalized Theorem 10.8, so this module supplies an
alternate proof that needs no general-position hypothesis.  The paper's
forward intersection-number proof and its general-position limit to Theorem
10.8 are checked independently in `EuclideanIntersectionLemma10_7` and
`EuclideanIntersectionTheorem10_8`.
-/

namespace BeyondSperner
namespace AffineColoring

open Classical Set

variable {I V P : Type*} [Fintype I]
  [DecidableEq I] [DecidableEq V]
  [AddCommGroup P] [Module ℝ P]

/-- If a map on the vertices of the envelope agrees with the prescribed old
colors and affine-basis vertices, then its image on the envelope simplex
associated with `(C, tau)` is exactly formula (40). -/
theorem image_envelopeSimplex_eq_affineCompletedPointFormula
    (D : SimplexFamily I V)
    (b : AffineBasis I ℝ P) (c : D.Vertex → P)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C)
    (φ : V ⊕ I → P)
    (hφold : ∀ v : D.Vertex, φ (Sum.inl v.1) = c v)
    (hφindex : ∀ i, φ (Sum.inr i) = b i) :
    (Envelope.oldSimplex tau ∪
        Envelope.indexSimplex (Finset.univ \ C)).image φ =
      affineCompletedPointFormula D b c C tau htau := by
  have hold : (Envelope.oldSimplex (I := I) tau).image φ =
      tau.attach.image (fun v ↦
        c ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩) := by
    ext p
    constructor
    · intro hp
      obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_image.mpr
      refine ⟨⟨v, hv⟩, by simp, ?_⟩
      exact (hφold
        ⟨v, MatroidColoring.mem_vertexSet_of_mem_simplex D htau hv⟩).symm.trans hxp
    · intro hp
      obtain ⟨v, hv, hvp⟩ := Finset.mem_image.mp hp
      refine Finset.mem_image.mpr ⟨Sum.inl v.1, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩
      · exact (hφold
          ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩).trans hvp
  have hindex :
      (Envelope.indexSimplex (V := V) (Finset.univ \ C)).image φ =
        (Finset.univ \ C).image b := by
    rw [Envelope.indexSimplex, Finset.image_image]
    apply Finset.image_congr
    intro i hi
    exact hφindex i
  rw [Finset.image_union, hold, hindex]
  rfl

section Cover

variable [Fintype V] [Nonempty I]

/-- The covering conclusion of Lemma 10.7, stated on the literal envelope
complex.  This version is stronger than the paper's stated lemma because it
requires no general-position assumption.  Its proof uses Theorem 10.8 rather
than the paper's intersection-number route. -/
theorem lemma10_7_envelope_of_theorem10_8
    (D : SimplexFamily I V)
    (b : AffineBasis I ℝ P) (c : D.Vertex → P) (z : P)
    (hz : z ∈ convexHull ℝ (Set.range b))
    (hchain : D.IsChainSimplex)
    (φ : V ⊕ I → P)
    (hφold : ∀ v : D.Vertex, φ (Sum.inl v.1) = c v)
    (hφindex : ∀ i, φ (Sum.inr i) = b i) :
    ∃ rho : Finset (V ⊕ I),
      rho ∈ Envelope.complex D Finset.univ ∧
      rho.card = Fintype.card I ∧
      z ∈ convexHull ℝ (rho.image φ : Set P) := by
  obtain ⟨C, tau, hsol⟩ := theorem10_8 D b c z hz hchain
  rcases hsol with ⟨htau, hC, htauCard, hdata⟩
  dsimp only at hdata
  rcases hdata with ⟨_hPointCard, hzCompleted, _hAffineIndependent⟩
  let rho : Finset (V ⊕ I) :=
    Envelope.oldSimplex tau ∪
      Envelope.indexSimplex (Finset.univ \ C)
  have hrhoTop :
      rho ∈ Envelope.complex D Finset.univ ∧
        rho.card = (Finset.univ : Finset I).card := by
    apply (Envelope.isTopSimplex_univ_iff D rho).mpr
    refine ⟨C, hC, ?_, ?_⟩
    · simpa [rho] using (show D.IsTopSimplex C tau from ⟨htau, htauCard⟩)
    · simp [rho]
  refine ⟨rho, hrhoTop.1, ?_, ?_⟩
  · simpa using hrhoTop.2
  · rw [image_envelopeSimplex_eq_affineCompletedPointFormula
      D b c C tau htau φ hφold hφindex]
    exact hzCompleted

end Cover

end AffineColoring
end BeyondSperner
