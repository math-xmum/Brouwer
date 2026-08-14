import BeyondSperner.Coloring.AffineEnvelope
import BeyondSperner.Euclidean.Intersection.AffineColoring

/-!
# Compatibility interface for the intersection proof of Theorem 10.8

The mathematical proof remains in the `BeyondSperner` module tree.  This
file is deliberately outside that tree: it converts the envelope conclusion
of `EuclideanIntersection.theorem10_8_envelope_intersection` into the public
`AffineColoring.IsAffineSolution` interface used by the pre-existing
oriented-matroid proof.

The theorem below does not invoke `AffineColoring.theorem10_8`; it reaches the
same conclusion through Lemma 10.7, general-position density, and the closed
finite-union argument from the paper.
-/

namespace BeyondSperner
namespace AffineColoring

open Classical Set

variable {I V P : Type*} [Fintype I] [Fintype V]
  [DecidableEq I] [DecidableEq V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The paper's intersection-number route to exactly the existing
`IsAffineSolution` conclusion of Theorem 10.8. -/
theorem theorem10_8_via_intersection
    (D : SimplexFamily I V)
    (b : AffineBasis I ℝ P) (c : D.Vertex → P) (z : P)
    (hz : z ∈ convexHull ℝ (Set.range b))
    (hchain : D.IsChainSimplex) :
    ∃ C : Finset I, ∃ tau : Finset V,
      IsAffineSolution D b c z C tau := by
  classical
  let _ : Nonempty I := Fintype.card_pos_iff.mp (by
    rw [b.card_eq_finrank_add_one]
    omega)
  let i₀ : I := Classical.choice inferInstance
  let φ : V ⊕ I → P := fun x ↦
    match x with
    | Sum.inl v => if hv : v ∈ D.vertexSet then c ⟨v, hv⟩ else b i₀
    | Sum.inr i => b i
  have hφold : ∀ v : D.Vertex, φ (Sum.inl v.1) = c v := by
    intro v
    simp [φ, v.property]
  have hφindex : ∀ i, φ (Sum.inr i) = b i := by
    intro i
    rfl
  obtain ⟨rho, hrhoComplex, hrhoCard, hrhoImageCard,
      hrhoGeneric, hzRho⟩ :=
    EuclideanIntersection.theorem10_8_envelope_intersection
      D b φ hφindex hchain z hz
  have hrhoTop :
      rho ∈ Envelope.complex D Finset.univ ∧
        rho.card = (Finset.univ : Finset I).card := by
    exact ⟨hrhoComplex, by simpa using hrhoCard⟩
  obtain ⟨C, hC, htop, hindex⟩ :=
    (Envelope.isTopSimplex_univ_iff D rho).mp hrhoTop
  let tau : Finset V := Envelope.oldPart rho
  have htau : tau ∈ D.complex C := htop.1
  have htauCard : tau.card = C.card := htop.2
  have himage :
      rho.image φ = affineCompletedPointFormula D b c C tau htau := by
    calc
      rho.image φ =
          (Envelope.oldSimplex tau ∪
            Envelope.indexSimplex (Finset.univ \ C)).image φ := by
        congr 1
        rw [Envelope.old_index_decomposition rho, hindex]
      _ = affineCompletedPointFormula D b c C tau htau :=
        image_envelopeSimplex_eq_affineCompletedPointFormula
          D b c C tau htau φ hφold hφindex
  refine ⟨C, tau, htau, hC, htauCard, ?_⟩
  dsimp only
  rw [← himage]
  exact ⟨hrhoImageCard, hzRho, hrhoGeneric⟩

end AffineColoring
end BeyondSperner
