import BeyondSperner.Euclidean.Intersection.Stokes

/-!
# The intersection-number proof of Lemma 10.7

This file follows the forward proof in Section 10 of Ivanov's *Beyond
Sperner's Lemma*.  It is intentionally independent of Theorem 10.8 and of the
alternate covering proof in `AffineEnvelope`.

The proof makes all four steps of the paper explicit:

1. the envelope equation gives `∂ E[[I]] = ∂ I`;
2. normalized pushforward commutes with boundary, so the sum of the pushed
   envelope chain and the reference simplex is a cycle;
3. Corollary 10.6 forces their point-intersection numbers to agree; and
4. a nonzero finite sum supplies an actual top envelope simplex containing
   the point after applying the prescribed vertex map.
-/

namespace BeyondSperner
namespace EuclideanIntersection

open Classical Set
open SimplexFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Every simplex in a top chain has the dimension determined by the index
set.  No purity statement about the underlying complex is needed. -/
theorem isMChain_topChain_of_card
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (D : SimplexFamily I V) (A : Finset I) (m : ℕ)
    (hcard : A.card = m + 1) : IsMChain m (D.topChain A) := by
  intro sigma hsigma
  rw [Finsupp.mem_support_iff, SimplexFamily.topChain_apply] at hsigma
  split at hsigma
  · next h => exact h.2.trans hcard
  · simp at hsigma

omit [FiniteDimensional ℝ E] in
/-- Chainwise point general position is preserved when chains are added. -/
theorem PointInGeneralPositionWithChain.add
    {c d : Chain E} {z : E}
    (hc : PointInGeneralPositionWithChain c z)
    (hd : PointInGeneralPositionWithChain d z) :
    PointInGeneralPositionWithChain (c + d) z := by
  intro sigma hsigma
  have hsigma' : sigma ∈ c.support ∪ d.support := Finsupp.support_add hsigma
  rcases Finset.mem_union.mp hsigma' with hsigma | hsigma
  · exact hc sigma hsigma
  · exact hd sigma hsigma

omit [FiniteDimensional ℝ E] in
/-- A point is in general position with a singleton chain exactly as required
once it is in general position with its one supporting simplex. -/
theorem pointInGeneralPositionWithChain_singleton
    (sigma : Finset E) (z : E) (hz : PointInGeneralPosition sigma z) :
    PointInGeneralPositionWithChain (singletonChain sigma) z := by
  intro tau htau
  have htauEq : tau = sigma := by
    simpa [singletonChain] using htau
  subst tau
  exact hz

omit [FiniteDimensional ℝ E] in
/-- The image of the formal index simplex is the reference affine-basis
simplex. -/
theorem image_indexSimplex_univ
    {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (b : AffineBasis I ℝ E) (φ : V ⊕ I → E)
    (hφindex : ∀ i, φ (Sum.inr i) = b i) :
    (Envelope.indexSimplex (V := V) (Finset.univ : Finset I)).image φ =
      Finset.univ.image b := by
  ext x
  simp [Envelope.indexSimplex, hφindex]

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- The prescribed map is injective on the formal reference simplex because
an affine basis is injectively indexed. -/
theorem injOn_indexSimplex_univ
    {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (b : AffineBasis I ℝ E) (φ : V ⊕ I → E)
    (hφindex : ∀ i, φ (Sum.inr i) = b i) :
    Set.InjOn φ (Envelope.indexSimplex (V := V) (Finset.univ : Finset I)) := by
  intro x hx y hy hxy
  rw [Envelope.indexSimplex] at hx hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  rw [hφindex i, hφindex j] at hxy
  rw [b.ind.injective hxy]

omit [FiniteDimensional ℝ E] in
/-- The finite set underlying an affine basis is its range. -/
theorem coe_univ_image_affineBasis
    {I : Type*} [Fintype I] [DecidableEq I]
    (b : AffineBasis I ℝ E) :
    ((Finset.univ.image b : Finset E) : Set E) = Set.range b := by
  ext x
  simp

/-- Lemma 10.7, proved by the paper's intersection-number route.

The two general-position hypotheses are precisely the paper's condition that
`z` be in general position with respect to the pushed envelope chain and the
reference simplex.  The conclusion is stated on the literal envelope
complex, with the exact cardinality and convex-hull witness needed later. -/
theorem lemma10_7_intersection
    {I V : Type*} [Fintype I] [Fintype V] [Nonempty I]
    [DecidableEq I] [DecidableEq V]
    (D : SimplexFamily I V)
    (b : AffineBasis I ℝ E)
    (z : E) (hz : z ∈ convexHull ℝ (Set.range b))
    (hchain : D.IsChainSimplex)
    (φ : V ⊕ I → E)
    (hφindex : ∀ i, φ (Sum.inr i) = b i)
    (hzMapped : PointInGeneralPositionWithChain
      (normalizedMapChainHom φ
        ((Envelope.family D).topChain (Finset.univ : Finset I))) z)
    (hzReference : PointInGeneralPosition
      (Finset.univ.image b : Finset E) z) :
    ∃ rho : Finset (V ⊕ I),
      rho ∈ Envelope.complex D Finset.univ ∧
      rho.card = Fintype.card I ∧
      z ∈ convexHull ℝ (rho.image φ : Set E) := by
  let n := Module.finrank ℝ E
  let envelopeChain : Chain (V ⊕ I) :=
    (Envelope.family D).topChain (Finset.univ : Finset I)
  let mappedChain : Chain E := normalizedMapChainHom φ envelopeChain
  let referenceSimplex : Finset E := Finset.univ.image b
  let referenceChain : Chain E := singletonChain referenceSimplex
  let pointChain : Chain E := singletonChain {z}

  have hindexImage :
      (Envelope.indexSimplex (V := V) (Finset.univ : Finset I)).image φ =
        referenceSimplex := by
    simpa [referenceSimplex] using image_indexSimplex_univ b φ hφindex
  have hindexInj :
      Set.InjOn φ
        (Envelope.indexSimplex (V := V) (Finset.univ : Finset I)) :=
    injOn_indexSimplex_univ b φ hφindex

  have henvelopeBoundary :
      boundary envelopeChain =
        boundary (singletonChain
          (Envelope.indexSimplex (V := V) (Finset.univ : Finset I))) := by
    calc
      boundary envelopeChain =
          (Envelope.family D).boundaryIndexChain Finset.univ := by
            exact (Envelope.chain_family hchain) Finset.univ
      _ = boundary (singletonChain
          (Envelope.indexSimplex (V := V) Finset.univ)) :=
            Envelope.boundaryIndexChain_univ_eq_boundary_indexSimplex D

  have hmappedBoundary : boundary mappedChain = boundary referenceChain := by
    calc
      boundary mappedChain = normalizedMapChainHom φ (boundary envelopeChain) := by
        exact (normalizedMapChainHom_boundary φ envelopeChain).symm
      _ = normalizedMapChainHom φ
          (boundary (singletonChain
            (Envelope.indexSimplex (V := V) (Finset.univ : Finset I)))) := by
        rw [henvelopeBoundary]
      _ = boundary (normalizedMapChainHom φ
          (singletonChain
            (Envelope.indexSimplex (V := V) (Finset.univ : Finset I)))) := by
        exact normalizedMapChainHom_boundary φ _
      _ = boundary (singletonChain
          ((Envelope.indexSimplex (V := V)
            (Finset.univ : Finset I)).image φ)) := by
        rw [normalizedMapChainHom_singleton,
          normalizedMapSimplex_eq_of_injOn φ _ hindexInj]
      _ = boundary referenceChain := by rw [hindexImage]

  have hcycle : boundary (mappedChain + referenceChain) = 0 := by
    rw [boundary_add, hmappedBoundary]
    ext sigma
    exact CharTwo.add_self_eq_zero ((boundary referenceChain) sigma)

  have hindexCard : (Finset.univ : Finset I).card = n + 1 := by
    simpa [n] using b.card_eq_finrank_add_one
  have henvelopeM : IsMChain n envelopeChain := by
    exact isMChain_topChain_of_card (Envelope.family D)
      (Finset.univ : Finset I) n hindexCard
  have hmappedM : IsMChain n mappedChain := by
    exact henvelopeM.normalizedMapChainHom n φ envelopeChain
  have hreferenceM : IsMChain n referenceChain := by
    apply (isMChain_singletonChain n referenceSimplex).2
    rw [IsMSimplex]
    change (Finset.univ.image b).card = n + 1
    rw [Finset.card_image_of_injective Finset.univ b.ind.injective]
    exact hindexCard
  have htotalM : IsMChain n (mappedChain + referenceChain) :=
    hmappedM.add hreferenceM

  have hreferenceGP : PointInGeneralPositionWithChain referenceChain z := by
    exact pointInGeneralPositionWithChain_singleton referenceSimplex z hzReference
  have htotalGP :
      PointInGeneralPositionWithChain (mappedChain + referenceChain) z := by
    exact hzMapped.add hreferenceGP

  have htotalIntersection :
      pointChainIntersection (mappedChain + referenceChain) pointChain = 0 := by
    exact corollary10_6 n (mappedChain + referenceChain) rfl htotalM hcycle z htotalGP

  have hzReferenceRealization : z ∈ realization referenceSimplex := by
    simpa [realization, referenceSimplex, coe_univ_image_affineBasis] using hz
  have hreferenceIntersection :
      pointChainIntersection referenceChain pointChain = 1 := by
    change pointChainIntersection (singletonChain referenceSimplex)
      (singletonChain {z}) = 1
    rw [pointChainIntersection_singleton]
    exact (pointIntersectionNumber_eq_one_iff referenceSimplex z).2
      hzReferenceRealization
  have hmappedIntersection :
      pointChainIntersection mappedChain pointChain = 1 := by
    rw [pointChainIntersection, chainPairing_add_left] at htotalIntersection
    have hneg := eq_neg_of_add_eq_zero_left htotalIntersection
    have hreferenceIntersection' :
        chainPairing pointSimplexIntersectionNumber referenceChain pointChain = 1 :=
      hreferenceIntersection
    rw [hreferenceIntersection'] at hneg
    change chainPairing pointSimplexIntersectionNumber mappedChain pointChain = 1
    simpa using hneg

  have hmappedExpansion :
      pointChainIntersection mappedChain pointChain =
        ∑ rho ∈ ((Envelope.family D).complex Finset.univ).topSimplices
            (Finset.univ : Finset I).card,
          pointChainIntersection (normalizedMapSimplex φ rho) pointChain := by
    simp [mappedChain, envelopeChain, SimplexFamily.topChain,
      pointChainIntersection, chainPairing_finsetSum_left]
  have hsumNonzero :
      (∑ rho ∈ ((Envelope.family D).complex Finset.univ).topSimplices
          (Finset.univ : Finset I).card,
        pointChainIntersection (normalizedMapSimplex φ rho) pointChain) ≠ 0 := by
    rw [← hmappedExpansion, hmappedIntersection]
    norm_num
  obtain ⟨rho, hrhoTop, hrhoIntersection⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hsumNonzero

  have hrhoInj : Set.InjOn φ rho := by
    by_contra hnot
    rw [normalizedMapSimplex_eq_zero_of_not_injOn φ rho hnot,
      pointChainIntersection, chainPairing_zero_left] at hrhoIntersection
    exact hrhoIntersection rfl
  have hzRho : z ∈ realization (rho.image φ) := by
    by_contra hnot
    rw [normalizedMapSimplex_eq_of_injOn φ rho hrhoInj,
      show pointChain = singletonChain {z} from rfl,
      pointChainIntersection_singleton,
      (pointIntersectionNumber_eq_zero_iff (rho.image φ) z).2 hnot] at hrhoIntersection
    exact hrhoIntersection rfl

  have hrhoData := Finset.mem_filter.mp hrhoTop
  refine ⟨rho, ?_, ?_, ?_⟩
  · exact (FiniteSimplicialComplex.mem_simplices_iff
      (Envelope.complex D Finset.univ) rho).mp hrhoData.1
  · simpa using hrhoData.2
  · simpa [realization] using hzRho

end EuclideanIntersection
end BeyondSperner
