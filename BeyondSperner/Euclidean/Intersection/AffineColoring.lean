import BeyondSperner.Euclidean.Intersection.EnvelopeCoverage

/-!
# The intersection-number proof of Theorem 10.8: envelope form

This file formalizes the general-position and limiting argument on page 54
of Ivanov's *Beyond Sperner's Lemma*.  It is independent of the oriented-
matroid proof of Theorem 10.8 in `AffineColoring`.

Instead of choosing an explicit sequence and then a constant subsequence, we
use the equivalent finite-closed-union argument.  Points avoiding the affine
spans of all small subsets of the finite vertex image are dense.  Lemma 10.7
puts every such point in the image hull of a generic top envelope simplex
whose image still has all `n + 1` vertices.  The union of these finitely many
hulls is closed, so it contains the closure of the interior of the reference
simplex, hence the whole reference simplex.
-/

namespace BeyondSperner
namespace EuclideanIntersection

open Classical Set
open SimplexFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- The finite union of affine spans of subsets of `S` having at most `n`
points.  Its complement is the strong general-position set used in the
paper's proof of Theorem 10.8. -/
noncomputable def smallAffineSpanLocus (S : Finset E) (n : ℕ) : Set E :=
  ⋃ t ∈ S.powerset.filter (fun t ↦ t.card ≤ n),
    (affineSpan ℝ (t : Set E) : Set E)

/-- A point avoids every affine combination of at most `n` points of `S`. -/
def AvoidsSmallAffineSpans (S : Finset E) (n : ℕ) (z : E) : Prop :=
  z ∉ smallAffineSpanLocus S n

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- When `n` is the ambient dimension, the locus of affine combinations of
at most `n` points from a finite set has empty interior. -/
theorem interior_smallAffineSpanLocus_eq_empty
    (S : Finset E) (n : ℕ) (hn : n = Module.finrank ℝ E) :
    interior (smallAffineSpanLocus S n) = ∅ := by
  rw [smallAffineSpanLocus]
  apply interior_iUnion_affineSpan_eq_empty_of_card_le_finrank
  intro t ht
  have ht' := (Finset.mem_filter.mp ht).2
  simpa [hn] using ht'

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- The small-affine-span obstacle locus is a finite union of closed affine
subspaces. -/
theorem isClosed_smallAffineSpanLocus (S : Finset E) (n : ℕ) :
    IsClosed (smallAffineSpanLocus S n) := by
  rw [smallAffineSpanLocus]
  apply isClosed_biUnion_finset
  intro t ht
  let _ : FiniteDimensional ℝ (affineSpan ℝ (t : Set E)).direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ t.finite_toSet
  exact AffineSubspace.closed_of_finiteDimensional _

omit [FiniteDimensional ℝ E] in
/-- Avoiding all small affine spans implies the paper's exact point general-
position condition for every `n`-simplex contained in the finite point set. -/
theorem pointInGeneralPosition_of_avoidsSmallAffineSpans
    (S sigma : Finset E) (n : ℕ) (z : E)
    (hz : AvoidsSmallAffineSpans S n z)
    (hsub : sigma ⊆ S) (hcard : IsMSimplex n sigma) :
    PointInGeneralPosition sigma z := by
  intro v hv hzFace
  apply hz
  rw [smallAffineSpanLocus]
  apply Set.mem_iUnion.mpr
  refine ⟨sigma.erase v, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr
      ((Finset.erase_subset v sigma).trans hsub), ?_⟩
    have hsigmaCard : sigma.card = n + 1 := hcard
    rw [Finset.card_erase_of_mem hv, hsigmaCard]
    omega
  · exact convexHull_subset_affineSpan _ hzFace

/-- Theorem 10.8 in its intermediate envelope form, proved along the paper's
intersection-number route.

For every point in the reference simplex, a top envelope simplex has a
generic, full-cardinality image containing that point in its convex hull.
Both source and image cardinality are recorded: source cardinality permits
the envelope classification, while image cardinality rules out collapsed
vertices and is required by formula (40). -/
theorem theorem10_8_envelope_intersection
    {I V : Type*} [Fintype I] [Fintype V] [Nonempty I]
    [DecidableEq I] [DecidableEq V]
    (D : SimplexFamily I V)
    (b : AffineBasis I ℝ E)
    (φ : V ⊕ I → E)
    (hφindex : ∀ i, φ (Sum.inr i) = b i)
    (hchain : D.IsChainSimplex)
    (z : E) (hz : z ∈ convexHull ℝ (Set.range b)) :
    ∃ rho : Finset (V ⊕ I),
      rho ∈ Envelope.complex D Finset.univ ∧
      rho.card = Fintype.card I ∧
      (rho.image φ).card = Fintype.card I ∧
      IsGeneric (rho.image φ) ∧
      z ∈ convexHull ℝ (rho.image φ : Set E) := by
  let n := Module.finrank ℝ E
  let pointSet : Finset E := (Finset.univ : Finset (V ⊕ I)).image φ
  let envelopeChain : Chain (V ⊕ I) :=
    (Envelope.family D).topChain (Finset.univ : Finset I)
  let mappedChain : Chain E := normalizedMapChainHom φ envelopeChain
  let referenceSimplex : Finset E := Finset.univ.image b
  let topSimplices : Finset (Finset (V ⊕ I)) :=
    (Envelope.complex D Finset.univ).topSimplices
      (Finset.univ : Finset I).card
  let fullGenericTopSimplices : Finset (Finset (V ⊕ I)) :=
    topSimplices.filter (fun rho ↦
      (rho.image φ).card = Fintype.card I ∧ IsGeneric (rho.image φ))
  let covered : Set E :=
    ⋃ rho ∈ fullGenericTopSimplices, realization (rho.image φ)
  let Gamma : Set E := convexHull ℝ (Set.range b)

  have hindexCard : (Finset.univ : Finset I).card = n + 1 := by
    simpa [n] using b.card_eq_finrank_add_one
  have henvelopeM : IsMChain n envelopeChain := by
    exact isMChain_topChain_of_card (Envelope.family D)
      (Finset.univ : Finset I) n hindexCard
  have hmappedM : IsMChain n mappedChain := by
    exact henvelopeM.normalizedMapChainHom n φ envelopeChain
  have hreferenceCard : IsMSimplex n referenceSimplex := by
    rw [IsMSimplex]
    change (Finset.univ.image b).card = n + 1
    rw [Finset.card_image_of_injective Finset.univ b.ind.injective]
    exact hindexCard
  have hreferenceSubset : referenceSimplex ⊆ pointSet := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨Sum.inr i, Finset.mem_univ _, ?_⟩
    exact hφindex i
  have hcoveredClosed : IsClosed covered := by
    simp only [covered]
    apply isClosed_biUnion_finset
    intro rho hrho
    exact (rho.image φ).finite_toSet.isClosed_convexHull ℝ

  have hgoodInteriorSubset :
      interior Gamma ∩ (smallAffineSpanLocus pointSet n)ᶜ ⊆ covered := by
    intro q hq
    have hqGamma : q ∈ convexHull ℝ (Set.range b) := interior_subset hq.1
    have hqAvoid : AvoidsSmallAffineSpans pointSet n q := hq.2
    have hqReference : PointInGeneralPosition referenceSimplex q :=
      pointInGeneralPosition_of_avoidsSmallAffineSpans
        pointSet referenceSimplex n q hqAvoid hreferenceSubset hreferenceCard
    have hqMapped : PointInGeneralPositionWithChain mappedChain q := by
      intro sigma hsigma
      apply pointInGeneralPosition_of_avoidsSmallAffineSpans
        pointSet sigma n q hqAvoid
      · exact normalizedMapChainHom_support_subset_image_univ
          φ envelopeChain hsigma
      · exact hmappedM sigma hsigma
    obtain ⟨rho, hrhoComplex, hrhoCard, hqRho⟩ :=
      lemma10_7_intersection D b q hqGamma hchain φ hφindex
        hqMapped hqReference
    have hrhoTop : rho ∈ topSimplices := by
      apply Finset.mem_filter.mpr
      refine ⟨(FiniteSimplicialComplex.mem_simplices_iff
        (Envelope.complex D Finset.univ) rho).mpr hrhoComplex, ?_⟩
      simpa using hrhoCard
    have hrhoImageSubset : rho.image φ ⊆ pointSet :=
      Finset.image_mono φ (Finset.subset_univ rho)
    have hrhoImageCard : (rho.image φ).card = n + 1 := by
      have hle : (rho.image φ).card ≤ rho.card := Finset.card_image_le
      have hnotle : ¬(rho.image φ).card ≤ n := by
        intro hsmall
        apply hqAvoid
        rw [smallAffineSpanLocus]
        apply Set.mem_iUnion.mpr
        refine ⟨rho.image φ, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr hrhoImageSubset, hsmall⟩
        · exact convexHull_subset_affineSpan _ hqRho
      have hrhoCard' : rho.card = n + 1 := by
        rw [hrhoCard]
        exact hindexCard
      omega
    have hqRhoGP : PointInGeneralPosition (rho.image φ) q :=
      pointInGeneralPosition_of_avoidsSmallAffineSpans
        pointSet (rho.image φ) n q hqAvoid hrhoImageSubset hrhoImageCard
    have hrhoGeneric : IsGeneric (rho.image φ) := by
      by_contra hng
      exact (not_mem_realization_of_not_isGeneric_of_pointGeneralPosition
        n (rho.image φ) hrhoImageCard hng hqRhoGP) hqRho
    have hrhoImageCardI : (rho.image φ).card = Fintype.card I :=
      hrhoImageCard.trans (by simpa using hindexCard.symm)
    simp only [covered]
    apply Set.mem_iUnion.mpr
    refine ⟨rho, Set.mem_iUnion.mpr ⟨?_, hqRho⟩⟩
    exact Finset.mem_filter.mpr
      ⟨hrhoTop, hrhoImageCardI, hrhoGeneric⟩

  have hdense : Dense (smallAffineSpanLocus pointSet n)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp
      (interior_smallAffineSpanLocus_eq_empty pointSet n rfl)
  have hInteriorClosure :
      interior Gamma ⊆
        closure (interior Gamma ∩ (smallAffineSpanLocus pointSet n)ᶜ) :=
    hdense.open_subset_closure_inter isOpen_interior
  have hInteriorCovered : interior Gamma ⊆ covered :=
    hInteriorClosure.trans
      (closure_minimal hgoodInteriorSubset hcoveredClosed)
  have hGammaConvex : Convex ℝ Gamma := convex_convexHull ℝ (Set.range b)
  have hGammaInterior : (interior Gamma).Nonempty := by
    exact ⟨Finset.univ.centroid ℝ b, b.centroid_mem_interior_convexHull⟩
  have hGammaClosed : IsClosed Gamma :=
    (Set.finite_range b).isClosed_convexHull ℝ
  have hclosureGamma : closure (interior Gamma) = Gamma := by
    calc
      closure (interior Gamma) = closure Gamma :=
        hGammaConvex.closure_interior_eq_closure_of_nonempty_interior
          hGammaInterior
      _ = Gamma := hGammaClosed.closure_eq
  have hzCovered : z ∈ covered := by
    apply closure_minimal hInteriorCovered hcoveredClosed
    rw [hclosureGamma]
    exact hz
  simp only [covered] at hzCovered
  obtain ⟨rho, hrho⟩ := Set.mem_iUnion.mp hzCovered
  obtain ⟨hrhoGenericTop, hzRho⟩ := Set.mem_iUnion.mp hrho
  have hrhoData := Finset.mem_filter.mp hrhoGenericTop
  have hrhoTop := Finset.mem_filter.mp hrhoData.1
  refine ⟨rho, ?_, ?_, hrhoData.2.1, hrhoData.2.2, ?_⟩
  · exact (FiniteSimplicialComplex.mem_simplices_iff
      (Envelope.complex D Finset.univ) rho).mp hrhoTop.1
  · simpa using hrhoTop.2
  · exact hzRho

end EuclideanIntersection
end BeyondSperner
