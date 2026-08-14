import BeyondSperner.Geometry.Triangulation.Core
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Purity of finite geometric triangulations

This file proves, rather than assumes, the dimensional homogeneity of a
finite geometric triangulation of a simplex.  The proof uses the ordinary
finite-dimensional topology on the ambient real vector space.  This
topological hypothesis is stated explicitly: it is what rules out a finite
cover of an open set by lower-dimensional affine subspaces.
-/

namespace BeyondSperner

open Classical Set

namespace GeometricTriangulation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ E)
variable (T : Data b)

/-- Every geometric face has at most the number of vertices of the ambient
reference simplex. -/
theorem geometric_face_card_le {s : Finset E} (hs : s ∈ T.complex.faces) :
    s.card ≤ n + 1 := by
  let sigma := abstractFace b T s hs
  have hsigma : sigma ∈ faceComplex b T Finset.univ :=
    abstractFace_mem_full b T s hs
  have hcard := faceComplex_card_le b T Finset.univ hsigma
  simpa [sigma] using hcard

/-- The finite collection of faces which are strictly lower-dimensional
than the reference simplex. -/
noncomputable def lowFaces : Finset (Finset E) :=
  (faces_finite b T).toFinset.filter fun s ↦ s.card < n + 1

theorem mem_lowFaces_iff (s : Finset E) :
    s ∈ lowFaces b T ↔ s ∈ T.complex.faces ∧ s.card < n + 1 := by
  simp [lowFaces]

/-- Union of the affine spans of all lower-dimensional geometric faces. -/
noncomputable def lowerDimensionalLocus : Set E :=
  ⋃ s ∈ lowFaces b T, (affineSpan ℝ (s : Set E) : Set E)

/-- A lower-dimensional face spans a proper affine subspace. -/
theorem affineSpan_ne_top_of_mem_lowFaces
    {s : Finset E} (hs : s ∈ lowFaces b T) :
    affineSpan ℝ (s : Set E) ≠ ⊤ := by
  let : FiniteDimensional ℝ E := b.finiteDimensional
  have hsData := (mem_lowFaces_iff b T s).1 hs
  intro htop
  have hcardRank :=
    (T.complex.indep hsData.1).affineSpan_eq_top_iff_card_eq_finrank_add_one.mp
      (by simpa using htop)
  have hbRank : n + 1 = Module.finrank ℝ E + 1 := by
    simpa using b.card_eq_finrank_add_one
  have hcard : s.card = n + 1 := by
    simpa [hbRank] using hcardRank
  omega

/-- Affine spans of faces are closed in the finite-dimensional ambient
space. -/
theorem isClosed_affineSpan_face
    (b : AffineBasis (Fin (n + 1)) ℝ E) (s : Finset E) :
    IsClosed (affineSpan ℝ (s : Set E) : Set E) := by
  let : FiniteDimensional ℝ E := b.finiteDimensional
  exact AffineSubspace.closed_of_finiteDimensional _

/-- A proper affine span has empty ambient interior. -/
theorem interior_affineSpan_eq_empty_of_mem_lowFaces
    {s : Finset E} (hs : s ∈ lowFaces b T) :
    interior (affineSpan ℝ (s : Set E) : Set E) = ∅ := by
  by_contra hne
  have hnonempty :
      (interior (affineSpan ℝ (s : Set E) : Set E)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hne
  have htop := isOpen_interior.affineSpan_eq_top hnonempty
  have hspanTop : affineSpan ℝ (s : Set E) = ⊤ := by
    apply top_unique
    rw [← htop]
    have hmono :
        affineSpan ℝ (interior (affineSpan ℝ (s : Set E) : Set E)) ≤
          affineSpan ℝ (affineSpan ℝ (s : Set E) : Set E) :=
      affineSpan_mono ℝ interior_subset
    simpa only [AffineSubspace.affineSpan_coe] using hmono
  exact affineSpan_ne_top_of_mem_lowFaces b T hs hspanTop

omit [NormedSpace ℝ E] in
/-- A finite union of closed sets with empty interior again has empty
interior.  Closedness is essential here. -/
theorem interior_biUnion_finset_eq_empty
    {ι : Type*} (S : Finset ι) (f : ι → Set E)
    (hclosed : ∀ i ∈ S, IsClosed (f i))
    (hempty : ∀ i ∈ S, interior (f i) = ∅) :
    interior (⋃ i ∈ S, f i) = ∅ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hunion : (⋃ i ∈ insert a S, f i) = f a ∪ ⋃ i ∈ S, f i := by
        ext x
        simp
      rw [hunion]
      rw [interior_union_isClosed_of_interior_empty
        (hclosed a (Finset.mem_insert_self a S))]
      · exact hempty a (Finset.mem_insert_self a S)
      · apply ih
        · intro i hi
          exact hclosed i (Finset.mem_insert_of_mem hi)
        · intro i hi
          exact hempty i (Finset.mem_insert_of_mem hi)

/-- The whole lower-dimensional locus has empty interior. -/
theorem interior_lowerDimensionalLocus_eq_empty :
    interior (lowerDimensionalLocus b T) = ∅ := by
  apply interior_biUnion_finset_eq_empty (lowFaces b T)
  · intro s _
    exact isClosed_affineSpan_face b s
  · intro s hs
    exact interior_affineSpan_eq_empty_of_mem_lowFaces b T hs

/-- The lower-dimensional locus is closed. -/
theorem isClosed_lowerDimensionalLocus :
    IsClosed (lowerDimensionalLocus b T) := by
  apply isClosed_biUnion_finset
  intro s _
  exact isClosed_affineSpan_face b s

/-- The finite collection of full-dimensional faces. -/
noncomputable def fullFaces : Finset (Finset E) :=
  (faces_finite b T).toFinset.filter fun s ↦ s.card = n + 1

theorem mem_fullFaces_iff (s : Finset E) :
    s ∈ fullFaces b T ↔ s ∈ T.complex.faces ∧ s.card = n + 1 := by
  simp [fullFaces]

/-- Union of the geometric simplices carried by the full-dimensional
faces. -/
noncomputable def fullDimensionalSpace : Set E :=
  ⋃ s ∈ fullFaces b T, convexHull ℝ (s : Set E)

/-- The full-dimensional part is closed because it is a finite union of
convex hulls of finite sets. -/
theorem isClosed_fullDimensionalSpace :
    IsClosed (fullDimensionalSpace b T) := by
  apply isClosed_biUnion_finset
  intro s _
  exact s.finite_toSet.isClosed_convexHull ℝ

/-- Every point of the interior which avoids all lower-dimensional affine
spans is carried by a full-dimensional face. -/
theorem interior_sdiff_lowerDimensionalLocus_subset_fullDimensionalSpace :
    interior (referenceFace b Finset.univ) \
        lowerDimensionalLocus b T ⊆ fullDimensionalSpace b T := by
  intro x hx
  have hxReference : x ∈ referenceFace b Finset.univ := interior_subset hx.1
  have hxSpace : x ∈ T.complex.space := by
    rw [T.space_eq]
    simpa [referenceFace, referenceFaceVertices] using hxReference
  obtain ⟨s, hsFace, hxHull⟩ := T.complex.mem_space_iff.mp hxSpace
  have hcardLe := geometric_face_card_le b T hsFace
  have hcard : s.card = n + 1 := by
    by_contra hne
    have hcardLt : s.card < n + 1 := lt_of_le_of_ne hcardLe hne
    have hsLow : s ∈ lowFaces b T :=
      (mem_lowFaces_iff b T s).2 ⟨hsFace, hcardLt⟩
    apply hx.2
    rw [lowerDimensionalLocus]
    apply Set.mem_iUnion.mpr
    refine ⟨s, Set.mem_iUnion.mpr ⟨hsLow, ?_⟩⟩
    exact convexHull_subset_affineSpan (s : Set E) hxHull
  rw [fullDimensionalSpace]
  apply Set.mem_iUnion.mpr
  refine ⟨s, Set.mem_iUnion.mpr ⟨?_, hxHull⟩⟩
  exact (mem_fullFaces_iff b T s).2 ⟨hsFace, hcard⟩

/-- Full-dimensional faces cover the interior of the reference simplex.
The density step is precisely where the empty-interior theorem for the
lower-dimensional locus is used. -/
theorem interior_referenceFace_subset_fullDimensionalSpace :
    interior (referenceFace b Finset.univ) ⊆ fullDimensionalSpace b T := by
  have hdense : Dense (lowerDimensionalLocus b T)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp
      (interior_lowerDimensionalLocus_eq_empty b T)
  have hopen : IsOpen (interior (referenceFace b Finset.univ)) :=
    isOpen_interior
  have hclosure :
      interior (referenceFace b Finset.univ) ⊆
        closure (interior (referenceFace b Finset.univ) ∩
          (lowerDimensionalLocus b T)ᶜ) :=
    hdense.open_subset_closure_inter hopen
  have hinside :
      interior (referenceFace b Finset.univ) ∩
          (lowerDimensionalLocus b T)ᶜ ⊆ fullDimensionalSpace b T := by
    simpa only [sdiff_eq, inter_comm] using
      (interior_sdiff_lowerDimensionalLocus_subset_fullDimensionalSpace b T)
  exact hclosure.trans
    (closure_minimal hinside (isClosed_fullDimensionalSpace b T))

/-- Full-dimensional faces cover the entire reference simplex.  Closure of
the interior is the simplex itself because an affine basis has a centroid
in its interior. -/
theorem referenceFace_subset_fullDimensionalSpace :
    referenceFace b Finset.univ ⊆ fullDimensionalSpace b T := by
  let gamma : Set E := referenceFace b Finset.univ
  have hgammaEq : gamma = convexHull ℝ (Set.range b) := by
    simp [gamma, referenceFace, referenceFaceVertices]
  have hconvex : Convex ℝ gamma := by
    rw [hgammaEq]
    exact convex_convexHull ℝ (Set.range b)
  have hinterior : (interior gamma).Nonempty := by
    rw [hgammaEq]
    exact ⟨Finset.univ.centroid ℝ b, b.centroid_mem_interior_convexHull⟩
  have hclosedGamma : IsClosed gamma := by
    rw [hgammaEq]
    exact Set.finite_range b |>.isClosed_convexHull ℝ
  have hclosureInterior : closure (interior gamma) = gamma := by
    calc
      closure (interior gamma) = closure gamma :=
        hconvex.closure_interior_eq_closure_of_nonempty_interior hinterior
      _ = gamma := hclosedGamma.closure_eq
  have hinteriorSubset : interior gamma ⊆ fullDimensionalSpace b T := by
    simpa [gamma] using
      (interior_referenceFace_subset_fullDimensionalSpace b T)
  change gamma ⊆ fullDimensionalSpace b T
  rw [← hclosureInterior]
  exact closure_minimal hinteriorSubset (isClosed_fullDimensionalSpace b T)

/-- The centroid of an affinely independent finite set cannot lie in the
affine span of a proper subset of that set. -/
theorem subset_of_indexed_centroid_mem_affineSpan
    {s t : Finset E} (hsNonempty : s.Nonempty)
    (hsIndependent : AffineIndependent ℝ ((↑) : s → E))
    (hcentroid :
      (Finset.univ : Finset s).centroid ℝ ((↑) : s → E) ∈
        affineSpan ℝ (s ∩ t : Set E)) :
    s ⊆ t := by
  intro y hyS
  by_contra hyT
  let indexSet : Set s := {z | z.1 ∈ t}
  have himage : ((↑) : s → E) '' indexSet = (s ∩ t : Set E) := by
    ext z
    simp [indexSet, and_comm]
  let vertices : Finset s := Finset.univ
  let weights : s → ℝ := vertices.centroidWeights ℝ
  have hsum : ∑ i ∈ vertices, weights i = 1 := by
    exact vertices.sum_centroidWeights_eq_one_of_nonempty ℝ
      (by simpa [vertices] using hsNonempty.attach)
  have hcombination :
      vertices.affineCombination ℝ ((↑) : s → E) weights ∈
        affineSpan ℝ (((↑) : s → E) '' indexSet) := by
    rw [himage]
    simpa [vertices, weights, Finset.centroid_def] using hcentroid
  let iy : s := ⟨y, hyS⟩
  have hiyNot : iy ∉ indexSet := by
    simpa [iy, indexSet] using hyT
  have hzero : weights iy = 0 :=
    hsIndependent.eq_zero_of_affineCombination_mem_affineSpan
      hsum hcombination (by simp [vertices]) hiyNot
  have hcardNe : (vertices.card : ℝ) ≠ 0 := by
    have hverticesNonempty : vertices.Nonempty := by
      exact ⟨iy, by simp [vertices]⟩
    exact_mod_cast Finset.card_ne_zero.mpr hverticesNonempty
  have hweightNe : weights iy ≠ 0 := by
    simpa [weights, Finset.centroidWeights_apply] using inv_ne_zero hcardNe
  exact hweightNe hzero

/-- Every geometric face is contained in a full-dimensional geometric
face.  This is the precise dimensional-homogeneity statement needed for
purity. -/
theorem exists_full_face_superset
    {s : Finset E} (hs : s ∈ T.complex.faces) :
    ∃ t : Finset E,
      t ∈ T.complex.faces ∧ t.card = n + 1 ∧ s ⊆ t := by
  let x : E :=
    (Finset.univ : Finset s).centroid ℝ ((↑) : s → E)
  have hsNonempty : s.Nonempty := T.complex.nonempty_of_mem_faces hs
  have hsum :
      ∑ i ∈ (Finset.univ : Finset s),
        (Finset.univ : Finset s).centroidWeights ℝ i = 1 :=
    (Finset.univ : Finset s).sum_centroidWeights_eq_one_of_nonempty ℝ
      (by simpa using hsNonempty.attach)
  have hxHullS : x ∈ convexHull ℝ (s : Set E) := by
    have hxRange :
        x ∈ convexHull ℝ (Set.range ((↑) : s → E)) := by
      dsimp [x]
      rw [Finset.centroid_def]
      exact affineCombination_mem_convexHull (by simp) hsum
    simpa using hxRange
  have hxReference : x ∈ referenceFace b Finset.univ := by
    have hxSpace : x ∈ T.complex.space :=
      T.complex.convexHull_subset_space hs hxHullS
    rw [T.space_eq] at hxSpace
    simpa [referenceFace, referenceFaceVertices] using hxSpace
  have hxFull : x ∈ fullDimensionalSpace b T :=
    referenceFace_subset_fullDimensionalSpace b T hxReference
  rw [fullDimensionalSpace] at hxFull
  obtain ⟨t, hxFull⟩ := Set.mem_iUnion.mp hxFull
  obtain ⟨htStored, hxHullT⟩ := Set.mem_iUnion.mp hxFull
  have htData := (mem_fullFaces_iff b T t).1 htStored
  refine ⟨t, htData.1, htData.2, ?_⟩
  apply subset_of_indexed_centroid_mem_affineSpan hsNonempty
      (T.complex.indep hs)
  apply convexHull_subset_affineSpan (s ∩ t : Set E)
  rw [← T.complex.convexHull_inter_convexHull hs htData.1]
  exact ⟨hxHullS, hxHullT⟩

/-- Purity is automatic for a finite geometric triangulation of a simplex;
it is no longer an external interface obligation. -/
theorem facetsHaveCardinality :
    FacetsHaveCardinality (b := b) T (n + 1) := by
  intro s hsFacet
  have hsData := (Geometry.SimplicialComplex.mem_facets.mp hsFacet)
  obtain ⟨t, htFace, htCard, hst⟩ :=
    exists_full_face_superset b T hsData.1
  have hstEq : s = t := hsData.2 t htFace hst
  simpa [hstEq] using htCard

/-- Kernel-checked abstract purity, with no purity hypothesis in the
statement. -/
theorem family_full_isPure_of_data :
    ((family b T).complex Finset.univ).IsPureOfCardinality (n + 1) :=
  family_full_isPure b T (facetsHaveCardinality b T)

end GeometricTriangulation
end BeyondSperner
