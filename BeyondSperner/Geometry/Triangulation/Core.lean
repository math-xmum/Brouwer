import BeyondSperner.Coloring.VectorHedgehog
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Finite geometric triangulations and their face families

This file begins the general bridge used in Section 10.  A finite geometric
triangulation is represented by an actual `Geometry.SimplicialComplex` whose
space is exactly the reference simplex.  No pseudo-simplex, chain-simplex,
purity, or incidence conclusion is stored in the input structure.

For every subset `C` of the reference vertices we construct the abstract
complex of geometric faces lying in the reference face spanned by `C`.  The
construction includes the empty face, proves downward closure and the exact
cardinality bound, and supplies the face-coordinate and ambient-inclusion
properties needed by Theorems 10.9 and 10.10.
-/

namespace BeyondSperner

open Classical Set

namespace GeometricTriangulation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ E)

/-- A finite geometric simplicial complex with exact coverage of the
reference simplex.  Importantly, nonbranching and purity are not fields. -/
structure Data where
  complex : Geometry.SimplicialComplex ℝ E
  verticesFinite : complex.vertices.Finite
  space_eq : complex.space = convexHull ℝ (Set.range b)

variable (T : Data b)

/-- Vertices of the geometric triangulation, bundled with the proof that
their singleton is a geometric face. -/
abbrev Data.Vertex (T : Data b) := T.complex.vertices

noncomputable instance vertexFintype : Fintype T.Vertex :=
  T.verticesFinite.fintype

noncomputable instance vertexDecidableEq : DecidableEq T.Vertex :=
  Classical.decEq _

/-- Forget the vertex certificates of an abstract simplex. -/
noncomputable def realizeSimplex (sigma : Finset T.Vertex) : Finset E :=
  sigma.image Subtype.val

/-- Vertices of the reference face indexed by `C`. -/
noncomputable def referenceFaceVertices (C : Finset (Fin (n + 1))) : Finset E :=
  C.image b

/-- The geometric reference face indexed by `C`. -/
noncomputable def referenceFace (C : Finset (Fin (n + 1))) : Set E :=
  convexHull ℝ (referenceFaceVertices b C : Set E)

/-- Predicate saying that all vertices of an abstract simplex lie in the
reference face indexed by `C`. -/
def LiesInReferenceFace (C : Finset (Fin (n + 1)))
    (sigma : Finset T.Vertex) : Prop :=
  ∀ v ∈ sigma, v.1 ∈ referenceFace b C

/-- The finite abstract complex induced on the geometric reference face
`Γ_C`.  The empty abstract simplex is inserted explicitly because mathlib's
geometric simplicial complex stores only nonempty faces. -/
noncomputable def faceComplex (C : Finset (Fin (n + 1))) :
    FiniteSimplicialComplex T.Vertex where
  simplices := Finset.univ.filter fun sigma ↦
    sigma = ∅ ∨
      (realizeSimplex b T sigma ∈ T.complex.faces ∧
        LiesInReferenceFace b T C sigma)
  empty_mem := by simp
  downward_closed := by
    intro sigma tau hsigma htau
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsigmaData := (Finset.mem_filter.mp hsigma).2
    rcases hsigmaData with hsigmaEmpty | ⟨hsigmaFace, hsigmaInFace⟩
    · left
      subst sigma
      exact Finset.subset_empty.mp htau
    · by_cases htauEmpty : tau = ∅
      · exact Or.inl htauEmpty
      · right
        constructor
        · apply T.complex.down_closed hsigmaFace
            (Finset.image_mono _ htau)
          simpa [realizeSimplex] using
            (Finset.nonempty_iff_ne_empty.mpr htauEmpty)
        · intro v hv
          exact hsigmaInFace v (htau hv)

theorem mem_faceComplex_iff (C : Finset (Fin (n + 1)))
    (sigma : Finset T.Vertex) :
    sigma ∈ faceComplex b T C ↔
      sigma = ∅ ∨
        (realizeSimplex b T sigma ∈ T.complex.faces ∧
          LiesInReferenceFace b T C sigma) := by
  change sigma ∈ Finset.univ.filter _ ↔ _
  simp

/-- A geometric face has no more vertices than the reference face containing
it.  This is derived from affine independence, not imposed by the definition
of `faceComplex`. -/
theorem faceComplex_card_le (C : Finset (Fin (n + 1)))
    {sigma : Finset T.Vertex} (hsigma : sigma ∈ faceComplex b T C) :
    sigma.card ≤ C.card := by
  rcases sigma.eq_empty_or_nonempty with rfl | hsigmaNonempty
  · simp
  have hsigmaData := (mem_faceComplex_iff b T C sigma).1 hsigma
  rcases hsigmaData with hsigmaEmpty | ⟨hsigmaFace, hsigmaInFace⟩
  · exact (hsigmaNonempty.ne_empty hsigmaEmpty).elim
  · let rho : Finset E := realizeSimplex b T sigma
    let gamma : Finset E := referenceFaceVertices b C
    have hrhoIndependent : AffineIndependent ℝ ((↑) : rho → E) :=
      T.complex.indep hsigmaFace
    have hrhoSubset : (rho : Set E) ⊆ affineSpan ℝ (gamma : Set E) := by
      intro x hx
      change x ∈ realizeSimplex b T sigma at hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact convexHull_subset_affineSpan (gamma : Set E)
        (hsigmaInFace v hv)
    have hcard :=
      hrhoIndependent.card_le_card_of_subset_affineSpan hrhoSubset
    have hrhoCard : rho.card = sigma.card := by
      simpa [rho, realizeSimplex] using
        (Finset.card_image_of_injective sigma Subtype.val_injective)
    have hgammaCard : gamma.card = C.card := by
      exact Finset.card_image_of_injective _ b.ind.injective
    simpa [hrhoCard, hgammaCard] using hcard

/-- The simplex-family associated with the finite geometric triangulation. -/
noncomputable def family : SimplexFamily (Fin (n + 1)) T.Vertex where
  complex := faceComplex b T
  dimension := fun C _sigma hsigma ↦ faceComplex_card_le b T C hsigma

/-- Reference faces are monotone in their index set. -/
theorem referenceFace_mono {C A : Finset (Fin (n + 1))} (hCA : C ⊆ A) :
    referenceFace b C ⊆ referenceFace b A := by
  apply convexHull_mono
  intro x hx
  obtain ⟨i, hiC, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨i, hCA hiC, rfl⟩

/-- The induced abstract complexes are monotone under inclusion of reference
faces. -/
theorem faceComplex_mono {C A : Finset (Fin (n + 1))} (hCA : C ⊆ A)
    {sigma : Finset T.Vertex} (hsigma : sigma ∈ faceComplex b T C) :
    sigma ∈ faceComplex b T A := by
  rcases (mem_faceComplex_iff b T C sigma).1 hsigma with rfl | hsigmaData
  · exact (faceComplex b T A).empty_mem
  · apply (mem_faceComplex_iff b T A sigma).2
    right
    refine ⟨hsigmaData.1, ?_⟩
    intro v hv
    exact referenceFace_mono b hCA (hsigmaData.2 v hv)

/-- Every face-family simplex is an ambient simplex of `D(I)`. -/
theorem faceComplex_subset_full (C : Finset (Fin (n + 1)))
    {sigma : Finset T.Vertex} (hsigma : sigma ∈ faceComplex b T C) :
    sigma ∈ faceComplex b T Finset.univ :=
  faceComplex_mono b T (Finset.subset_univ C) hsigma

/-- Every triangulation vertex lies in the full reference simplex.  This is
the first place where exact coverage of the reference simplex is used. -/
theorem vertex_mem_referenceFace_univ (v : T.Vertex) :
    v.1 ∈ referenceFace b Finset.univ := by
  have hvSpace : v.1 ∈ T.complex.space :=
    T.complex.vertices_subset_space v.2
  rw [T.space_eq] at hvSpace
  simpa [referenceFace, referenceFaceVertices] using hvSpace

/-- On the full reference face, the abstract complex contains exactly the
nonempty geometric faces (together with the explicitly inserted empty
face).  Thus no simplex is lost by the face-family construction. -/
theorem mem_faceComplex_univ_iff (sigma : Finset T.Vertex) :
    sigma ∈ faceComplex b T Finset.univ ↔
      sigma = ∅ ∨ realizeSimplex b T sigma ∈ T.complex.faces := by
  rw [mem_faceComplex_iff]
  constructor
  · rintro (rfl | ⟨hsigma, -⟩)
    · exact Or.inl rfl
    · exact Or.inr hsigma
  · rintro (rfl | hsigma)
    · exact Or.inl rfl
    · exact Or.inr ⟨hsigma, fun v _ ↦ vertex_mem_referenceFace_univ b T v⟩

/-- Bundle the vertices of a geometric face as vertices of the finite
abstract complex.  The face certificate, rather than an arbitrary choice,
supplies each vertex certificate. -/
noncomputable def abstractFace (s : Finset E) (hs : s ∈ T.complex.faces) :
    Finset T.Vertex :=
  s.attach.image fun x ↦
    ⟨x.1, T.complex.down_closed hs
      (Finset.singleton_subset_iff.mpr x.2) (Finset.singleton_nonempty x.1)⟩

@[simp]
theorem realize_abstractFace (s : Finset E) (hs : s ∈ T.complex.faces) :
    realizeSimplex b T (abstractFace b T s hs) = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
    rw [← hvx, ← congrArg Subtype.val hyv]
    exact y.2
  · intro hx
    let vx : T.Vertex :=
      ⟨x, T.complex.down_closed hs
        (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)⟩
    apply Finset.mem_image.mpr
    refine ⟨vx, ?_, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨x, hx⟩, Finset.mem_attach s ⟨x, hx⟩, rfl⟩

@[simp]
theorem card_abstractFace (s : Finset E) (hs : s ∈ T.complex.faces) :
    (abstractFace b T s hs).card = s.card := by
  rw [← Finset.card_image_of_injective
    (abstractFace b T s hs) Subtype.val_injective]
  exact congrArg Finset.card (realize_abstractFace b T s hs)

/-- Every nonempty geometric face occurs in the full abstract complex. -/
theorem abstractFace_mem_full (s : Finset E) (hs : s ∈ T.complex.faces) :
    abstractFace b T s hs ∈ faceComplex b T Finset.univ := by
  apply (mem_faceComplex_univ_iff b T _).2
  exact Or.inr (by simpa using hs)

/-- Finiteness of the vertex set implies finiteness of the geometric face
set.  This is needed to extend any face to an actual facet without a Zorn
argument. -/
theorem faces_finite : T.complex.faces.Finite := by
  classical
  let vertices : Finset E := T.verticesFinite.toFinset
  apply vertices.powerset.finite_toSet.subset
  intro s hs
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro x hx
  rw [Set.Finite.mem_toFinset]
  exact T.complex.down_closed hs
    (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)

/-- Every geometric face of a finite complex is contained in a facet. -/
theorem exists_facet_superset {s : Finset E} (hs : s ∈ T.complex.faces) :
    ∃ t : Finset E, t ∈ T.complex.facets ∧ s ⊆ t := by
  obtain ⟨t, hst, htMax⟩ := (faces_finite b T).exists_le_maximal hs
  refine ⟨t, ?_, hst⟩
  rw [Geometry.SimplicialComplex.mem_facets, maximal_iff] at *
  exact htMax

/-- Exact coverage of the nonempty reference simplex ensures that the
geometric complex has at least one face and hence at least one facet. -/
theorem exists_facet : T.complex.facets.Nonempty := by
  let i : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  have hbi : b i ∈ T.complex.space := by
    rw [T.space_eq]
    exact subset_convexHull ℝ (Set.range b) (Set.mem_range_self i)
  obtain ⟨s, hs, -⟩ := T.complex.mem_space_iff.mp hbi
  obtain ⟨t, ht, -⟩ := exists_facet_superset b T hs
  exact ⟨t, ht⟩

/-- Standard geometric purity condition: every maximal geometric simplex
has the stated number of vertices.  It is deliberately a predicate rather
than a field of `Data`, so uses of purity remain visible in theorem
statements. -/
def FacetsHaveCardinality (m : ℕ) : Prop :=
  ∀ {s : Finset E}, s ∈ T.complex.facets → s.card = m

/-- Geometric facet purity induces the exact abstract purity property used
by Theorem 10.10.  In particular, the abstract purity conclusion is not an
input field of the triangulation data. -/
theorem family_full_isPure
    (hfacets : FacetsHaveCardinality (b := b) T (n + 1)) :
    ((family b T).complex Finset.univ).IsPureOfCardinality (n + 1) := by
  intro sigma hsigma
  by_cases hsigmaEmpty : sigma = ∅
  · subst sigma
    obtain ⟨t, htFacet⟩ := exists_facet b T
    let tau := abstractFace b T t
      (Geometry.SimplicialComplex.facets_subset htFacet)
    refine ⟨tau, ?_, Finset.empty_subset _, ?_⟩
    · exact abstractFace_mem_full b T t
        (Geometry.SimplicialComplex.facets_subset htFacet)
    · simpa [tau] using hfacets htFacet
  · have hsigmaFace : realizeSimplex b T sigma ∈ T.complex.faces :=
      ((mem_faceComplex_univ_iff b T sigma).1 hsigma).resolve_left hsigmaEmpty
    obtain ⟨t, htFacet, hst⟩ := exists_facet_superset b T hsigmaFace
    let htFace : t ∈ T.complex.faces :=
      Geometry.SimplicialComplex.facets_subset htFacet
    let tau := abstractFace b T t htFace
    refine ⟨tau, abstractFace_mem_full b T t htFace, ?_, ?_⟩
    · intro v hv
      have hvRealized : v.1 ∈ realizeSimplex b T sigma :=
        Finset.mem_image.mpr ⟨v, hv, rfl⟩
      have hvTauRealized : v.1 ∈ realizeSimplex b T tau := by
        rw [realize_abstractFace b T t htFace]
        exact hst hvRealized
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hvTauRealized
      have : w = v := Subtype.ext hwv
      simpa [this] using hw
    · simpa [tau] using hfacets htFacet

/-- Every point of a reference face has zero barycentric coordinates outside
that face. -/
theorem coord_eq_zero_of_mem_referenceFace
    {C : Finset (Fin (n + 1))} {x : E}
    (hx : x ∈ referenceFace b C) {i : Fin (n + 1)} (hiC : i ∉ C) :
    b.coord i x = 0 := by
  let H : Set E := (b.coord i) ⁻¹' ({0} : Set ℝ)
  have hvertices : (referenceFaceVertices b C : Set E) ⊆ H := by
    intro y hy
    obtain ⟨j, hjC, rfl⟩ := Finset.mem_image.mp hy
    change b.coord i (b j) = 0
    rw [b.coord_apply_ne]
    exact fun hij ↦ hiC (hij ▸ hjC)
  have hconvex : Convex ℝ H := by
    exact (convex_singleton (0 : ℝ)).affine_preimage (b.coord i)
  exact convexHull_min hvertices hconvex hx

/-- Exact barycentric description of a reference face: all coordinates are
nonnegative, and precisely the coordinates outside the indexing set are
forced to vanish.  The reverse implication is proved by reconstructing the
point from its affine-basis coordinates supported on `C`. -/
theorem mem_referenceFace_iff_coord
    (C : Finset (Fin (n + 1))) (x : E) :
    x ∈ referenceFace b C ↔
      (∀ i, 0 ≤ b.coord i x) ∧ ∀ i, i ∉ C → b.coord i x = 0 := by
  constructor
  · intro hx
    have hxFull : x ∈ referenceFace b Finset.univ :=
      referenceFace_mono b (Finset.subset_univ C) hx
    have hxNonnegative : ∀ i, 0 ≤ b.coord i x := by
      rw [referenceFace, referenceFaceVertices] at hxFull
      simpa [AffineBasis.convexHull_eq_nonneg_coord] using hxFull
    exact ⟨hxNonnegative, fun i hi ↦
      coord_eq_zero_of_mem_referenceFace b hx hi⟩
  · rintro ⟨hnonnegative, hzero⟩
    let w : {i // i ∈ C} → ℝ := fun i ↦ b.coord i.1 x
    let z : {i // i ∈ C} → E := fun i ↦ b i.1
    apply mem_convexHull_of_exists_fintype w z
    · intro i
      exact hnonnegative i.1
    · calc
        ∑ i, w i = ∑ i ∈ C, b.coord i x := by
          symm
          exact Finset.sum_subtype C (fun i ↦ by simp) (fun i ↦ b.coord i x)
        _ = ∑ i, b.coord i x := by
          apply Finset.sum_subset (Finset.subset_univ C)
          intro i _ hi
          exact hzero i hi
        _ = 1 := b.sum_coord_apply_eq_one x
    · intro i
      exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
    · calc
        ∑ i, w i • z i = ∑ i ∈ C, b.coord i x • b i := by
          symm
          exact Finset.sum_subtype C (fun i ↦ by simp)
            (fun i ↦ b.coord i x • b i)
        _ = ∑ i, b.coord i x • b i := by
          apply Finset.sum_subset (Finset.subset_univ C)
          intro i _ hi
          rw [hzero i hi, zero_smul]
        _ = x := b.linear_combination_coord_eq_self x

/-- Barycentric coordinates commute with a finite center of mass whose
weights sum to one. -/
theorem coord_centerMass (s : Finset E) (w : E → ℝ)
    (hw : ∑ y ∈ s, w y = 1) (i : Fin (n + 1)) :
    b.coord i (s.centerMass w id) =
      ∑ y ∈ s, w y * b.coord i y := by
  rw [Finset.centerMass_eq_of_sum_1 s id hw]
  rw [← Finset.affineCombination_eq_linear_combination s id w hw]
  rw [Finset.map_affineCombination s id w hw (b.coord i)]
  rw [Finset.affineCombination_eq_linear_combination s
    ((b.coord i : E → ℝ) ∘ id) w hw]
  simp [Function.comp_apply, smul_eq_mul]

/-- Every vertex of a geometric face has nonnegative barycentric
coordinates, because exact coverage places all triangulation vertices in the
reference simplex. -/
theorem coord_nonnegative_of_mem_geometric_face
    {s : Finset E} (hs : s ∈ T.complex.faces)
    {y : E} (hy : y ∈ s) (i : Fin (n + 1)) :
    0 ≤ b.coord i y := by
  let v : T.Vertex :=
    ⟨y, T.complex.down_closed hs (Finset.singleton_subset_iff.mpr hy)
      (Finset.singleton_nonempty y)⟩
  exact ((mem_referenceFace_iff_coord b Finset.univ y).1
    (vertex_mem_referenceFace_univ b T v)).1 i

/-- The subcomplex induced on a reference face really covers that reference
face.  Given a point in a geometric simplex, all positive-weight vertices
in a convex representation must remain in the same reference face: an
outside positive barycentric coordinate would otherwise make the point's
corresponding coordinate positive. -/
theorem exists_faceComplex_simplex_containing
    (C : Finset (Fin (n + 1))) {x : E} (hx : x ∈ referenceFace b C) :
    ∃ sigma : Finset T.Vertex,
      sigma ∈ faceComplex b T C ∧
        x ∈ convexHull ℝ (realizeSimplex b T sigma : Set E) := by
  have hxSpace : x ∈ T.complex.space := by
    rw [T.space_eq]
    simpa [referenceFace, referenceFaceVertices] using
      referenceFace_mono b (Finset.subset_univ C) hx
  obtain ⟨s, hs, hxHull⟩ := T.complex.mem_space_iff.mp hxSpace
  rw [Finset.convexHull_eq] at hxHull
  obtain ⟨w, hwNonnegative, hwSum, hcenter⟩ := hxHull
  have hweightZero : ∀ y ∈ s, y ∉ referenceFace b C → w y = 0 := by
    intro y hy hyNotFace
    have hyNonnegative : ∀ i, 0 ≤ b.coord i y :=
      coord_nonnegative_of_mem_geometric_face b T hs hy
    have hnotzero : ¬ ∀ i, i ∉ C → b.coord i y = 0 := by
      intro hzero
      exact hyNotFace ((mem_referenceFace_iff_coord b C y).2
        ⟨hyNonnegative, hzero⟩)
    push Not at hnotzero
    obtain ⟨i, hiC, hiNe⟩ := hnotzero
    have hsumCoord : ∑ z ∈ s, w z * b.coord i z = 0 := by
      rw [← coord_centerMass b s w hwSum i, hcenter]
      exact coord_eq_zero_of_mem_referenceFace b hx hiC
    have htermsNonnegative :
        ∀ z ∈ s, 0 ≤ w z * b.coord i z := by
      intro z hz
      exact mul_nonneg (hwNonnegative z hz)
        (coord_nonnegative_of_mem_geometric_face b T hs hz i)
    have hyTerm : w y * b.coord i y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg htermsNonnegative).1 hsumCoord y hy
    exact (mul_eq_zero.mp hyTerm).resolve_right hiNe
  let t : Finset E := s.filter fun y ↦ y ∈ referenceFace b C
  have htSubset : t ⊆ s := Finset.filter_subset _ _
  have hwOutside : ∀ y ∈ s, y ∉ t → w y = 0 := by
    intro y hy hyNotT
    apply hweightZero y hy
    intro hyFace
    exact hyNotT (Finset.mem_filter.mpr ⟨hy, hyFace⟩)
  have hwSumT : ∑ y ∈ t, w y = 1 := by
    calc
      ∑ y ∈ t, w y = ∑ y ∈ s, w y :=
        Finset.sum_subset htSubset hwOutside
      _ = 1 := hwSum
  have htNonempty : t.Nonempty := by
    by_contra ht
    rw [Finset.not_nonempty_iff_eq_empty.mp ht] at hwSumT
    simp at hwSumT
  have hcenterT : t.centerMass w id = s.centerMass w id := by
    apply Finset.centerMass_congr_finset
    intro y hyUnion hwy
    have hyS : y ∈ s := by
      rcases Finset.mem_union.mp hyUnion with hyT | hyS
      · exact htSubset hyT
      · exact hyS
    have hyT : y ∈ t := by
      by_contra hyNotT
      exact hwy (hwOutside y hyS hyNotT)
    exact Finset.mem_inter.mpr ⟨hyT, hyS⟩
  have hxHullT : x ∈ convexHull ℝ (t : Set E) := by
    have hcenterMem : t.centerMass w id ∈ convexHull ℝ (t : Set E) :=
      t.centerMass_mem_convexHull
        (fun y hy ↦ hwNonnegative y (htSubset hy))
        (by rw [hwSumT]; norm_num)
        (fun y hy ↦ hy)
    simpa [hcenterT, hcenter] using hcenterMem
  let htFace : t ∈ T.complex.faces :=
    T.complex.down_closed hs htSubset htNonempty
  let sigma : Finset T.Vertex := abstractFace b T t htFace
  refine ⟨sigma, ?_, ?_⟩
  · apply (mem_faceComplex_iff b T C sigma).2
    right
    refine ⟨by simpa [sigma] using htFace, ?_⟩
    intro v hv
    have hvRealized : v.1 ∈ realizeSimplex b T sigma :=
      Finset.mem_image.mpr ⟨v, hv, rfl⟩
    rw [show realizeSimplex b T sigma = t by
      dsimp [sigma]
      exact realize_abstractFace b T t htFace] at hvRealized
    exact (Finset.mem_filter.mp hvRealized).2
  · rw [show realizeSimplex b T sigma = t by
      dsimp [sigma]
      exact realize_abstractFace b T t htFace]
    exact hxHullT

/-- Geometric realization of the induced abstract complex on a reference
face. -/
noncomputable def realizedFaceComplexSpace
    (C : Finset (Fin (n + 1))) : Set E :=
  ⋃ sigma ∈ (faceComplex b T C).simplices,
    convexHull ℝ (realizeSimplex b T sigma : Set E)

/-- The induced face complex has exact geometric space equal to the intended
reference face, not merely vertex containment in that face. -/
theorem realizedFaceComplexSpace_eq_referenceFace
    (C : Finset (Fin (n + 1))) :
    realizedFaceComplexSpace b T C = referenceFace b C := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [realizedFaceComplexSpace] at hx
    obtain ⟨sigma, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hsigmaStored, hxHull⟩ := Set.mem_iUnion.mp hx
    have hsigma : sigma ∈ faceComplex b T C :=
      (FiniteSimplicialComplex.mem_simplices_iff (faceComplex b T C) sigma).mp
        hsigmaStored
    rcases (mem_faceComplex_iff b T C sigma).1 hsigma with rfl | hsigmaData
    · simp [realizeSimplex] at hxHull
    · apply convexHull_min _ (convex_convexHull ℝ (referenceFaceVertices b C : Set E))
        hxHull
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact hsigmaData.2 v hv
  · intro x hx
    obtain ⟨sigma, hsigma, hxHull⟩ :=
      exists_faceComplex_simplex_containing b T C hx
    rw [realizedFaceComplexSpace]
    apply Set.mem_iUnion.mpr
    refine ⟨sigma, Set.mem_iUnion.mpr ⟨?_, hxHull⟩⟩
    exact (FiniteSimplicialComplex.mem_simplices_iff (faceComplex b T C) sigma).mpr
      hsigma

/-- Reference faces meet exactly in the face indexed by the intersection of
their vertex sets. -/
theorem referenceFace_inter (C A : Finset (Fin (n + 1))) :
    referenceFace b C ∩ referenceFace b A = referenceFace b (C ∩ A) := by
  ext x
  simp only [Set.mem_inter_iff, mem_referenceFace_iff_coord]
  constructor
  · rintro ⟨⟨hCnonneg, hCzero⟩, ⟨-, hAzero⟩⟩
    refine ⟨hCnonneg, ?_⟩
    intro i hi
    rw [Finset.mem_inter, not_and_or] at hi
    exact hi.elim (hCzero i) (hAzero i)
  · rintro ⟨hnonneg, hzero⟩
    refine ⟨⟨hnonneg, ?_⟩, ⟨hnonneg, ?_⟩⟩
    · intro i hiC
      exact hzero i (by simp [hiC])
    · intro i hiA
      exact hzero i (by simp [hiA])

/-- The induced abstract reference-face construction preserves binary
intersections exactly. -/
theorem mem_faceComplex_inter_iff
    (C A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex) :
    sigma ∈ faceComplex b T (C ∩ A) ↔
      sigma ∈ faceComplex b T C ∧ sigma ∈ faceComplex b T A := by
  constructor
  · intro hsigma
    exact ⟨faceComplex_mono b T Finset.inter_subset_left hsigma,
      faceComplex_mono b T Finset.inter_subset_right hsigma⟩
  · rintro ⟨hsigmaC, hsigmaA⟩
    by_cases hsigmaEmpty : sigma = ∅
    · subst sigma
      exact (faceComplex b T (C ∩ A)).empty_mem
    · have hsigmaCData :=
        ((mem_faceComplex_iff b T C sigma).1 hsigmaC).resolve_left hsigmaEmpty
      have hsigmaAData :=
        ((mem_faceComplex_iff b T A sigma).1 hsigmaA).resolve_left hsigmaEmpty
      apply (mem_faceComplex_iff b T (C ∩ A) sigma).2
      right
      refine ⟨hsigmaCData.1, ?_⟩
      intro v hv
      rw [← referenceFace_inter b C A]
      exact ⟨hsigmaCData.2 v hv, hsigmaAData.2 v hv⟩

/-- A simplex of cardinality `|A|-1` cannot lie in two distinct
codimension-one reference faces of `A`.  The proof uses exact preservation
of face intersections and the affine-independence cardinality bound. -/
theorem boundary_index_unique
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hcard : sigma.card + 1 = A.card)
    {B₁ B₂ : Finset (Fin (n + 1))}
    (hB₁ : B₁ ∈ SimplexFamily.boundaryIndices A)
    (hB₂ : B₂ ∈ SimplexFamily.boundaryIndices A)
    (hsigma₁ : sigma ∈ faceComplex b T B₁)
    (hsigma₂ : sigma ∈ faceComplex b T B₂) :
    B₁ = B₂ := by
  have hB₁Data := Finset.mem_filter.mp hB₁
  have hB₂Data := Finset.mem_filter.mp hB₂
  have hB₁Card : B₁.card + 1 = A.card := hB₁Data.2
  have hB₂Card : B₂.card + 1 = A.card := hB₂Data.2
  by_contra hne
  have hinterSS : B₁ ∩ B₂ ⊂ B₁ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro hinterEq
    have hB₁B₂ : B₁ ⊆ B₂ := by
      intro i hi
      have hiInter : i ∈ B₁ ∩ B₂ := by
        rw [hinterEq]
        exact hi
      exact (Finset.mem_inter.mp hiInter).2
    have hEq : B₁ = B₂ :=
      Finset.eq_of_subset_of_card_le hB₁B₂ (by omega)
    exact hne hEq
  have hsigmaInter : sigma ∈ faceComplex b T (B₁ ∩ B₂) :=
    (mem_faceComplex_inter_iff b T B₁ B₂ sigma).2
      ⟨hsigma₁, hsigma₂⟩
  have hdimension := faceComplex_card_le b T (B₁ ∩ B₂) hsigmaInter
  have hinterCard := Finset.card_lt_card hinterSS
  omega

/-- Consequently, the boundary-membership count of a relevant
codimension-one simplex is at most one. -/
theorem boundaryMembershipCount_le_one
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hcard : sigma.card + 1 = A.card) :
    (family b T).boundaryMembershipCount A sigma ≤ 1 := by
  rw [SimplexFamily.boundaryMembershipCount, Finset.card_le_one]
  intro B₁ hB₁ B₂ hB₂
  have hB₁Data := Finset.mem_filter.mp hB₁
  have hB₂Data := Finset.mem_filter.mp hB₂
  exact boundary_index_unique b T A sigma hcard
    hB₁Data.1 hB₂Data.1 hB₁Data.2 hB₂Data.2

/-- Geometric boundary predicate for a simplex in the triangulation of the
reference face `A`. -/
def LiesInReferenceBoundary
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex) : Prop :=
  ∃ B ∈ SimplexFamily.boundaryIndices A, LiesInReferenceFace b T B sigma

/-- For a codimension-one simplex already in `D(A)`, the combinatorial
boundary-membership count is one exactly when all its vertices lie in one
geometric codimension-one reference face. -/
theorem boundaryMembershipCount_eq_one_iff
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigmaA : sigma ∈ faceComplex b T A)
    (hcard : sigma.card + 1 = A.card) :
    (family b T).boundaryMembershipCount A sigma = 1 ↔
      LiesInReferenceBoundary b T A sigma := by
  let boundaryMembers :=
    (SimplexFamily.boundaryIndices A).filter
      (fun B ↦ sigma ∈ faceComplex b T B)
  have hle : boundaryMembers.card ≤ 1 := by
    have hle' := boundaryMembershipCount_le_one b T A sigma hcard
    change ((SimplexFamily.boundaryIndices A).filter
      (fun B ↦ sigma ∈ faceComplex b T B)).card ≤ 1 at hle'
    simpa [boundaryMembers] using hle'
  have hmember_iff : boundaryMembers.Nonempty ↔
      LiesInReferenceBoundary b T A sigma := by
    constructor
    · rintro ⟨B, hB⟩
      have hBData := Finset.mem_filter.mp hB
      refine ⟨B, hBData.1, ?_⟩
      rcases (mem_faceComplex_iff b T B sigma).1 hBData.2 with rfl | hdata
      · intro v hv
        simp at hv
      · exact hdata.2
    · rintro ⟨B, hBIndex, hBGeom⟩
      refine ⟨B, Finset.mem_filter.mpr ⟨hBIndex, ?_⟩⟩
      by_cases hsigmaEmpty : sigma = ∅
      · subst sigma
        exact (faceComplex b T B).empty_mem
      · have hsigmaAData :=
          ((mem_faceComplex_iff b T A sigma).1 hsigmaA).resolve_left hsigmaEmpty
        exact (mem_faceComplex_iff b T B sigma).2
          (Or.inr ⟨hsigmaAData.1, hBGeom⟩)
  change boundaryMembers.card = 1 ↔ _
  constructor
  · intro hcardOne
    apply hmember_iff.mp
    rw [← Finset.card_pos]
    omega
  · intro hboundary
    have hnonempty := hmember_iff.mpr hboundary
    have hone : 1 ≤ boundaryMembers.card := Finset.one_le_card.mpr hnonempty
    omega

/-- Standard local non-branching condition for the induced triangulations:
a codimension-one simplex has one top coface on the geometric boundary and
two top cofaces in the relative interior.  This is a visible theorem
obligation, not a field of `Data`. -/
def IsNonbranching : Prop :=
  ∀ (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex),
    sigma ∈ faceComplex b T A → sigma.card + 1 = A.card →
      (family b T).cofaceCount A sigma =
        if LiesInReferenceBoundary b T A sigma then 1 else 2

/-- The paper's statement that non-branching triangulations yield
pseudo-simplices, now separated into its exact local geometric hypothesis
and a checked incidence-count proof. -/
theorem IsNonbranching.isPseudoSimplex
    (hT : IsNonbranching b T) : (family b T).IsPseudoSimplex := by
  intro A sigma hRelevant
  have hsigmaA : sigma ∈ faceComplex b T A := by
    rcases hRelevant.2 with hsigmaA | ⟨B, hBIndex, hsigmaB⟩
    · exact hsigmaA
    · have hBA : B ⊆ A :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hBIndex).1
      exact faceComplex_mono b T hBA hsigmaB
  have hboundaryLe :=
    boundaryMembershipCount_le_one b T A sigma hRelevant.1
  have hboundaryCases :
      (family b T).boundaryMembershipCount A sigma = 0 ∨
        (family b T).boundaryMembershipCount A sigma = 1 := by
    omega
  have hcofaces := hT A sigma hsigmaA hRelevant.1
  rcases hboundaryCases with hboundaryZero | hboundaryOne
  · have hnotBoundary : ¬ LiesInReferenceBoundary b T A sigma := by
      intro hboundary
      have := (boundaryMembershipCount_eq_one_iff b T A sigma
        hsigmaA hRelevant.1).2 hboundary
      omega
    rw [if_neg hnotBoundary] at hcofaces
    omega
  · have hboundary : LiesInReferenceBoundary b T A sigma :=
      (boundaryMembershipCount_eq_one_iff b T A sigma
        hsigmaA hRelevant.1).1 hboundaryOne
    rw [if_pos hboundary] at hcofaces
    omega

/-- A geometrically non-branching finite triangulation supplies the exact
chain-simplex hypothesis consumed by Theorems 10.8--10.10. -/
theorem IsNonbranching.isChainSimplex
    (hT : IsNonbranching b T) : (family b T).IsChainSimplex :=
  (hT.isPseudoSimplex b T).isChainSimplex

/-- The exact face-coordinate obligation used by Theorems 10.9 and 10.10 is
derived from geometric face membership. -/
theorem family_face_coordinate
    (C : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigma : sigma ∈ (family b T).complex C)
    (v : (family b T).Vertex) (hv : v.1 ∈ sigma)
    {i : Fin (n + 1)} (hi : i ∈ Finset.univ \ C) :
    b.coord i v.1.1 = 0 := by
  have hsigmaData := (mem_faceComplex_iff b T C sigma).1 hsigma
  rcases hsigmaData with hsigmaEmpty | hsigmaData
  · subst sigma
    simp at hv
  · exact coord_eq_zero_of_mem_referenceFace b
      (hsigmaData.2 v.1 hv) (Finset.mem_sdiff.mp hi).2

/-- The ambient-inclusion obligation used by Theorem 10.10 is automatic for
the geometric face family. -/
theorem family_subset_full
    (C : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigma : sigma ∈ (family b T).complex C) :
    sigma ∈ (family b T).complex Finset.univ :=
  faceComplex_subset_full b T C hsigma

end GeometricTriangulation
end BeyondSperner
