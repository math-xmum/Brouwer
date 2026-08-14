import BeyondSperner.Geometry.Triangulation.Purity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Local incidence in a finite geometric triangulation

This file proves the full local incidence theorem for a finite geometric
triangulation.  Every codimension-one simplex has a top-dimensional coface
and at most two such cofaces; a simplex on the reference boundary has exactly
one, while a non-boundary simplex has exactly two.  Consequently
`IsNonbranching` is derived from `Data` rather than assumed.  No purity or
incidence hypothesis is used.
-/

namespace BeyondSperner

open Classical Set Filter Topology

namespace GeometricTriangulation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ E)
variable (T : Data b)

/-- The local convex-geometric overlap lemma behind nonbranching.  Let
`i₀` be one vertex of an affine basis and let `x` be the centroid of the
opposite face.  If `q` has positive `i₀`-coordinate, then a sufficiently
short segment from `x` towards `q` has all basis coordinates nonnegative,
has strictly positive `i₀`-coordinate, and lies in both the basis simplex
and the simplex obtained by adjoining `q` to the opposite face.

The conclusion is stated after an arbitrary affine map `f` into a vector
space.  This lets us apply the lemma to the subtype inclusion of a reference
face's affine span while keeping convex hulls in the original ambient
space. -/
theorem convexHull_overlap_of_positive_apexCoord
    {V P F I : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype I] [DecidableEq I]
    (a : AffineBasis I ℝ P) (f : P →ᵃ[ℝ] F)
    (i₀ : I) (hrest : (Finset.univ.erase i₀).Nonempty)
    (q : P) (hq : 0 < a.coord i₀ q) :
    ∃ z : P,
      0 < a.coord i₀ z ∧
      (∀ i, 0 ≤ a.coord i z) ∧
      f z ∈ convexHull ℝ (Set.range (f ∘ a)) ∧
      f z ∈ convexHull ℝ
        (insert (f q) ((f ∘ a) '' (Finset.univ.erase i₀ : Set I))) := by
  let J : Finset I := Finset.univ.erase i₀
  let x : P := J.centroid ℝ a
  let O : Set P := ⋂ i ∈ J, (a.coord i) ⁻¹' Set.Ioi 0
  have hOOpen : IsOpen O := by
    apply isOpen_biInter_finset
    intro i _
    exact isOpen_Ioi.preimage (continuous_barycentric_coord a i)
  have hJcard : 0 < J.card := Finset.card_pos.mpr hrest
  have hxO : x ∈ O := by
    dsimp only [O]
    rw [Set.mem_iInter₂]
    intro i hi
    change 0 < a.coord i x
    rw [show x = J.centroid ℝ a by rfl, a.coord_apply_centroid hi]
    exact inv_pos.mpr (Nat.cast_pos.mpr hJcard)
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  let y : ℕ → P := fun k ↦ AffineMap.lineMap x q (t k)
  have htTendsto : Tendsto t atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hyTendsto : Tendsto y atTop (nhds x) := by
    have hline : Tendsto
        (fun r : ℝ ↦ AffineMap.lineMap x q r)
          (nhds (0 : ℝ)) (nhds x) := by
      simpa using AffineMap.lineMap_continuous.tendsto (0 : ℝ)
    change Tendsto ((fun r : ℝ ↦ AffineMap.lineMap x q r) ∘ t)
      atTop (nhds x)
    exact hline.comp htTendsto
  have hyEventually : ∀ᶠ k in atTop, y k ∈ O :=
    hyTendsto.eventually (hOOpen.mem_nhds hxO)
  rw [eventually_atTop] at hyEventually
  obtain ⟨k, hk⟩ := hyEventually
  let r : ℝ := t k
  let z : P := y k
  have hrPos : 0 < r := by
    dsimp [r, t]
    positivity
  have hrLe : r ≤ 1 := by
    dsimp [r, t]
    rw [one_div]
    apply inv_le_one_of_one_le₀
    have hkNonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hzO : z ∈ O := hk k le_rfl
  have hi₀J : i₀ ∉ J := by simp [J]
  have hxCoordZero : a.coord i₀ x = 0 := by
    rw [show x = J.centroid ℝ a by rfl, Finset.centroid_def]
    exact a.coord_apply_combination_of_notMem hi₀J
      (J.sum_centroidWeights_eq_one_of_nonempty ℝ hrest)
  have hcoordLine (i : I) :
      a.coord i z =
        AffineMap.lineMap (a.coord i x) (a.coord i q) r := by
    change a.coord i (AffineMap.lineMap x q r) = _
    rw [← AffineMap.comp_apply, AffineMap.comp_lineMap]
  have hzCoordPos : 0 < a.coord i₀ z := by
    rw [hcoordLine, hxCoordZero, AffineMap.lineMap_apply_ring]
    simpa using mul_pos hrPos hq
  have hzCoords : ∀ i, 0 ≤ a.coord i z := by
    intro i
    by_cases hi : i = i₀
    · simpa [hi] using hzCoordPos.le
    · have hiJ : i ∈ J := by simp [J, hi]
      exact (show 0 < a.coord i z from
        (Set.mem_iInter₂.mp hzO i hiJ)).le
  have hsumCoords : ∑ i, a.coord i z = 1 :=
    a.sum_coord_apply_eq_one z
  have hzFirst : f z ∈ convexHull ℝ (Set.range (f ∘ a)) := by
    have hcomb := affineCombination_mem_convexHull
      (s := (Finset.univ : Finset I)) (v := f ∘ a)
      (w := fun i ↦ a.coord i z) (by simpa using hzCoords) hsumCoords
    rw [← Finset.map_affineCombination Finset.univ a
      (fun i ↦ a.coord i z) hsumCoords f] at hcomb
    simpa using hcomb
  let e : J ↪ I := Function.Embedding.subtype (fun i ↦ i ∈ J)
  have hunivMap : (Finset.univ : Finset J).map e = J := by
    ext i
    simp [e]
  have hxSubtype :
      x = (Finset.univ : Finset J).centroid ℝ (a ∘ e) := by
    calc
      x = J.centroid ℝ a := rfl
      _ = ((Finset.univ : Finset J).map e).centroid ℝ a := by
        rw [hunivMap]
      _ = (Finset.univ : Finset J).centroid ℝ (a ∘ e) :=
        (Finset.univ : Finset J).centroid_map ℝ e a
  have hJNonempty : J.Nonempty := by
    simpa [J] using hrest
  let : Nonempty J := hJNonempty.to_subtype
  have hsubNonempty : (Finset.univ : Finset J).Nonempty :=
    Finset.univ_nonempty
  have hxCommon : f x ∈ convexHull ℝ ((f ∘ a) '' (J : Set I)) := by
    let w : J → ℝ :=
      (Finset.univ : Finset J).centroidWeights ℝ
    have hwNonneg : ∀ i ∈ (Finset.univ : Finset J), 0 ≤ w i := by
      intro i _
      simp [w, Finset.centroidWeights]
    have hwSum : ∑ i ∈ (Finset.univ : Finset J), w i = 1 :=
      (Finset.univ : Finset J).sum_centroidWeights_eq_one_of_nonempty
        ℝ hsubNonempty
    have hcomb := affineCombination_mem_convexHull
      (s := (Finset.univ : Finset J)) (v := f ∘ a ∘ e) (w := w)
      hwNonneg hwSum
    have hmap :
        f ((Finset.univ : Finset J).affineCombination ℝ (a ∘ e) w) =
          (Finset.univ : Finset J).affineCombination ℝ (f ∘ a ∘ e) w :=
      Finset.map_affineCombination _ _ _ hwSum f
    rw [← hmap] at hcomb
    have hcentroid :
        (Finset.univ : Finset J).affineCombination ℝ (a ∘ e) w =
          (Finset.univ : Finset J).centroid ℝ (a ∘ e) := by
      rfl
    rw [hcentroid, ← hxSubtype] at hcomb
    apply convexHull_mono _ hcomb
    rintro _ ⟨i, rfl⟩
    exact ⟨i.1, i.2, rfl⟩
  have hqSecond : f q ∈
      convexHull ℝ (insert (f q) ((f ∘ a) '' (J : Set I))) :=
    subset_convexHull ℝ _ (Set.mem_insert _ _)
  have hxSecond : f x ∈
      convexHull ℝ (insert (f q) ((f ∘ a) '' (J : Set I))) :=
    convexHull_mono (Set.subset_insert _ _) hxCommon
  have hzSecond : f z ∈
      convexHull ℝ (insert (f q) ((f ∘ a) '' (J : Set I))) := by
    have hline := (convex_convexHull ℝ
      (insert (f q) ((f ∘ a) '' (J : Set I)))).lineMap_mem
        hxSecond hqSecond ⟨hrPos.le, hrLe⟩
    have hfline : f z = AffineMap.lineMap (f x) (f q) r := by
      change f (AffineMap.lineMap x q r) = _
      rw [← AffineMap.comp_apply, AffineMap.comp_lineMap]
    rwa [hfline]
  exact ⟨z, hzCoordPos, hzCoords, hzFirst, hzSecond⟩

/-- A barycentric coordinate of an affine basis vanishes exactly on the
affine span of the opposite face. -/
theorem coord_eq_zero_iff_mem_affineSpan_erase
    {V P I : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
    [Fintype I] [DecidableEq I]
    (a : AffineBasis I ℝ P) (i₀ : I) (q : P) :
    a.coord i₀ q = 0 ↔
      q ∈ affineSpan ℝ
        (a '' (Finset.univ.erase i₀ : Set I)) := by
  constructor
  · intro hzero
    rw [← a.affineCombination_coord_eq_self q]
    apply affineCombination_mem_affineSpan_image
      (a.sum_coord_apply_eq_one q)
    · intro i _ hi
      have hii₀ : i = i₀ := by simpa using hi
      simpa [hii₀] using hzero
  · intro hspan
    have hsum := a.sum_coord_apply_eq_one q
    exact a.ind.eq_zero_of_affineCombination_mem_affineSpan
      hsum (by simpa using hspan) (Finset.mem_univ i₀) (by simp)

/-- The affine span of a nonempty reference face is inhabited. -/
theorem referenceSpanNonempty
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty) :
    Nonempty (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
  ⟨⟨b hA.choose, mem_affineSpan ℝ <| Finset.mem_coe.mpr <|
    Finset.mem_image.mpr ⟨hA.choose, hA.choose_spec, rfl⟩⟩⟩

/-- The vertices indexed by a nonempty reference face form an affine basis
of that face's affine span.  Working in the affine-span subtype avoids any
implicit assumption that the reference face is full-dimensional in `E`. -/
noncomputable def referenceFaceAffineBasis
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    AffineBasis {i // i ∈ A} ℝ
      (affineSpan ℝ (referenceFaceVertices b A : Set E)) := by
  classical
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let i₀ : {i // i ∈ A} := ⟨hA.choose, hA.choose_spec⟩
  let p : {i // i ∈ A} → R := fun i ↦
    ⟨b i.1, by
      apply mem_affineSpan ℝ
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩)⟩
  letI : Nonempty R := referenceSpanNonempty b A hA
  refine ⟨p, ?_, ?_⟩
  · exact AffineIndependent.of_comp (AffineSubspace.subtype R) (by
      simpa [p, Function.comp_def] using
        b.ind.comp_embedding (Function.Embedding.subtype (fun i ↦ i ∈ A)))
  · apply top_unique
    intro x _
    have hmap :
        (affineSpan ℝ (Set.range p)).map (AffineSubspace.subtype R) = R := by
      rw [AffineSubspace.map_span]
      have himage :
          (AffineSubspace.subtype R) '' Set.range p =
            (referenceFaceVertices b A : Set E) := by
        ext y
        constructor
        · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
          exact Finset.mem_coe.mpr <|
            Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
        · intro hy
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
          let ii : {j // j ∈ A} := ⟨i, hi⟩
          exact ⟨p ii, Set.mem_range_self ii, rfl⟩
      rw [himage]
    have hxMap : x.1 ∈
        (affineSpan ℝ (Set.range p)).map (AffineSubspace.subtype R) := by
      rw [hmap]
      exact x.2
    rw [AffineSubspace.mem_map] at hxMap
    obtain ⟨y, hy, hyx⟩ := hxMap
    have hxy : y = x := Subtype.ext hyx
    simpa [hxy] using hy

@[simp]
theorem referenceFaceAffineBasis_apply_coe
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (i : {j // j ∈ A}) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    ((referenceFaceAffineBasis b A hA i :
      affineSpan ℝ (referenceFaceVertices b A : Set E)) : E) = b i.1 := by
  rfl

/-- Intrinsic coordinates in the affine span of a reference face are the
corresponding coordinates of the ambient affine basis. -/
theorem referenceFaceAffineBasis_coord_eq
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (i : {j // j ∈ A})
    (q : affineSpan ℝ (referenceFaceVertices b A : Set E)) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    (referenceFaceAffineBasis b A hA).coord i q = b.coord i.1 q.1 := by
  classical
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let c : AffineBasis {j // j ∈ A} ℝ R :=
    referenceFaceAffineBasis b A hA
  let f : R →ᵃ[ℝ] E := AffineSubspace.subtype R
  have hmaps : (b.coord i.1).comp f = c.coord i := by
    apply AffineMap.ext_on c.tot
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      change b.coord i.1 ((c i : R) : E) = c.coord i (c i)
      rw [referenceFaceAffineBasis_apply_coe b A hA i,
        b.coord_apply_eq, c.coord_apply_eq]
    · change b.coord i.1 ((c j : R) : E) = c.coord i (c j)
      rw [referenceFaceAffineBasis_apply_coe b A hA j,
        b.coord_apply_ne, c.coord_apply_ne]
      · exact Ne.symm hji
      · exact fun hval ↦ hji (Subtype.ext hval.symm)
  have hq := congrArg (fun g : R →ᵃ[ℝ] ℝ ↦ g q) hmaps
  simpa [c, f] using hq.symm

/-- An affine functional is recovered from its values on an affine basis
using the barycentric coordinates of that basis. -/
theorem affineMap_apply_eq_sum_coord
    {V P I : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
    [Fintype I] (a : AffineBasis I ℝ P) (L : P →ᵃ[ℝ] ℝ) (q : P) :
    L q = ∑ i, a.coord i q * L (a i) := by
  have hsum : ∑ i, a.coord i q = 1 := a.sum_coord_apply_eq_one q
  calc
    L q = L ((Finset.univ : Finset I).affineCombination ℝ a
        (fun i ↦ a.coord i q)) :=
      congrArg L (a.affineCombination_coord_eq_self q).symm
    _ = (Finset.univ : Finset I).affineCombination ℝ (L ∘ a)
        (fun i ↦ a.coord i q) :=
      Finset.map_affineCombination Finset.univ a
        (fun i ↦ a.coord i q) hsum L
    _ = ∑ i, a.coord i q * L (a i) := by
      rw [Finset.affineCombination_eq_linear_combination]
      · simp [Function.comp_apply, smul_eq_mul]
      · simp

/-- Extend an affine functional on a reference face's affine span to the
ambient vector space by its values on the reference-face affine basis. -/
noncomputable def extendAffineMapFromReferenceSpan
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    (affineSpan ℝ (referenceFaceVertices b A : Set E) →ᵃ[ℝ] ℝ) →
      E →ᵃ[ℝ] ℝ := by
  letI : Nonempty
      (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
    referenceSpanNonempty b A hA
  intro L
  let c := referenceFaceAffineBasis b A hA
  exact ∑ j, L (c j) • b.coord j.1

/-- The ambient extension agrees with the original functional everywhere
on the reference affine span. -/
theorem extendAffineMapFromReferenceSpan_apply
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    ∀ (L : affineSpan ℝ (referenceFaceVertices b A : Set E) →ᵃ[ℝ] ℝ)
      (q : affineSpan ℝ (referenceFaceVertices b A : Set E)),
      extendAffineMapFromReferenceSpan b A hA L q.1 = L q := by
  classical
  intro L q
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let c : AffineBasis {j // j ∈ A} ℝ R :=
    referenceFaceAffineBasis b A hA
  let f : R →ᵃ[ℝ] E := AffineSubspace.subtype R
  let H : E →ᵃ[ℝ] ℝ := extendAffineMapFromReferenceSpan b A hA L
  have hmaps : H.comp f = L := by
    apply AffineMap.ext_on c.tot
    rintro _ ⟨k, rfl⟩
    change (∑ j, L (c j) • b.coord j.1) ((c k : R) : E) = L (c k)
    rw [referenceFaceAffineBasis_apply_coe b A hA k]
    let ev : AddMonoidHom (E →ᵃ[ℝ] ℝ) ℝ :=
      { toFun := fun F ↦ F (b k.1)
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    change ev (∑ j, L (c j) • b.coord j.1) = L (c k)
    rw [map_sum]
    change (∑ j : {j // j ∈ A},
      L (c j) * b.coord j.1 (b k.1)) = L (c k)
    rw [Fintype.sum_eq_single k]
    · rw [b.coord_apply_eq, mul_one]
    · intro j hjk
      rw [b.coord_apply_ne, mul_zero]
      exact fun hval ↦ hjk (Subtype.ext hval)
  have hq := congrArg (fun g : R →ᵃ[ℝ] ℝ ↦ g q) hmaps
  simpa [H, f] using hq

/-- A top simplex in an induced reference-face triangulation is also an
affine basis of the reference face's affine span.  Thus its barycentric
coordinates are intrinsic to the reference face, even when that face is a
proper affine subspace of the ambient space. -/
noncomputable def topCofaceAffineBasis
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (tau : Finset T.Vertex) (htau : tau ∈ faceComplex b T A)
    (htauCard : tau.card = A.card) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    AffineBasis tau ℝ
      (affineSpan ℝ (referenceFaceVertices b A : Set E)) := by
  classical
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  letI : Nonempty R := referenceSpanNonempty b A hA
  letI : FiniteDimensional ℝ R.direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ
      (referenceFaceVertices b A).finite_toSet
  have htauNonempty : tau.Nonempty := by
    rw [← Finset.card_pos, htauCard]
    exact hA.card_pos
  have htauData :=
    ((mem_faceComplex_iff b T A tau).1 htau).resolve_left
      htauNonempty.ne_empty
  let p : tau → R := fun v ↦
    ⟨v.1.1, convexHull_subset_affineSpan
      (referenceFaceVertices b A : Set E) (htauData.2 v.1 v.2)⟩
  let e : tau ↪ realizeSimplex b T tau :=
    ⟨fun v ↦ ⟨v.1.1, Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩,
      fun v w hvw ↦ by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : realizeSimplex b T tau ↦ z.1) hvw⟩
  have hrealIndependent :
      AffineIndependent ℝ
        ((↑) : realizeSimplex b T tau → E) :=
    T.complex.indep htauData.1
  have habstractIndependent :
      AffineIndependent ℝ (fun v : tau ↦ v.1.1) := by
    change AffineIndependent ℝ
      (((↑) : realizeSimplex b T tau → E) ∘ e)
    exact hrealIndependent.comp_embedding e
  have hpIndependent : AffineIndependent ℝ p := by
    apply AffineIndependent.of_comp (AffineSubspace.subtype R)
    simpa [p, Function.comp_def] using habstractIndependent
  refine ⟨p, hpIndependent, ?_⟩
  apply hpIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  calc
    Fintype.card tau = tau.card := Fintype.card_coe tau
    _ = A.card := htauCard
    _ = Fintype.card {i // i ∈ A} := (Fintype.card_coe A).symm
    _ = Module.finrank ℝ R.direction + 1 :=
      (referenceFaceAffineBasis b A hA).card_eq_finrank_add_one

@[simp]
theorem topCofaceAffineBasis_apply_coe
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (tau : Finset T.Vertex) (htau : tau ∈ faceComplex b T A)
    (htauCard : tau.card = A.card) (v : tau) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    ((topCofaceAffineBasis b T A hA tau htau htauCard v :
      affineSpan ℝ (referenceFaceVertices b A : Set E)) : E) = v.1.1 := by
  rfl

/-- Every point of a top simplex has nonnegative intrinsic barycentric
coordinates.  The statement explicitly transports the convex hull through
the affine-span subtype, so no ambient full-dimensionality is assumed. -/
theorem topCoface_coord_nonnegative_of_mem_convexHull
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (tau : Finset T.Vertex) (htau : tau ∈ faceComplex b T A)
    (htauCard : tau.card = A.card)
    (i : tau)
    (q : affineSpan ℝ (referenceFaceVertices b A : Set E))
    (hq : q.1 ∈ convexHull ℝ (realizeSimplex b T tau : Set E)) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    0 ≤ (topCofaceAffineBasis b T A hA tau htau htauCard).coord i q := by
  classical
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let a : AffineBasis tau ℝ R :=
    topCofaceAffineBasis b T A hA tau htau htauCard
  let L : R →ᵃ[ℝ] ℝ := a.coord i
  let H : E →ᵃ[ℝ] ℝ := extendAffineMapFromReferenceSpan b A hA L
  have hverticesNonnegative :
      (realizeSimplex b T tau : Set E) ⊆ H ⁻¹' Set.Ici 0 := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    let j : tau := ⟨v, hv⟩
    have hjPoint : (a j : R).1 = v.1 :=
      topCofaceAffineBasis_apply_coe b T A hA tau htau htauCard j
    change 0 ≤ H v.1
    rw [← hjPoint, extendAffineMapFromReferenceSpan_apply b A hA L (a j)]
    by_cases hji : j = i
    · rw [hji, a.coord_apply_eq]
      norm_num
    · rw [a.coord_apply_ne (Ne.symm hji)]
  have hconvex : Convex ℝ (H ⁻¹' Set.Ici 0) :=
    (convex_Ici (0 : ℝ)).affine_preimage H
  have hHq : 0 ≤ H q.1 :=
    convexHull_min hverticesNonnegative hconvex hq
  rw [extendAffineMapFromReferenceSpan_apply b A hA L q] at hHq
  exact hHq

/-- The apex coordinate of a top coface vanishes on the convex hull of its
opposite face. -/
theorem topCoface_apexCoord_eq_zero_of_mem_opposite_convexHull
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (sigma : Finset T.Vertex) (hsigma : sigma ∈ faceComplex b T A)
    (hsigmaNonempty : sigma.Nonempty)
    (tau : Finset T.Vertex) (htau : tau ∈ faceComplex b T A)
    (htauCard : tau.card = A.card) (hsigmaTau : sigma ⊆ tau)
    (v : T.Vertex) (hvTau : v ∈ tau) (hvSigma : v ∉ sigma)
    (q : affineSpan ℝ (referenceFaceVertices b A : Set E))
    (hq : q.1 ∈ convexHull ℝ (realizeSimplex b T sigma : Set E)) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    (topCofaceAffineBasis b T A hA tau htau htauCard).coord
      ⟨v, hvTau⟩ q = 0 := by
  classical
  have hsigmaData :=
    ((mem_faceComplex_iff b T A sigma).1 hsigma).resolve_left
      hsigmaNonempty.ne_empty
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let a : AffineBasis tau ℝ R :=
    topCofaceAffineBasis b T A hA tau htau htauCard
  let i : tau := ⟨v, hvTau⟩
  let L : R →ᵃ[ℝ] ℝ := a.coord i
  let H : E →ᵃ[ℝ] ℝ := extendAffineMapFromReferenceSpan b A hA L
  have hverticesZero :
      (realizeSimplex b T sigma : Set E) ⊆ H ⁻¹' ({0} : Set ℝ) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    let j : tau := ⟨w, hsigmaTau hw⟩
    have hji : j ≠ i := by
      intro hji
      apply hvSigma
      have hwv : w = v := congrArg Subtype.val hji
      simpa [hwv] using hw
    have hjPoint : (a j : R).1 = w.1 :=
      topCofaceAffineBasis_apply_coe b T A hA tau htau htauCard j
    change H w.1 ∈ ({0} : Set ℝ)
    rw [← hjPoint, extendAffineMapFromReferenceSpan_apply b A hA L (a j)]
    simp [L, a.coord_apply_ne (Ne.symm hji)]
  have hconvexZero : Convex ℝ (H ⁻¹' ({0} : Set ℝ)) :=
    (convex_singleton (0 : ℝ)).affine_preimage H
  have hHq : H q.1 ∈ ({0} : Set ℝ) :=
    convexHull_min hverticesZero hconvexZero hq
  rw [extendAffineMapFromReferenceSpan_apply b A hA L q] at hHq
  exact hHq

/-- A top simplex of `faceComplex A` spans exactly the affine span of the
reference face `A`; in particular, it does not merely have the right number
of vertices. -/
theorem affineSpan_realize_topCoface_eq_referenceSpan
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (tau : Finset T.Vertex) (htau : tau ∈ faceComplex b T A)
    (htauCard : tau.card = A.card) :
    affineSpan ℝ (realizeSimplex b T tau : Set E) =
      affineSpan ℝ (referenceFaceVertices b A : Set E) := by
  classical
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let : FiniteDimensional ℝ R.direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ
      (referenceFaceVertices b A).finite_toSet
  have htauNonempty : tau.Nonempty := by
    rw [← Finset.card_pos, htauCard]
    exact hA.card_pos
  have htauData :=
    ((mem_faceComplex_iff b T A tau).1 htau).resolve_left
      htauNonempty.ne_empty
  let rho : Finset E := realizeSimplex b T tau
  have hrhoIndependent : AffineIndependent ℝ ((↑) : rho → E) :=
    T.complex.indep htauData.1
  have hspanLe : affineSpan ℝ (Set.range ((↑) : rho → E)) ≤ R := by
    apply affineSpan_le.mpr
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp z.2
    rw [← hvz]
    exact convexHull_subset_affineSpan
      (referenceFaceVertices b A : Set E) (htauData.2 v hv)
  have hrhoCard : Fintype.card rho = A.card := by
    rw [Fintype.card_coe]
    calc
      rho.card = tau.card := by
        simpa [rho, realizeSimplex] using
          Finset.card_image_of_injective tau Subtype.val_injective
      _ = A.card := htauCard
  have hdimension : A.card = Module.finrank ℝ R.direction + 1 := by
    calc
      A.card = Fintype.card {i // i ∈ A} := (Fintype.card_coe A).symm
      _ = Module.finrank ℝ R.direction + 1 :=
        (referenceFaceAffineBasis b A hA).card_eq_finrank_add_one
  have hspan :=
    hrhoIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
      hspanLe (hrhoCard.trans hdimension)
  simpa [rho] using hspan

/-- If `sigma` has exactly one fewer vertex than a containing simplex
`tau`, then `tau \ sigma` consists of a unique apex vertex. -/
theorem existsUnique_apex_of_subset_card_add_one
    {V : Type*} [DecidableEq V] {sigma tau : Finset V}
    (hsubset : sigma ⊆ tau) (hcard : sigma.card + 1 = tau.card) :
    ∃! v, v ∈ tau ∧ v ∉ sigma := by
  have hdiffCard : (tau \ sigma).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsubset]
    omega
  simpa using (Finset.card_eq_one_iff_existsUnique.mp hdiffCard)

theorem eq_insert_of_subset_card_add_one
    {V : Type*} [DecidableEq V] {sigma tau : Finset V} {v : V}
    (hsubset : sigma ⊆ tau) (hcard : sigma.card + 1 = tau.card)
    (hvTau : v ∈ tau) (hvSigma : v ∉ sigma) :
    tau = insert v sigma := by
  have hu := existsUnique_apex_of_subset_card_add_one hsubset hcard
  ext w
  constructor
  · intro hw
    by_cases hwSigma : w ∈ sigma
    · exact Finset.mem_insert_of_mem hwSigma
    · have hwv : w = v := hu.unique ⟨hw, hwSigma⟩ ⟨hvTau, hvSigma⟩
      simp [hwv]
  · intro hw
    rcases Finset.mem_insert.mp hw with rfl | hwSigma
    · exact hvTau
    · exact hsubset hwSigma

/-- Two distinct top cofaces of the same nonempty codimension-one face
cannot put their respective apex vertices on the same positive side of the
first coface's opposite-face hyperplane.  This is the geometric
non-overlap statement: positivity would produce a point in the relative
interiors of both simplices outside their common face, contradicting the
defining exact convex-hull intersection law. -/
theorem topCoface_apexCoord_nonpos_of_ne
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (sigma : Finset T.Vertex) (hsigmaNonempty : sigma.Nonempty)
    (tau₁ tau₂ : Finset T.Vertex)
    (htau₁ : tau₁ ∈ faceComplex b T A) (htau₁Card : tau₁.card = A.card)
    (htau₂ : tau₂ ∈ faceComplex b T A) (htau₂Card : tau₂.card = A.card)
    (hsigma₁ : sigma ⊆ tau₁) (hsigma₂ : sigma ⊆ tau₂)
    (hcodim : sigma.card + 1 = A.card)
    (v₁ v₂ : T.Vertex)
    (hv₁Tau : v₁ ∈ tau₁) (hv₁Sigma : v₁ ∉ sigma)
    (hv₂Tau : v₂ ∈ tau₂) (hv₂Sigma : v₂ ∉ sigma)
    (hne : tau₁ ≠ tau₂) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    let a := topCofaceAffineBasis b T A hA tau₁ htau₁ htau₁Card
    let q₂ : affineSpan ℝ (referenceFaceVertices b A : Set E) :=
      ⟨v₂.1, convexHull_subset_affineSpan
        (referenceFaceVertices b A : Set E)
        ((((mem_faceComplex_iff b T A tau₂).1 htau₂).resolve_left
          (by
            intro htau₂Empty
            rw [htau₂Empty] at hv₂Tau
            simp at hv₂Tau)).2 v₂ hv₂Tau)⟩
    a.coord ⟨v₁, hv₁Tau⟩ q₂ ≤ 0 := by
  classical
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let : FiniteDimensional ℝ R.direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ
      (referenceFaceVertices b A).finite_toSet
  let a : AffineBasis tau₁ ℝ R :=
    topCofaceAffineBasis b T A hA tau₁ htau₁ htau₁Card
  let f : R →ᵃ[ℝ] E := AffineSubspace.subtype R
  have haCoe (i : tau₁) : f (a i) = i.1.1 := by
    exact topCofaceAffineBasis_apply_coe b T A hA tau₁
      htau₁ htau₁Card i
  have htau₁Nonempty : tau₁.Nonempty := hsigmaNonempty.mono hsigma₁
  have htau₂Nonempty : tau₂.Nonempty := hsigmaNonempty.mono hsigma₂
  have htau₁Data :=
    ((mem_faceComplex_iff b T A tau₁).1 htau₁).resolve_left
      htau₁Nonempty.ne_empty
  have htau₂Data :=
    ((mem_faceComplex_iff b T A tau₂).1 htau₂).resolve_left
      htau₂Nonempty.ne_empty
  let q₂ : R := ⟨v₂.1, convexHull_subset_affineSpan
    (referenceFaceVertices b A : Set E) (htau₂Data.2 v₂ hv₂Tau)⟩
  let i₁ : tau₁ := ⟨v₁, hv₁Tau⟩
  have htau₁Eq : tau₁ = insert v₁ sigma :=
    eq_insert_of_subset_card_add_one hsigma₁
      (by omega) hv₁Tau hv₁Sigma
  have htau₂Eq : tau₂ = insert v₂ sigma :=
    eq_insert_of_subset_card_add_one hsigma₂
      (by omega) hv₂Tau hv₂Sigma
  have hv₁v₂ : v₁ ≠ v₂ := by
    intro hv
    apply hne
    rw [htau₁Eq, htau₂Eq, hv]
  have hinter : tau₁ ∩ tau₂ = sigma := by
    ext v
    simp [htau₁Eq, htau₂Eq, hv₁Sigma, hv₂Sigma,
      hv₁v₂]
  have hrest : (Finset.univ.erase i₁).Nonempty := by
    obtain ⟨w, hwSigma⟩ := hsigmaNonempty
    let iw : tau₁ := ⟨w, hsigma₁ hwSigma⟩
    refine ⟨iw, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ iw⟩⟩
    intro hiw
    have hwv₁ : w = v₁ := congrArg (fun z : tau₁ ↦ z.1) hiw
    exact hv₁Sigma (hwv₁ ▸ hwSigma)
  have hRange₁ : Set.range (f ∘ a) =
      (realizeSimplex b T tau₁ : Set E) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.mem_coe.mpr <|
        Finset.mem_image.mpr ⟨i.1, i.2, (haCoe i).symm⟩
    · intro hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      let i : tau₁ := ⟨v, hv⟩
      exact ⟨i, haCoe i⟩
  have hOpposite : (f ∘ a) '' (Finset.univ.erase i₁ : Set tau₁) =
      (realizeSimplex b T sigma : Set E) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hii₁ : i ≠ i₁ := by simpa using hi
      have hiSigma : i.1 ∈ sigma := by
        have hiInsert : i.1 ∈ insert v₁ sigma := by
          rw [← htau₁Eq]
          exact i.2
        rcases Finset.mem_insert.mp hiInsert with hiv₁ | hiSigma
        · exact (hii₁ (Subtype.ext hiv₁)).elim
        · exact hiSigma
      exact Finset.mem_coe.mpr <|
        Finset.mem_image.mpr ⟨i.1, hiSigma, (haCoe i).symm⟩
    · intro hy
      obtain ⟨v, hvSigma, rfl⟩ :=
        Finset.mem_image.mp (Finset.mem_coe.mp hy)
      let i : tau₁ := ⟨v, hsigma₁ hvSigma⟩
      refine ⟨i, ?_, haCoe i⟩
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ i⟩
      intro hii₁
      have hvv₁ : v = v₁ := congrArg (fun z : tau₁ ↦ z.1) hii₁
      exact hv₁Sigma (hvv₁ ▸ hvSigma)
  have hRange₂ :
      insert (f q₂) ((f ∘ a) '' (Finset.univ.erase i₁ : Set tau₁)) =
        (realizeSimplex b T tau₂ : Set E) := by
    rw [hOpposite, htau₂Eq]
    ext y
    simp [q₂, f, realizeSimplex]
  by_contra hnotNonpos
  have hpositive : 0 < a.coord i₁ q₂ := lt_of_not_ge hnotNonpos
  obtain ⟨z, hzPositive, -, hzTau₁, hzTau₂⟩ :=
    convexHull_overlap_of_positive_apexCoord a f i₁ hrest q₂ hpositive
  rw [hRange₁] at hzTau₁
  rw [hRange₂] at hzTau₂
  have hzIntersection : f z ∈
      convexHull ℝ (realizeSimplex b T tau₁ : Set E) ∩
        convexHull ℝ (realizeSimplex b T tau₂ : Set E) :=
    ⟨hzTau₁, hzTau₂⟩
  rw [T.complex.convexHull_inter_convexHull
    htau₁Data.1 htau₂Data.1] at hzIntersection
  have hRealIntersection :
      realizeSimplex b T tau₁ ∩ realizeSimplex b T tau₂ =
        realizeSimplex b T sigma := by
    ext y
    constructor
    · intro hy
      have hyParts := Finset.mem_inter.mp hy
      obtain ⟨v₁', hv₁', hv₁y⟩ := Finset.mem_image.mp hyParts.1
      obtain ⟨v₂', hv₂', hv₂y⟩ := Finset.mem_image.mp hyParts.2
      have hvEq : v₁' = v₂' := Subtype.ext (hv₁y.trans hv₂y.symm)
      apply Finset.mem_image.mpr
      refine ⟨v₁', ?_, hv₁y⟩
      rw [← hinter]
      exact Finset.mem_inter.mpr ⟨hv₁', hvEq ▸ hv₂'⟩
    · intro hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨v, hsigma₁ hv, rfl⟩,
          Finset.mem_image.mpr ⟨v, hsigma₂ hv, rfl⟩⟩
  have hSetIntersection :
      (realizeSimplex b T tau₁ : Set E) ∩
          (realizeSimplex b T tau₂ : Set E) =
        (realizeSimplex b T sigma : Set E) := by
    ext y
    simpa using congrArg (fun s : Finset E ↦ y ∈ s) hRealIntersection
  rw [hSetIntersection] at hzIntersection
  have hzSpanE : f z ∈ affineSpan ℝ (realizeSimplex b T sigma : Set E) :=
    convexHull_subset_affineSpan _ hzIntersection
  have hmapSpan :
      (affineSpan ℝ (a '' (Finset.univ.erase i₁ : Set tau₁))).map f =
        affineSpan ℝ (realizeSimplex b T sigma : Set E) := by
    rw [AffineSubspace.map_span]
    have himageComp :
        f '' (a '' (Finset.univ.erase i₁ : Set tau₁)) =
          (f ∘ a) '' (Finset.univ.erase i₁ : Set tau₁) := by
      ext y
      constructor
      · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
        exact ⟨i, hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨a i, ⟨i, hi, rfl⟩, rfl⟩
    rw [himageComp, hOpposite]
  rw [← hmapSpan, AffineSubspace.mem_map] at hzSpanE
  obtain ⟨z', hz'Span, hz'z⟩ := hzSpanE
  have hz'Eq : z' = z := Subtype.ext hz'z
  have hzZero : a.coord i₁ z = 0 :=
    (coord_eq_zero_iff_mem_affineSpan_erase a i₁ z).2 (by
      simpa [hz'Eq] using hz'Span)
  linarith

/-- Normal coordinates determined by two top cofaces of the same
codimension-one face differ by multiplication by the first coordinate of
the second apex.  This is the precise affine-algebraic version of saying
that the normal quotient is one-dimensional. -/
theorem topCoface_apexCoord_relation
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (sigma : Finset T.Vertex) (_hsigmaNonempty : sigma.Nonempty)
    (tau₀ tau₁ : Finset T.Vertex)
    (htau₀ : tau₀ ∈ faceComplex b T A) (htau₀Card : tau₀.card = A.card)
    (htau₁ : tau₁ ∈ faceComplex b T A) (htau₁Card : tau₁.card = A.card)
    (hsigma₀ : sigma ⊆ tau₀) (hsigma₁ : sigma ⊆ tau₁)
    (hcodim : sigma.card + 1 = A.card)
    (v₀ v₁ : T.Vertex)
    (hv₀Tau : v₀ ∈ tau₀) (hv₀Sigma : v₀ ∉ sigma)
    (hv₁Tau : v₁ ∈ tau₁) (hv₁Sigma : v₁ ∉ sigma) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A hA
    let a₀ := topCofaceAffineBasis b T A hA tau₀ htau₀ htau₀Card
    let a₁ := topCofaceAffineBasis b T A hA tau₁ htau₁ htau₁Card
    let i₀ : tau₀ := ⟨v₀, hv₀Tau⟩
    let i₁ : tau₁ := ⟨v₁, hv₁Tau⟩
    let q₁ : affineSpan ℝ (referenceFaceVertices b A : Set E) :=
      a₁ i₁
    ∀ q, a₀.coord i₀ q = a₀.coord i₀ q₁ * a₁.coord i₁ q := by
  classical
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let a₀ : AffineBasis tau₀ ℝ R :=
    topCofaceAffineBasis b T A hA tau₀ htau₀ htau₀Card
  let a₁ : AffineBasis tau₁ ℝ R :=
    topCofaceAffineBasis b T A hA tau₁ htau₁ htau₁Card
  let i₀ : tau₀ := ⟨v₀, hv₀Tau⟩
  let i₁ : tau₁ := ⟨v₁, hv₁Tau⟩
  let q₁ : R := a₁ i₁
  dsimp only
  have htau₀Eq : tau₀ = insert v₀ sigma :=
    eq_insert_of_subset_card_add_one hsigma₀ (by omega)
      hv₀Tau hv₀Sigma
  have htau₁Eq : tau₁ = insert v₁ sigma :=
    eq_insert_of_subset_card_add_one hsigma₁ (by omega)
      hv₁Tau hv₁Sigma
  have hmaps :
      a₀.coord i₀ = (a₀.coord i₀ q₁) • a₁.coord i₁ := by
    apply AffineMap.ext_on a₁.tot
    rintro _ ⟨j, rfl⟩
    by_cases hji₁ : j = i₁
    · subst j
      simp [q₁]
    · have hjSigma : j.1 ∈ sigma := by
        have hjInsert : j.1 ∈ insert v₁ sigma := by
          rw [← htau₁Eq]
          exact j.2
        rcases Finset.mem_insert.mp hjInsert with hjv₁ | hjSigma
        · exact (hji₁ (Subtype.ext hjv₁)).elim
        · exact hjSigma
      let k : tau₀ := ⟨j.1, hsigma₀ hjSigma⟩
      have hki₀ : k ≠ i₀ := by
        intro hki
        have hjv₀ : j.1 = v₀ := congrArg (fun z : tau₀ ↦ z.1) hki
        exact hv₀Sigma (hjv₀ ▸ hjSigma)
      have hpoints : a₁ j = a₀ k := by
        apply Subtype.ext
        calc
          ((a₁ j : R) : E) = j.1.1 :=
            topCofaceAffineBasis_apply_coe b T A hA tau₁
              htau₁ htau₁Card j
          _ = ((a₀ k : R) : E) :=
            (topCofaceAffineBasis_apply_coe b T A hA tau₀
              htau₀ htau₀Card k).symm
      calc
        a₀.coord i₀ (a₁ j) = a₀.coord i₀ (a₀ k) :=
          congrArg (a₀.coord i₀) hpoints
        _ = 0 := a₀.coord_apply_ne hki₀.symm
        _ = a₀.coord i₀ q₁ * a₁.coord i₁ (a₁ j) := by
          rw [a₁.coord_apply_ne (Ne.symm hji₁), mul_zero]
  intro q
  have hq := congrArg (fun g : R →ᵃ[ℝ] ℝ ↦ g q) hmaps
  simpa [smul_eq_mul] using hq

/-- Three pairwise distinct top cofaces cannot contain the same nonempty
codimension-one simplex.  Choosing one coface as a reference puts both
other apexes on its negative side.  The coordinate-change identity turns
the second apex positive relative to the first, contradicting the
same-positive-side non-overlap theorem. -/
theorem no_three_distinct_topCofaces_of_nonempty
    (A : Finset (Fin (n + 1)))
    (sigma : Finset T.Vertex) (hsigmaNonempty : sigma.Nonempty)
    (hcodim : sigma.card + 1 = A.card)
    (tau₀ tau₁ tau₂ : Finset T.Vertex)
    (htau₀ : tau₀ ∈ faceComplex b T A) (htau₀Card : tau₀.card = A.card)
    (htau₁ : tau₁ ∈ faceComplex b T A) (htau₁Card : tau₁.card = A.card)
    (htau₂ : tau₂ ∈ faceComplex b T A) (htau₂Card : tau₂.card = A.card)
    (hsigma₀ : sigma ⊆ tau₀) (hsigma₁ : sigma ⊆ tau₁)
    (hsigma₂ : sigma ⊆ tau₂) :
    tau₀ = tau₁ ∨ tau₀ = tau₂ ∨ tau₁ = tau₂ := by
  classical
  by_contra hdistinct
  push Not at hdistinct
  have hA : A.Nonempty := by
    apply Finset.card_pos.mp
    have hsigmaCardPos := hsigmaNonempty.card_pos
    omega
  obtain ⟨v₀, hv₀, -⟩ := existsUnique_apex_of_subset_card_add_one
    hsigma₀ (by omega)
  obtain ⟨v₁, hv₁, -⟩ := existsUnique_apex_of_subset_card_add_one
    hsigma₁ (by omega)
  obtain ⟨v₂, hv₂, -⟩ := existsUnique_apex_of_subset_card_add_one
    hsigma₂ (by omega)
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let a₀ : AffineBasis tau₀ ℝ R :=
    topCofaceAffineBasis b T A hA tau₀ htau₀ htau₀Card
  let a₁ : AffineBasis tau₁ ℝ R :=
    topCofaceAffineBasis b T A hA tau₁ htau₁ htau₁Card
  let a₂ : AffineBasis tau₂ ℝ R :=
    topCofaceAffineBasis b T A hA tau₂ htau₂ htau₂Card
  let i₀ : tau₀ := ⟨v₀, hv₀.1⟩
  let i₁ : tau₁ := ⟨v₁, hv₁.1⟩
  let i₂ : tau₂ := ⟨v₂, hv₂.1⟩
  let q₁ : R := a₁ i₁
  let q₂ : R := a₂ i₂
  have hq₁Vertex : q₁.1 = v₁.1 := by
    exact topCofaceAffineBasis_apply_coe b T A hA tau₁
      htau₁ htau₁Card i₁
  have hq₂Vertex : q₂.1 = v₂.1 := by
    exact topCofaceAffineBasis_apply_coe b T A hA tau₂
      htau₂ htau₂Card i₂
  have h₀₁raw := topCoface_apexCoord_nonpos_of_ne b T A hA sigma
    hsigmaNonempty tau₀ tau₁ htau₀ htau₀Card htau₁ htau₁Card
    hsigma₀ hsigma₁ hcodim v₀ v₁ hv₀.1 hv₀.2 hv₁.1 hv₁.2
    hdistinct.1
  have h₀₂raw := topCoface_apexCoord_nonpos_of_ne b T A hA sigma
    hsigmaNonempty tau₀ tau₂ htau₀ htau₀Card htau₂ htau₂Card
    hsigma₀ hsigma₂ hcodim v₀ v₂ hv₀.1 hv₀.2 hv₂.1 hv₂.2
    hdistinct.2.1
  have h₁₂raw := topCoface_apexCoord_nonpos_of_ne b T A hA sigma
    hsigmaNonempty tau₁ tau₂ htau₁ htau₁Card htau₂ htau₂Card
    hsigma₁ hsigma₂ hcodim v₁ v₂ hv₁.1 hv₁.2 hv₂.1 hv₂.2
    hdistinct.2.2
  have h₀₁ : a₀.coord i₀ q₁ ≤ 0 := by
    let q₁' : R :=
      ⟨v₁.1, convexHull_subset_affineSpan
        (referenceFaceVertices b A : Set E)
        ((((mem_faceComplex_iff b T A tau₁).1 htau₁).resolve_left
          (hsigmaNonempty.mono hsigma₁).ne_empty).2 v₁ hv₁.1)⟩
    have hq : q₁ = q₁' := Subtype.ext hq₁Vertex
    simpa [a₀, i₀, q₁', hq] using h₀₁raw
  have h₀₂ : a₀.coord i₀ q₂ ≤ 0 := by
    let q₂' : R :=
      ⟨v₂.1, convexHull_subset_affineSpan
        (referenceFaceVertices b A : Set E)
        ((((mem_faceComplex_iff b T A tau₂).1 htau₂).resolve_left
          (hsigmaNonempty.mono hsigma₂).ne_empty).2 v₂ hv₂.1)⟩
    have hq : q₂ = q₂' := Subtype.ext hq₂Vertex
    simpa [a₀, i₀, q₂', hq] using h₀₂raw
  have h₁₂ : a₁.coord i₁ q₂ ≤ 0 := by
    let q₂' : R :=
      ⟨v₂.1, convexHull_subset_affineSpan
        (referenceFaceVertices b A : Set E)
        ((((mem_faceComplex_iff b T A tau₂).1 htau₂).resolve_left
          (hsigmaNonempty.mono hsigma₂).ne_empty).2 v₂ hv₂.1)⟩
    have hq : q₂ = q₂' := Subtype.ext hq₂Vertex
    simpa [a₁, i₁, q₂', hq] using h₁₂raw
  have hrel : ∀ q : R,
      a₀.coord i₀ q = a₀.coord i₀ q₁ * a₁.coord i₁ q := by
    simpa [a₀, a₁, i₀, i₁, q₁] using
      (topCoface_apexCoord_relation b T A hA sigma hsigmaNonempty
        tau₀ tau₁ htau₀ htau₀Card htau₁ htau₁Card
        hsigma₀ hsigma₁ hcodim v₀ v₁ hv₀.1 hv₀.2 hv₁.1 hv₁.2)
  have hfactorNe : a₀.coord i₀ q₁ ≠ 0 := by
    intro hzero
    have hAtApex := hrel (a₀ i₀)
    rw [a₀.coord_apply_eq, hzero, zero_mul] at hAtApex
    norm_num at hAtApex
  have h₀₁neg : a₀.coord i₀ q₁ < 0 := lt_of_le_of_ne h₀₁ hfactorNe
  have hrel₀₂ : ∀ q : R,
      a₀.coord i₀ q = a₀.coord i₀ q₂ * a₂.coord i₂ q := by
    simpa [a₀, a₂, i₀, i₂, q₂] using
      (topCoface_apexCoord_relation b T A hA sigma hsigmaNonempty
        tau₀ tau₂ htau₀ htau₀Card htau₂ htau₂Card
        hsigma₀ hsigma₂ hcodim v₀ v₂ hv₀.1 hv₀.2 hv₂.1 hv₂.2)
  have hq₂Ne : a₀.coord i₀ q₂ ≠ 0 := by
    intro hzero
    have hAtApex := hrel₀₂ (a₀ i₀)
    rw [a₀.coord_apply_eq, hzero, zero_mul] at hAtApex
    norm_num at hAtApex
  have h₀₂neg : a₀.coord i₀ q₂ < 0 := lt_of_le_of_ne h₀₂ hq₂Ne
  have hrel₂ := hrel q₂
  have hpositive : 0 < a₁.coord i₁ q₂ := by
    nlinarith
  linarith

/-- Counting form of the preceding theorem: a nonempty codimension-one
simplex has at most two top-dimensional cofaces. -/
theorem cofaceCount_le_two_of_nonempty
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigmaNonempty : sigma.Nonempty)
    (hcodim : sigma.card + 1 = A.card) :
    (family b T).cofaceCount A sigma ≤ 2 := by
  classical
  rw [SimplexFamily.cofaceCount]
  let S := ((faceComplex b T A).topSimplices A.card).filter
    (fun tau ↦ sigma ⊆ tau)
  change S.card ≤ 2
  by_contra hnot
  have htwoLt : 2 < S.card := by omega
  obtain ⟨tau₀, tau₁, tau₂, htau₀S, htau₁S, htau₂S,
      hne₀₁, hne₀₂, hne₁₂⟩ :=
    Finset.two_lt_card_iff.mp htwoLt
  have topData {tau : Finset T.Vertex} (htauS : tau ∈ S) :
      tau ∈ faceComplex b T A ∧ tau.card = A.card ∧ sigma ⊆ tau := by
    have houter := Finset.mem_filter.mp htauS
    have hinner := Finset.mem_filter.mp houter.1
    exact ⟨(FiniteSimplicialComplex.mem_simplices_iff
      (faceComplex b T A) tau).mpr hinner.1, hinner.2, houter.2⟩
  have h₀ := topData htau₀S
  have h₁ := topData htau₁S
  have h₂ := topData htau₂S
  rcases no_three_distinct_topCofaces_of_nonempty b T A sigma
      hsigmaNonempty hcodim tau₀ tau₁ tau₂
      h₀.1 h₀.2.1 h₁.1 h₁.2.1 h₂.1 h₂.2.1
      h₀.2.2 h₁.2.2 h₂.2.2 with h | h | h
  · exact hne₀₁ h
  · exact hne₀₂ h
  · exact hne₁₂ h

/-- A one-vertex reference face is a point, so it admits only one
one-vertex top simplex. -/
theorem topCoface_eq_of_reference_card_eq_one
    (A : Finset (Fin (n + 1))) (hAcard : A.card = 1)
    (tau₁ tau₂ : Finset T.Vertex)
    (htau₁ : tau₁ ∈ faceComplex b T A) (htau₁Card : tau₁.card = A.card)
    (htau₂ : tau₂ ∈ faceComplex b T A) (htau₂Card : tau₂.card = A.card) :
    tau₁ = tau₂ := by
  classical
  obtain ⟨i, hAeq⟩ := Finset.card_eq_one.mp hAcard
  have htau₁One : tau₁.card = 1 := htau₁Card.trans hAcard
  have htau₂One : tau₂.card = 1 := htau₂Card.trans hAcard
  obtain ⟨v₁, htau₁Eq⟩ := Finset.card_eq_one.mp htau₁One
  obtain ⟨v₂, htau₂Eq⟩ := Finset.card_eq_one.mp htau₂One
  have htau₁Data :=
    ((mem_faceComplex_iff b T A tau₁).1 htau₁).resolve_left
      (by simp [htau₁Eq])
  have htau₂Data :=
    ((mem_faceComplex_iff b T A tau₂).1 htau₂).resolve_left
      (by simp [htau₂Eq])
  have hv₁Ref : v₁.1 ∈ referenceFace b A :=
    htau₁Data.2 v₁ (by simp [htau₁Eq])
  have hv₂Ref : v₂.1 ∈ referenceFace b A :=
    htau₂Data.2 v₂ (by simp [htau₂Eq])
  have hv₁Eq : v₁.1 = b i := by
    simpa [referenceFace, referenceFaceVertices, hAeq] using hv₁Ref
  have hv₂Eq : v₂.1 = b i := by
    simpa [referenceFace, referenceFaceVertices, hAeq] using hv₂Ref
  have hvEq : v₁ = v₂ := Subtype.ext (hv₁Eq.trans hv₂Eq.symm)
  rw [htau₁Eq, htau₂Eq, hvEq]

/-- The zero-dimensional case has at most one top coface. -/
theorem cofaceCount_le_one_of_sigma_empty
    (A : Finset (Fin (n + 1)))
    (hcodim : (∅ : Finset T.Vertex).card + 1 = A.card) :
    (family b T).cofaceCount A ∅ ≤ 1 := by
  classical
  have hAcard : A.card = 1 := by simpa using hcodim.symm
  rw [SimplexFamily.cofaceCount]
  let S := ((faceComplex b T A).topSimplices A.card).filter
    (fun tau ↦ (∅ : Finset T.Vertex) ⊆ tau)
  change S.card ≤ 1
  by_contra hnot
  have honeLt : 1 < S.card := by omega
  obtain ⟨tau₁, tau₂, htau₁S, htau₂S, hne⟩ :=
    Finset.one_lt_card_iff.mp honeLt
  have topData {tau : Finset T.Vertex} (htauS : tau ∈ S) :
      tau ∈ faceComplex b T A ∧ tau.card = A.card := by
    have houter := Finset.mem_filter.mp htauS
    have hinner := Finset.mem_filter.mp houter.1
    exact ⟨(FiniteSimplicialComplex.mem_simplices_iff
      (faceComplex b T A) tau).mpr hinner.1, hinner.2⟩
  have h₁ := topData htau₁S
  have h₂ := topData htau₂S
  exact hne (topCoface_eq_of_reference_card_eq_one b T A hAcard
    tau₁ tau₂ h₁.1 h₁.2 h₂.1 h₂.2)

/-- Every codimension-one simplex, including the zero-dimensional edge
case, has at most two top cofaces. -/
theorem cofaceCount_le_two
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hcodim : sigma.card + 1 = A.card) :
    (family b T).cofaceCount A sigma ≤ 2 := by
  rcases sigma.eq_empty_or_nonempty with rfl | hsigmaNonempty
  · exact (cofaceCount_le_one_of_sigma_empty b T A hcodim).trans (by omega)
  · exact cofaceCount_le_two_of_nonempty b T A sigma hsigmaNonempty hcodim

/-- On a nonempty codimension-one reference boundary face, two top
cofaces containing the same simplex coincide.  The missing reference
coordinate is strictly positive at each apex; comparing it with the first
coface's intrinsic normal coordinate puts the second apex on the positive
side, where geometric non-overlap forces equality. -/
theorem topCoface_eq_of_liesInReferenceBoundary_of_nonempty
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigmaA : sigma ∈ faceComplex b T A)
    (hsigmaNonempty : sigma.Nonempty)
    (hcodim : sigma.card + 1 = A.card)
    (hboundary : LiesInReferenceBoundary b T A sigma)
    (tau₁ tau₂ : Finset T.Vertex)
    (htau₁ : tau₁ ∈ faceComplex b T A) (htau₁Card : tau₁.card = A.card)
    (htau₂ : tau₂ ∈ faceComplex b T A) (htau₂Card : tau₂.card = A.card)
    (hsigma₁ : sigma ⊆ tau₁) (hsigma₂ : sigma ⊆ tau₂) :
    tau₁ = tau₂ := by
  classical
  by_contra hne
  obtain ⟨B, hBindex, hsigmaLiesB⟩ := hboundary
  have hBdata := Finset.mem_filter.mp hBindex
  have hBA : B ⊆ A := Finset.mem_powerset.mp hBdata.1
  have hBcard : B.card + 1 = A.card := hBdata.2
  have hsigmaCardB : sigma.card = B.card := by omega
  have hdiffCard : (A \ B).card = 1 := by
    rw [Finset.card_sdiff_of_subset hBA]
    omega
  obtain ⟨k, hdiffEq⟩ := Finset.card_eq_one.mp hdiffCard
  have hkDiff : k ∈ A \ B := by simp [hdiffEq]
  have hkA : k ∈ A := (Finset.mem_sdiff.mp hkDiff).1
  have hkB : k ∉ B := (Finset.mem_sdiff.mp hkDiff).2
  have hBErase : B = A.erase k := by
    ext j
    constructor
    · intro hjB
      exact Finset.mem_erase.mpr ⟨fun hjk ↦ hkB (hjk ▸ hjB), hBA hjB⟩
    · intro hjErase
      have hj := Finset.mem_erase.mp hjErase
      by_contra hjB
      have hjDiff : j ∈ A \ B := Finset.mem_sdiff.mpr ⟨hj.2, hjB⟩
      have hjk : j = k := by simpa [hdiffEq] using hjDiff
      exact hj.1 hjk
  have hA : A.Nonempty := ⟨k, hkA⟩
  have hsigmaData :=
    ((mem_faceComplex_iff b T A sigma).1 hsigmaA).resolve_left
      hsigmaNonempty.ne_empty
  obtain ⟨v₁, hv₁, -⟩ := existsUnique_apex_of_subset_card_add_one
    hsigma₁ (by omega)
  obtain ⟨v₂, hv₂, -⟩ := existsUnique_apex_of_subset_card_add_one
    hsigma₂ (by omega)
  have htau₁Nonempty : tau₁.Nonempty := hsigmaNonempty.mono hsigma₁
  have htau₂Nonempty : tau₂.Nonempty := hsigmaNonempty.mono hsigma₂
  have htau₁Data :=
    ((mem_faceComplex_iff b T A tau₁).1 htau₁).resolve_left
      htau₁Nonempty.ne_empty
  have htau₂Data :=
    ((mem_faceComplex_iff b T A tau₂).1 htau₂).resolve_left
      htau₂Nonempty.ne_empty
  have htau₁Eq : tau₁ = insert v₁ sigma :=
    eq_insert_of_subset_card_add_one hsigma₁ (by omega) hv₁.1 hv₁.2
  have htau₂Eq : tau₂ = insert v₂ sigma :=
    eq_insert_of_subset_card_add_one hsigma₂ (by omega) hv₂.1 hv₂.2
  have apexCoordPositive
      (tau : Finset T.Vertex) (htau : tau ∈ faceComplex b T A)
      (htauCard : tau.card = A.card) (htauData :
        realizeSimplex b T tau ∈ T.complex.faces ∧
          LiesInReferenceFace b T A tau)
      (v : T.Vertex) (hvTau : v ∈ tau) (hvSigma : v ∉ sigma)
      (hsigmaTau : sigma ⊆ tau) :
      0 < b.coord k v.1 := by
    have hnonnegative : 0 ≤ b.coord k v.1 :=
      coord_nonnegative_of_mem_geometric_face b T htauData.1
        (by exact Finset.mem_image.mpr ⟨v, hvTau, rfl⟩) k
    apply lt_of_le_of_ne hnonnegative
    intro hzero
    have hvRefB : v.1 ∈ referenceFace b B := by
      apply (mem_referenceFace_iff_coord b B v.1).2
      constructor
      · intro j
        exact coord_nonnegative_of_mem_geometric_face b T htauData.1
          (Finset.mem_image.mpr ⟨v, hvTau, rfl⟩) j
      · intro j hjB
        by_cases hjA : j ∈ A
        · have hjk : j = k := by
            by_contra hjk
            apply hjB
            rw [hBErase]
            exact Finset.mem_erase.mpr ⟨hjk, hjA⟩
          simpa [hjk] using hzero.symm
        · exact coord_eq_zero_of_mem_referenceFace b
            (htauData.2 v hvTau) hjA
    have htauLiesB : LiesInReferenceFace b T B tau := by
      intro w hwTau
      have htauEq : tau = insert v sigma :=
        eq_insert_of_subset_card_add_one hsigmaTau (by omega)
          hvTau hvSigma
      rw [htauEq] at hwTau
      rcases Finset.mem_insert.mp hwTau with rfl | hwSigma
      · exact hvRefB
      · exact hsigmaLiesB w hwSigma
    have htauB : tau ∈ faceComplex b T B :=
      (mem_faceComplex_iff b T B tau).2 (Or.inr ⟨htauData.1, htauLiesB⟩)
    have hdim := faceComplex_card_le b T B htauB
    omega
  have hv₁Pos : 0 < b.coord k v₁.1 :=
    apexCoordPositive tau₁ htau₁ htau₁Card htau₁Data
      v₁ hv₁.1 hv₁.2 hsigma₁
  have hv₂Pos : 0 < b.coord k v₂.1 :=
    apexCoordPositive tau₂ htau₂ htau₂Card htau₂Data
      v₂ hv₂.1 hv₂.2 hsigma₂
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let : FiniteDimensional ℝ R.direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ
      (referenceFaceVertices b A).finite_toSet
  let f : R →ᵃ[ℝ] E := AffineSubspace.subtype R
  let a₁ : AffineBasis tau₁ ℝ R :=
    topCofaceAffineBasis b T A hA tau₁ htau₁ htau₁Card
  let i₁ : tau₁ := ⟨v₁, hv₁.1⟩
  let q₂ : R := ⟨v₂.1, convexHull_subset_affineSpan
    (referenceFaceVertices b A : Set E) (htau₂Data.2 v₂ hv₂.1)⟩
  let H : R →ᵃ[ℝ] ℝ := (b.coord k).comp f
  have hmaps : H = (b.coord k v₁.1) • a₁.coord i₁ := by
    apply AffineMap.ext_on a₁.tot
    rintro _ ⟨j, rfl⟩
    by_cases hji₁ : j = i₁
    · subst j
      change b.coord k ((a₁ i₁ : R) : E) =
        b.coord k v₁.1 * a₁.coord i₁ (a₁ i₁)
      rw [topCofaceAffineBasis_apply_coe b T A hA tau₁
        htau₁ htau₁Card i₁, a₁.coord_apply_eq]
      have hi₁val : i₁.1 = v₁ := rfl
      rw [hi₁val, mul_one]
    · have hjSigma : j.1 ∈ sigma := by
        have hjInsert : j.1 ∈ insert v₁ sigma := by
          rw [← htau₁Eq]
          exact j.2
        rcases Finset.mem_insert.mp hjInsert with hjv₁ | hjSigma
        · exact (hji₁ (Subtype.ext hjv₁)).elim
        · exact hjSigma
      have hjRefB : j.1.1 ∈ referenceFace b B :=
        hsigmaLiesB j.1 hjSigma
      have hcoordZero : b.coord k j.1.1 = 0 :=
        coord_eq_zero_of_mem_referenceFace b hjRefB hkB
      have hbasisZero : a₁.coord i₁ (a₁ j) = 0 :=
        a₁.coord_apply_ne (Ne.symm hji₁)
      change b.coord k ((a₁ j : R) : E) =
        b.coord k v₁.1 * a₁.coord i₁ (a₁ j)
      rw [topCofaceAffineBasis_apply_coe b T A hA tau₁
        htau₁ htau₁Card j, hcoordZero, hbasisZero, mul_zero]
  have hq := congrArg (fun g : R →ᵃ[ℝ] ℝ ↦ g q₂) hmaps
  have hpositive : 0 < a₁.coord i₁ q₂ := by
    change b.coord k v₂.1 =
      b.coord k v₁.1 * a₁.coord i₁ q₂ at hq
    nlinarith
  have hnonposRaw := topCoface_apexCoord_nonpos_of_ne b T A hA sigma
    hsigmaNonempty tau₁ tau₂ htau₁ htau₁Card htau₂ htau₂Card
    hsigma₁ hsigma₂ hcodim v₁ v₂ hv₁.1 hv₁.2 hv₂.1 hv₂.2 hne
  have hnonpos : a₁.coord i₁ q₂ ≤ 0 := by
    simpa [a₁, i₁, q₂] using hnonposRaw
  linarith

/-- If an affinely independent set has one fewer vertex than a reference
face, some reference vertex lies outside its affine span. -/
theorem exists_referenceFaceVertex_not_mem_affineSpan
    (A : Finset (Fin (n + 1))) {s : Finset E}
    (hcard : s.card + 1 = A.card) :
    ∃ q ∈ referenceFaceVertices b A,
      q ∉ affineSpan ℝ (s : Set E) := by
  let gamma : Finset E := referenceFaceVertices b A
  have hgammaIndependent :
      AffineIndependent ℝ ((↑) : gamma → E) := by
    apply (b.ind.range).mono
    intro q hq
    change q ∈ gamma at hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Set.mem_range_self i
  by_contra hnone
  push Not at hnone
  have hsubset : (gamma : Set E) ⊆ affineSpan ℝ (s : Set E) := by
    intro q hq
    exact hnone q hq
  have hle := hgammaIndependent.card_le_card_of_subset_affineSpan hsubset
  have hgammaCard : gamma.card = A.card := by
    simpa [gamma, referenceFaceVertices] using
      Finset.card_image_of_injective A b.ind.injective
  omega

/-- The union of all geometric simplices which do not contain `s`.  Its
complement is a genuine open neighborhood of the centroid of `s`. -/
noncomputable def nonCofaceRegion (s : Finset E) : Set E :=
  ⋃ u ∈ (faces_finite b T).toFinset.filter (fun u ↦ ¬s ⊆ u),
    convexHull ℝ (u : Set E)

theorem isClosed_nonCofaceRegion (s : Finset E) :
    IsClosed (nonCofaceRegion b T s) := by
  apply isClosed_biUnion_finset
  intro u _
  exact u.finite_toSet.isClosed_convexHull ℝ

/-- The indexed centroid of a geometric face avoids every simplex which
does not contain that face.  This is a local consequence of the defining
convex-hull intersection property of a geometric simplicial complex. -/
theorem indexedCentroid_not_mem_nonCofaceRegion
    {s : Finset E} (hs : s ∈ T.complex.faces) :
    (Finset.univ : Finset s).centroid ℝ ((↑) : s → E) ∉
      nonCofaceRegion b T s := by
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
  intro hxBad
  rw [nonCofaceRegion] at hxBad
  obtain ⟨u, hxBad⟩ := Set.mem_iUnion.mp hxBad
  obtain ⟨huStored, hxHullU⟩ := Set.mem_iUnion.mp hxBad
  have huData : u ∈ T.complex.faces ∧ ¬s ⊆ u := by
    have huFilter := Finset.mem_filter.mp huStored
    exact ⟨by simpa using huFilter.1, huFilter.2⟩
  apply huData.2
  apply subset_of_indexed_centroid_mem_affineSpan hsNonempty
      (T.complex.indep hs)
  apply convexHull_subset_affineSpan (s ∩ u : Set E)
  rw [← T.complex.convexHull_inter_convexHull hs huData.1]
  exact ⟨hxHullS, hxHullU⟩

/-- A nonempty codimension-one simplex in an induced reference-face
complex has a top-dimensional coface in that same induced complex. -/
theorem exists_top_coface_of_nonempty
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigma : sigma ∈ faceComplex b T A) (hsigmaNonempty : sigma.Nonempty)
    (hcard : sigma.card + 1 = A.card) :
    ∃ tau : Finset T.Vertex,
      tau ∈ faceComplex b T A ∧ tau.card = A.card ∧ sigma ⊆ tau := by
  have hsigmaData :=
    ((mem_faceComplex_iff b T A sigma).1 hsigma).resolve_left
      hsigmaNonempty.ne_empty
  let s : Finset E := realizeSimplex b T sigma
  have hsFace : s ∈ T.complex.faces := hsigmaData.1
  have hsCard : s.card = sigma.card := by
    simpa [s, realizeSimplex] using
      Finset.card_image_of_injective sigma Subtype.val_injective
  let x : E :=
    (Finset.univ : Finset s).centroid ℝ ((↑) : s → E)
  have hsNonempty : s.Nonempty := T.complex.nonempty_of_mem_faces hsFace
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
  have hxReference : x ∈ referenceFace b A := by
    apply convexHull_min _
        (convex_convexHull ℝ (referenceFaceVertices b A : Set E)) hxHullS
    intro y hy
    change y ∈ realizeSimplex b T sigma at hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact hsigmaData.2 v hv
  obtain ⟨q, hqVertex, hqSpan⟩ :=
    exists_referenceFaceVertex_not_mem_affineSpan b A (s := s)
      (by omega)
  have hqReference : q ∈ referenceFace b A :=
    subset_convexHull ℝ (referenceFaceVertices b A : Set E) hqVertex
  let O : Set E := (nonCofaceRegion b T s)ᶜ
  have hOOpen : IsOpen O := (isClosed_nonCofaceRegion b T s).isOpen_compl
  have hxO : x ∈ O := by
    exact indexedCentroid_not_mem_nonCofaceRegion b T hsFace
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  let y : ℕ → E := fun k ↦ AffineMap.lineMap x q (t k)
  have htTendsto : Tendsto t atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hyTendsto : Tendsto y atTop (𝓝 x) := by
    have hline : Tendsto
        (fun r : ℝ ↦ AffineMap.lineMap x q r) (𝓝 (0 : ℝ)) (𝓝 x) := by
      have hcontinuous : Continuous
          (fun r : ℝ ↦ AffineMap.lineMap x q r) :=
        AffineMap.lineMap_continuous
      simpa using hcontinuous.tendsto (0 : ℝ)
    change Tendsto ((fun r : ℝ ↦ AffineMap.lineMap x q r) ∘ t)
      atTop (𝓝 x)
    exact hline.comp htTendsto
  have hyEventually : ∀ᶠ k in atTop, y k ∈ O :=
    hyTendsto.eventually (hOOpen.mem_nhds hxO)
  rw [eventually_atTop] at hyEventually
  obtain ⟨k, hk⟩ := hyEventually
  let r : ℝ := t k
  let z : E := y k
  have hrPos : 0 < r := by
    dsimp [r, t]
    positivity
  have hrLe : r ≤ 1 := by
    dsimp [r, t]
    rw [one_div]
    apply inv_le_one_of_one_le₀
    have hkNonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hzO : z ∈ O := hk k le_rfl
  have hzReference : z ∈ referenceFace b A := by
    exact (convex_convexHull ℝ (referenceFaceVertices b A : Set E)).lineMap_mem
      hxReference hqReference ⟨hrPos.le, hrLe⟩
  have hxSpan : x ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan (s : Set E) hxHullS
  have hzNotSpan : z ∉ affineSpan ℝ (s : Set E) := by
    intro hzSpan
    have hrecover := AffineMap.lineMap_mem r⁻¹ hxSpan hzSpan
    have hrNe : r ≠ 0 := ne_of_gt hrPos
    change AffineMap.lineMap x q r ∈ affineSpan ℝ (s : Set E) at hzSpan
    rw [show z = AffineMap.lineMap x q r by rfl] at hrecover
    rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hrNe,
      AffineMap.lineMap_apply_one] at hrecover
    exact hqSpan hrecover
  obtain ⟨tau, htau, hzHullTau⟩ :=
    exists_faceComplex_simplex_containing b T A hzReference
  have htauNonempty : tau.Nonempty := by
    by_contra htauEmpty
    rw [Finset.not_nonempty_iff_eq_empty.mp htauEmpty] at hzHullTau
    simp [realizeSimplex] at hzHullTau
  have htauData :=
    ((mem_faceComplex_iff b T A tau).1 htau).resolve_left
      htauNonempty.ne_empty
  have hsRealizedSubset : s ⊆ realizeSimplex b T tau := by
    by_contra hnotSubset
    apply hzO
    rw [nonCofaceRegion]
    apply Set.mem_iUnion.mpr
    refine ⟨realizeSimplex b T tau, Set.mem_iUnion.mpr ⟨?_, hzHullTau⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨(Set.Finite.mem_toFinset (faces_finite b T)).mpr htauData.1, ?_⟩
    exact hnotSubset
  have hsigmaSubset : sigma ⊆ tau := by
    intro v hv
    have hvRealized : v.1 ∈ s := by
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hvTau := hsRealizedSubset hvRealized
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hvTau
    have hwEq : w = v := Subtype.ext hwv
    simpa [hwEq] using hw
  have hsigmaProper : sigma ⊂ tau := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsigmaSubset, ?_⟩
    intro hsigmaEq
    apply hzNotSpan
    apply convexHull_subset_affineSpan (s : Set E)
    simpa [s, hsigmaEq] using hzHullTau
  have htauCardLe := faceComplex_card_le b T A htau
  have htauCardGt := Finset.card_lt_card hsigmaProper
  refine ⟨tau, htau, ?_, hsigmaSubset⟩
  omega

/-- Every codimension-one simplex, including the empty simplex in a
zero-dimensional reference face, has at least one top-dimensional coface. -/
theorem exists_top_coface
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigma : sigma ∈ faceComplex b T A)
    (hcard : sigma.card + 1 = A.card) :
    ∃ tau : Finset T.Vertex,
      tau ∈ faceComplex b T A ∧ tau.card = A.card ∧ sigma ⊆ tau := by
  rcases sigma.eq_empty_or_nonempty with rfl | hsigmaNonempty
  · have hAcard : A.card = 1 := by simpa using hcard.symm
    obtain ⟨i, hiA⟩ : ∃ i, i ∈ A := by
      exact A.card_pos.mp (by omega)
    have hbiReference : b i ∈ referenceFace b A :=
      subset_convexHull ℝ (referenceFaceVertices b A : Set E)
        (Finset.mem_image.mpr ⟨i, hiA, rfl⟩)
    obtain ⟨tau, htau, hbiHull⟩ :=
      exists_faceComplex_simplex_containing b T A hbiReference
    have htauNonempty : tau.Nonempty := by
      by_contra htauEmpty
      rw [Finset.not_nonempty_iff_eq_empty.mp htauEmpty] at hbiHull
      simp [realizeSimplex] at hbiHull
    have htauLe := faceComplex_card_le b T A htau
    refine ⟨tau, htau, ?_, Finset.empty_subset tau⟩
    rw [hAcard] at htauLe ⊢
    exact Nat.le_antisymm htauLe (Finset.one_le_card.mpr htauNonempty)
  · exact exists_top_coface_of_nonempty b T A sigma hsigma hsigmaNonempty hcard

/-- In counting form, every relevant codimension-one simplex has at least
one top-dimensional coface. -/
theorem one_le_cofaceCount
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigma : sigma ∈ faceComplex b T A)
    (hcard : sigma.card + 1 = A.card) :
    1 ≤ (family b T).cofaceCount A sigma := by
  obtain ⟨tau, htau, htauCard, hsigmaTau⟩ :=
    exists_top_coface b T A sigma hsigma hcard
  rw [SimplexFamily.cofaceCount]
  apply Finset.one_le_card.mpr
  refine ⟨tau, Finset.mem_filter.mpr ⟨?_, hsigmaTau⟩⟩
  apply Finset.mem_filter.mpr
  exact ⟨(FiniteSimplicialComplex.mem_simplices_iff
    (faceComplex b T A) tau).mpr htau, htauCard⟩

/-- A codimension-one simplex on the geometric reference boundary has
exactly one top coface. -/
theorem cofaceCount_eq_one_of_liesInReferenceBoundary
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigmaA : sigma ∈ faceComplex b T A)
    (hcodim : sigma.card + 1 = A.card)
    (hboundary : LiesInReferenceBoundary b T A sigma) :
    (family b T).cofaceCount A sigma = 1 := by
  have honeLe := one_le_cofaceCount b T A sigma hsigmaA hcodim
  have hleOne : (family b T).cofaceCount A sigma ≤ 1 := by
    rcases sigma.eq_empty_or_nonempty with rfl | hsigmaNonempty
    · exact cofaceCount_le_one_of_sigma_empty b T A hcodim
    · classical
      rw [SimplexFamily.cofaceCount, Finset.card_le_one]
      intro tau₁ htau₁S tau₂ htau₂S
      have topData {tau : Finset T.Vertex}
          (htauS : tau ∈
            ((faceComplex b T A).topSimplices A.card).filter
              (fun tau ↦ sigma ⊆ tau)) :
          tau ∈ faceComplex b T A ∧ tau.card = A.card ∧ sigma ⊆ tau := by
        have houter := Finset.mem_filter.mp htauS
        have hinner := Finset.mem_filter.mp houter.1
        exact ⟨(FiniteSimplicialComplex.mem_simplices_iff
          (faceComplex b T A) tau).mpr hinner.1,
          hinner.2, houter.2⟩
      have h₁ := topData htau₁S
      have h₂ := topData htau₂S
      exact topCoface_eq_of_liesInReferenceBoundary_of_nonempty b T
        A sigma hsigmaA hsigmaNonempty hcodim hboundary
        tau₁ tau₂ h₁.1 h₁.2.1 h₂.1 h₂.2.1 h₁.2.2 h₂.2.2
  omega

/-- Without yet classifying boundary versus interior, the local geometric
arguments already force every codimension-one coface count to be either
one or two. -/
theorem cofaceCount_eq_one_or_two
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigmaA : sigma ∈ faceComplex b T A)
    (hcodim : sigma.card + 1 = A.card) :
    (family b T).cofaceCount A sigma = 1 ∨
      (family b T).cofaceCount A sigma = 2 := by
  have hlo := one_le_cofaceCount b T A sigma hsigmaA hcodim
  have hhi := cofaceCount_le_two b T A sigma hcodim
  omega

/-- If the apex coordinate of one top coface is nonnegative on the whole
reference simplex, then its opposite codimension-one face lies in a
codimension-one reference face.  This is the supporting-hyperplane half of
the interior-incidence argument. -/
theorem liesInReferenceBoundary_of_no_negative_topCofaceCoord
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigmaA : sigma ∈ faceComplex b T A)
    (hsigmaNonempty : sigma.Nonempty)
    (hcodim : sigma.card + 1 = A.card)
    (tau : Finset T.Vertex)
    (htau : tau ∈ faceComplex b T A) (htauCard : tau.card = A.card)
    (hsigmaTau : sigma ⊆ tau)
    (v : T.Vertex) (hvTau : v ∈ tau) (hvSigma : v ∉ sigma)
    (hnoNegative :
      letI : Nonempty
          (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
        referenceSpanNonempty b A (by
          apply Finset.card_pos.mp
          have := hsigmaNonempty.card_pos
          omega)
      let a := topCofaceAffineBasis b T A (by
          apply Finset.card_pos.mp
          have := hsigmaNonempty.card_pos
          omega) tau htau htauCard
      ¬ ∃ q : affineSpan ℝ (referenceFaceVertices b A : Set E),
          q.1 ∈ referenceFace b A ∧
            a.coord ⟨v, hvTau⟩ q < 0) :
    LiesInReferenceBoundary b T A sigma := by
  classical
  have hA : A.Nonempty := by
    apply Finset.card_pos.mp
    have := hsigmaNonempty.card_pos
    omega
  have hsigmaData :=
    ((mem_faceComplex_iff b T A sigma).1 hsigmaA).resolve_left
      hsigmaNonempty.ne_empty
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let c : AffineBasis {j // j ∈ A} ℝ R :=
    referenceFaceAffineBasis b A hA
  let a : AffineBasis tau ℝ R :=
    topCofaceAffineBasis b T A hA tau htau htauCard
  let i : tau := ⟨v, hvTau⟩
  let L : R →ᵃ[ℝ] ℝ := a.coord i
  have hno : ¬ ∃ q : R,
      q.1 ∈ referenceFace b A ∧ L q < 0 := by
    simpa [R, a, i, L] using hnoNegative
  have hLNonnegative (q : R) (hq : q.1 ∈ referenceFace b A) :
      0 ≤ L q := by
    exact le_of_not_gt fun hqNeg ↦ hno ⟨q, hq, hqNeg⟩
  have hLsigma (w : T.Vertex) (hw : w ∈ sigma) :
      L ⟨w.1, convexHull_subset_affineSpan
        (referenceFaceVertices b A : Set E) (hsigmaData.2 w hw)⟩ = 0 := by
    let j : tau := ⟨w, hsigmaTau hw⟩
    have hji : j ≠ i := by
      intro hji
      apply hvSigma
      have hwv : w = v := congrArg Subtype.val hji
      simpa [hwv] using hw
    have hpoints :
        a j = ⟨w.1, convexHull_subset_affineSpan
          (referenceFaceVertices b A : Set E) (hsigmaData.2 w hw)⟩ := by
      apply Subtype.ext
      exact topCofaceAffineBasis_apply_coe b T A hA tau
        htau htauCard j
    calc
      L ⟨w.1, convexHull_subset_affineSpan
          (referenceFaceVertices b A : Set E) (hsigmaData.2 w hw)⟩ =
          L (a j) := congrArg L hpoints.symm
      _ = 0 := a.coord_apply_ne (Ne.symm hji)
  let e : {j // j ∈ A} ↪ Fin (n + 1) :=
    Function.Embedding.subtype (fun j ↦ j ∈ A)
  let Z : Finset {j // j ∈ A} :=
    Finset.univ.filter (fun j ↦ L (c j) = 0)
  let B : Finset (Fin (n + 1)) := Z.map e
  have hBA : B ⊆ A := by
    intro k hkB
    obtain ⟨j, hjZ, hjk⟩ := Finset.mem_map.mp hkB
    rw [← hjk]
    exact j.2
  have hBNe : B ≠ A := by
    intro hBAEq
    have hLbasisZero (j : {k // k ∈ A}) : L (c j) = 0 := by
      have hjB : j.1 ∈ B := by
        rw [hBAEq]
        exact j.2
      obtain ⟨k, hkZ, hkj⟩ := Finset.mem_map.mp hjB
      have hkj' : k = j := Subtype.ext hkj
      subst k
      exact (Finset.mem_filter.mp hkZ).2
    have hLapexZero : L (a i) = 0 := by
      rw [affineMap_apply_eq_sum_coord c L (a i)]
      simp [hLbasisZero]
    have hLapexOne : L (a i) = 1 := by
      exact a.coord_apply_eq i
    linarith
  have hsigmaLiesB : LiesInReferenceFace b T B sigma := by
    intro w hw
    apply (mem_referenceFace_iff_coord b B w.1).2
    constructor
    · intro k
      exact coord_nonnegative_of_mem_geometric_face b T hsigmaData.1
        (Finset.mem_image.mpr ⟨w, hw, rfl⟩) k
    · intro k hkB
      by_cases hkA : k ∈ A
      · let j : {r // r ∈ A} := ⟨k, hkA⟩
        have hcRef : (c j).1 ∈ referenceFace b A := by
          apply subset_convexHull ℝ (referenceFaceVertices b A : Set E)
          rw [referenceFaceAffineBasis_apply_coe b A hA j]
          exact Finset.mem_image.mpr ⟨k, hkA, rfl⟩
        have hLjNonnegative : 0 ≤ L (c j) :=
          hLNonnegative (c j) hcRef
        have hLjNe : L (c j) ≠ 0 := by
          intro hLjZero
          apply hkB
          apply Finset.mem_map.mpr
          refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLjZero⟩, rfl⟩
        have hLjPositive : 0 < L (c j) :=
          lt_of_le_of_ne hLjNonnegative (Ne.symm hLjNe)
        let q : R :=
          ⟨w.1, convexHull_subset_affineSpan
            (referenceFaceVertices b A : Set E) (hsigmaData.2 w hw)⟩
        have hLq : L q = 0 := hLsigma w hw
        have htermsNonnegative :
            ∀ r ∈ (Finset.univ : Finset {r // r ∈ A}),
              0 ≤ c.coord r q * L (c r) := by
          intro r _
          apply mul_nonneg
          · rw [referenceFaceAffineBasis_coord_eq b A hA r q]
            exact coord_nonnegative_of_mem_geometric_face b T hsigmaData.1
              (Finset.mem_image.mpr ⟨w, hw, rfl⟩) r.1
          · have hcrRef : (c r).1 ∈ referenceFace b A := by
              apply subset_convexHull ℝ
                (referenceFaceVertices b A : Set E)
              rw [referenceFaceAffineBasis_apply_coe b A hA r]
              exact Finset.mem_image.mpr ⟨r.1, r.2, rfl⟩
            exact hLNonnegative (c r) hcrRef
        have hsumZero : ∑ r, c.coord r q * L (c r) = 0 := by
          rw [← affineMap_apply_eq_sum_coord c L q]
          exact hLq
        have htermZero : c.coord j q * L (c j) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg htermsNonnegative).1
            hsumZero j (Finset.mem_univ j)
        have hcZero : c.coord j q = 0 :=
          (mul_eq_zero.mp htermZero).resolve_right hLjNe
        rw [referenceFaceAffineBasis_coord_eq b A hA j q] at hcZero
        exact hcZero
      · exact coord_eq_zero_of_mem_referenceFace b
          (hsigmaData.2 w hw) hkA
  have hsigmaB : sigma ∈ faceComplex b T B :=
    (mem_faceComplex_iff b T B sigma).2
      (Or.inr ⟨hsigmaData.1, hsigmaLiesB⟩)
  have hBcardLower := faceComplex_card_le b T B hsigmaB
  have hBcardUpper : B.card < A.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hBA, hBNe⟩)
  refine ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBA, ?_⟩,
    hsigmaLiesB⟩
  omega

/-- For a non-boundary codimension-one face, every chosen top coface has a
reference-simplex point strictly on the negative side of its opposite-face
hyperplane. -/
theorem exists_referenceFace_point_negative_topCofaceCoord
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigmaA : sigma ∈ faceComplex b T A)
    (hsigmaNonempty : sigma.Nonempty)
    (hcodim : sigma.card + 1 = A.card)
    (hnotBoundary : ¬ LiesInReferenceBoundary b T A sigma)
    (tau : Finset T.Vertex)
    (htau : tau ∈ faceComplex b T A) (htauCard : tau.card = A.card)
    (hsigmaTau : sigma ⊆ tau)
    (v : T.Vertex) (hvTau : v ∈ tau) (hvSigma : v ∉ sigma) :
    letI : Nonempty
        (affineSpan ℝ (referenceFaceVertices b A : Set E)) :=
      referenceSpanNonempty b A (by
        apply Finset.card_pos.mp
        have := hsigmaNonempty.card_pos
        omega)
    let a := topCofaceAffineBasis b T A (by
        apply Finset.card_pos.mp
        have := hsigmaNonempty.card_pos
        omega) tau htau htauCard
    ∃ q : affineSpan ℝ (referenceFaceVertices b A : Set E),
      q.1 ∈ referenceFace b A ∧ a.coord ⟨v, hvTau⟩ q < 0 := by
  classical
  by_contra hnoNegative
  apply hnotBoundary
  exact liesInReferenceBoundary_of_no_negative_topCofaceCoord b T
    A sigma hsigmaA hsigmaNonempty hcodim tau htau htauCard hsigmaTau
    v hvTau hvSigma hnoNegative

/-- A non-boundary, nonempty codimension-one face has a second top coface
distinct from any prescribed first one.  Starting at the opposite-face
centroid, move a sufficiently short distance toward the negative reference
point supplied above.  The complement of all non-cofaces is an open
neighborhood of the centroid, so any simplex covering the new point must
contain the whole opposite face; negativity excludes the prescribed
coface. -/
theorem exists_distinct_topCoface_of_not_boundary_of_nonempty
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigmaA : sigma ∈ faceComplex b T A)
    (hsigmaNonempty : sigma.Nonempty)
    (hcodim : sigma.card + 1 = A.card)
    (hnotBoundary : ¬ LiesInReferenceBoundary b T A sigma)
    (tau₁ : Finset T.Vertex)
    (htau₁ : tau₁ ∈ faceComplex b T A) (htau₁Card : tau₁.card = A.card)
    (hsigma₁ : sigma ⊆ tau₁) :
    ∃ tau₂ : Finset T.Vertex,
      tau₂ ∈ faceComplex b T A ∧ tau₂.card = A.card ∧
        sigma ⊆ tau₂ ∧ tau₂ ≠ tau₁ := by
  classical
  have hA : A.Nonempty := by
    apply Finset.card_pos.mp
    have := hsigmaNonempty.card_pos
    omega
  have hsigmaData :=
    ((mem_faceComplex_iff b T A sigma).1 hsigmaA).resolve_left
      hsigmaNonempty.ne_empty
  obtain ⟨v₁, hv₁, -⟩ := existsUnique_apex_of_subset_card_add_one
    hsigma₁ (by omega)
  let R : AffineSubspace ℝ E :=
    affineSpan ℝ (referenceFaceVertices b A : Set E)
  let : Nonempty R := referenceSpanNonempty b A hA
  let a : AffineBasis tau₁ ℝ R :=
    topCofaceAffineBasis b T A hA tau₁ htau₁ htau₁Card
  let i : tau₁ := ⟨v₁, hv₁.1⟩
  let L : R →ᵃ[ℝ] ℝ := a.coord i
  obtain ⟨q, hqReference, hqNegative⟩ :=
    exists_referenceFace_point_negative_topCofaceCoord b T
      A sigma hsigmaA hsigmaNonempty hcodim hnotBoundary
      tau₁ htau₁ htau₁Card hsigma₁ v₁ hv₁.1 hv₁.2
  let s : Finset E := realizeSimplex b T sigma
  have hsFace : s ∈ T.complex.faces := hsigmaData.1
  let x : E :=
    (Finset.univ : Finset s).centroid ℝ ((↑) : s → E)
  have hsNonempty : s.Nonempty := T.complex.nonempty_of_mem_faces hsFace
  have hsum :
      ∑ j ∈ (Finset.univ : Finset s),
        (Finset.univ : Finset s).centroidWeights ℝ j = 1 :=
    (Finset.univ : Finset s).sum_centroidWeights_eq_one_of_nonempty ℝ
      (by simpa using hsNonempty.attach)
  have hxHullS : x ∈ convexHull ℝ (s : Set E) := by
    have hxRange :
        x ∈ convexHull ℝ (Set.range ((↑) : s → E)) := by
      dsimp [x]
      rw [Finset.centroid_def]
      exact affineCombination_mem_convexHull (by simp) hsum
    simpa using hxRange
  have hxReference : x ∈ referenceFace b A := by
    apply convexHull_min _
        (convex_convexHull ℝ (referenceFaceVertices b A : Set E)) hxHullS
    intro y hy
    change y ∈ realizeSimplex b T sigma at hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    exact hsigmaData.2 w hw
  let xR : R :=
    ⟨x, convexHull_subset_affineSpan
      (referenceFaceVertices b A : Set E) hxReference⟩
  have hLxZero : L xR = 0 := by
    simpa [R, a, i, L, xR, s] using
      (topCoface_apexCoord_eq_zero_of_mem_opposite_convexHull b T
        A hA sigma hsigmaA hsigmaNonempty tau₁ htau₁ htau₁Card
        hsigma₁ v₁ hv₁.1 hv₁.2 xR (by simpa [s] using hxHullS))
  let O : Set E := (nonCofaceRegion b T s)ᶜ
  have hOOpen : IsOpen O := (isClosed_nonCofaceRegion b T s).isOpen_compl
  have hxO : x ∈ O := indexedCentroid_not_mem_nonCofaceRegion b T hsFace
  let t : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  let y : ℕ → E := fun k ↦ AffineMap.lineMap x q.1 (t k)
  have htTendsto : Tendsto t atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hyTendsto : Tendsto y atTop (𝓝 x) := by
    have hline : Tendsto
        (fun r : ℝ ↦ AffineMap.lineMap x q.1 r)
          (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa using AffineMap.lineMap_continuous.tendsto (0 : ℝ)
    change Tendsto ((fun r : ℝ ↦ AffineMap.lineMap x q.1 r) ∘ t)
      atTop (𝓝 x)
    exact hline.comp htTendsto
  have hyEventually : ∀ᶠ k in atTop, y k ∈ O :=
    hyTendsto.eventually (hOOpen.mem_nhds hxO)
  rw [eventually_atTop] at hyEventually
  obtain ⟨k, hk⟩ := hyEventually
  let r : ℝ := t k
  let z : E := y k
  have hrPos : 0 < r := by
    dsimp [r, t]
    positivity
  have hrLe : r ≤ 1 := by
    dsimp [r, t]
    rw [one_div]
    apply inv_le_one_of_one_le₀
    have hkNonnegative : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hzO : z ∈ O := hk k le_rfl
  have hzReference : z ∈ referenceFace b A :=
    (convex_convexHull ℝ (referenceFaceVertices b A : Set E)).lineMap_mem
      hxReference hqReference ⟨hrPos.le, hrLe⟩
  let zR : R :=
    ⟨z, convexHull_subset_affineSpan
      (referenceFaceVertices b A : Set E) hzReference⟩
  have hzRLine : zR = AffineMap.lineMap xR q r := by
    apply Subtype.ext
    rfl
  have hLzNegative : L zR < 0 := by
    rw [hzRLine]
    have hmapLine :
        L (AffineMap.lineMap xR q r) =
          AffineMap.lineMap (L xR) (L q) r := by
      rw [← AffineMap.comp_apply, AffineMap.comp_lineMap]
    rw [hmapLine, AffineMap.lineMap_apply_ring, hLxZero]
    simpa only [mul_zero, zero_add] using
      mul_neg_of_pos_of_neg hrPos hqNegative
  obtain ⟨tau₂, htau₂, hzHullTau₂⟩ :=
    exists_faceComplex_simplex_containing b T A hzReference
  have htau₂Nonempty : tau₂.Nonempty := by
    by_contra htau₂Empty
    rw [Finset.not_nonempty_iff_eq_empty.mp htau₂Empty] at hzHullTau₂
    simp [realizeSimplex] at hzHullTau₂
  have htau₂Data :=
    ((mem_faceComplex_iff b T A tau₂).1 htau₂).resolve_left
      htau₂Nonempty.ne_empty
  have hsRealizedSubset : s ⊆ realizeSimplex b T tau₂ := by
    by_contra hnotSubset
    apply hzO
    rw [nonCofaceRegion]
    apply Set.mem_iUnion.mpr
    refine ⟨realizeSimplex b T tau₂, Set.mem_iUnion.mpr ⟨?_, hzHullTau₂⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨(Set.Finite.mem_toFinset (faces_finite b T)).mpr htau₂Data.1, ?_⟩
    exact hnotSubset
  have hsigma₂ : sigma ⊆ tau₂ := by
    intro w hw
    have hwRealized : w.1 ∈ s :=
      Finset.mem_image.mpr ⟨w, hw, rfl⟩
    have hwTau₂ := hsRealizedSubset hwRealized
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hwTau₂
    have huEq : u = w := Subtype.ext huw
    simpa [huEq] using hu
  have hsigmaNeTau₂ : sigma ≠ tau₂ := by
    intro hsigmaEq
    have hzHullSigma : z ∈
        convexHull ℝ (realizeSimplex b T sigma : Set E) := by
      simpa [hsigmaEq] using hzHullTau₂
    have hzero :=
      topCoface_apexCoord_eq_zero_of_mem_opposite_convexHull b T
        A hA sigma hsigmaA hsigmaNonempty tau₁ htau₁ htau₁Card
        hsigma₁ v₁ hv₁.1 hv₁.2 zR hzHullSigma
    have : L zR = 0 := by simpa [a, i, L] using hzero
    linarith
  have hsigmaProper : sigma ⊂ tau₂ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsigma₂, hsigmaNeTau₂⟩
  have htau₂CardLe := faceComplex_card_le b T A htau₂
  have htau₂CardGt := Finset.card_lt_card hsigmaProper
  have htau₂Card : tau₂.card = A.card := by omega
  have htau₂NeTau₁ : tau₂ ≠ tau₁ := by
    intro htauEq
    have hnonnegative :=
      topCoface_coord_nonnegative_of_mem_convexHull b T A hA
        tau₁ htau₁ htau₁Card i zR (by simpa [htauEq] using hzHullTau₂)
    have : 0 ≤ L zR := by simpa [a, i, L] using hnonnegative
    linarith
  exact ⟨tau₂, htau₂, htau₂Card, hsigma₂, htau₂NeTau₁⟩

/-- The empty codimension-one simplex in a one-vertex reference face is a
boundary simplex; this isolates the zero-dimensional edge case. -/
theorem empty_liesInReferenceBoundary_of_card_eq_one
    (A : Finset (Fin (n + 1))) (hAcard : A.card = 1) :
    LiesInReferenceBoundary b T A ∅ := by
  refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
    (Finset.empty_subset A), ?_⟩, ?_⟩
  · simpa using hAcard.symm
  · intro v hv
    simp at hv

/-- A codimension-one simplex away from the reference boundary has exactly
two top-dimensional cofaces. -/
theorem cofaceCount_eq_two_of_not_liesInReferenceBoundary
    (A : Finset (Fin (n + 1))) (sigma : Finset T.Vertex)
    (hsigmaA : sigma ∈ faceComplex b T A)
    (hcodim : sigma.card + 1 = A.card)
    (hnotBoundary : ¬ LiesInReferenceBoundary b T A sigma) :
    (family b T).cofaceCount A sigma = 2 := by
  classical
  have hsigmaNonempty : sigma.Nonempty := by
    by_contra hsigmaEmpty
    have hsigmaEq : sigma = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsigmaEmpty
    subst sigma
    have hAcard : A.card = 1 := by simpa using hcodim.symm
    exact hnotBoundary
      (empty_liesInReferenceBoundary_of_card_eq_one b T A hAcard)
  obtain ⟨tau₁, htau₁, htau₁Card, hsigma₁⟩ :=
    exists_top_coface b T A sigma hsigmaA hcodim
  obtain ⟨tau₂, htau₂, htau₂Card, hsigma₂, htau₂NeTau₁⟩ :=
    exists_distinct_topCoface_of_not_boundary_of_nonempty b T
      A sigma hsigmaA hsigmaNonempty hcodim hnotBoundary
      tau₁ htau₁ htau₁Card hsigma₁
  rw [SimplexFamily.cofaceCount]
  let S := ((faceComplex b T A).topSimplices A.card).filter
    (fun tau ↦ sigma ⊆ tau)
  change S.card = 2
  have htauMem (tau : Finset T.Vertex)
      (htau : tau ∈ faceComplex b T A) (htauCard : tau.card = A.card)
      (hsigmaTau : sigma ⊆ tau) : tau ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, htauCard⟩, hsigmaTau⟩
    exact (FiniteSimplicialComplex.mem_simplices_iff
      (faceComplex b T A) tau).mpr htau
  have htau₁S : tau₁ ∈ S := htauMem tau₁ htau₁ htau₁Card hsigma₁
  have htau₂S : tau₂ ∈ S := htauMem tau₂ htau₂ htau₂Card hsigma₂
  have hlower : 1 < S.card :=
    Finset.one_lt_card_iff.mpr
      ⟨tau₁, tau₂, htau₁S, htau₂S, Ne.symm htau₂NeTau₁⟩
  have hupper := cofaceCount_le_two b T A sigma hcodim
  change S.card ≤ 2 at hupper
  omega

/-- Every finite geometric triangulation of a reference simplex is locally
nonbranching: boundary codimension-one faces have one top coface and all
other codimension-one faces have two. -/
theorem isNonbranching : IsNonbranching b T := by
  intro A sigma hsigmaA hcodim
  by_cases hboundary : LiesInReferenceBoundary b T A sigma
  · rw [if_pos hboundary]
    exact cofaceCount_eq_one_of_liesInReferenceBoundary b T
      A sigma hsigmaA hcodim hboundary
  · rw [if_neg hboundary]
    exact cofaceCount_eq_two_of_not_liesInReferenceBoundary b T
      A sigma hsigmaA hcodim hboundary

end GeometricTriangulation
end BeyondSperner
