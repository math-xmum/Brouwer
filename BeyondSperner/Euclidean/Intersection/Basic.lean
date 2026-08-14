import BeyondSperner.Euclidean.Chains
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Order.Compact

/-!
# General position and intersection numbers in a real vector space

This file begins the independent intersection-number route of Section 10 of
Ivanov's *Beyond Sperner's Lemma*.  Simplices are literal finite sets of
points, just as in the paper.  The definitions below deliberately use convex
hulls of faces, rather than the stronger condition of avoiding their affine
spans.

The two geometric intersection numbers are total `ZMod 2`-valued functions;
the paper only uses them under the corresponding general-position predicates.
Their extension outside general position is definitionally harmless and makes
the finite-chain pairing genuinely bilinear.
-/

namespace BeyondSperner
namespace EuclideanIntersection

open Classical Filter Set
open scoped Topology
open SimplexFamily

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- An `m`-simplex in the paper is a set of exactly `m + 1` points. -/
def IsMSimplex (m : ℕ) (sigma : Finset E) : Prop :=
  sigma.card = m + 1

/-- A Euclidean simplex is generic when its vertices are affinely
independent. -/
def IsGeneric (sigma : Finset E) : Prop :=
  AffineIndependent ℝ (fun x : (sigma : Set E) ↦ x.1)

/-- A chain is homogeneous of simplex-cardinality `k`. -/
def IsChainOfCardinality (k : ℕ) (c : Chain E) : Prop :=
  ∀ sigma ∈ c.support, sigma.card = k

/-- An `m`-chain is supported on finite sets of cardinality `m + 1`. -/
def IsMChain (m : ℕ) (c : Chain E) : Prop :=
  IsChainOfCardinality (m + 1) c

@[simp]
theorem isMChain_zero
    {V : Type*} [DecidableEq V] (m : ℕ) : IsMChain m (0 : Chain V) := by
  simp [IsMChain, IsChainOfCardinality]

/-- A sum of homogeneous chains of the same dimension is homogeneous. -/
theorem IsMChain.add
    {V : Type*} [DecidableEq V] {m : ℕ} {c d : Chain V}
    (hc : IsMChain m c) (hd : IsMChain m d) : IsMChain m (c + d) := by
  intro sigma hsigma
  have hsigma' : sigma ∈ c.support ∪ d.support := Finsupp.support_add hsigma
  rcases Finset.mem_union.mp hsigma' with hsigma | hsigma
  · exact hc sigma hsigma
  · exact hd sigma hsigma

/-- The normalized image of one `m`-simplex is either its injective image or
zero, and hence remains an `m`-chain in both cases. -/
theorem isMChain_normalizedMapSimplex
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (m : ℕ) (f : V → W) (sigma : Finset V) (hsigma : IsMSimplex m sigma) :
    IsMChain m (SimplexFamily.normalizedMapSimplex f sigma) := by
  by_cases hf : Set.InjOn f sigma
  · rw [SimplexFamily.normalizedMapSimplex_eq_of_injOn f sigma hf]
    simpa [IsMChain, IsChainOfCardinality, IsMSimplex, singletonChain,
      Finset.card_image_of_injOn hf] using hsigma
  · rw [SimplexFamily.normalizedMapSimplex_eq_zero_of_not_injOn f sigma hf]
    exact isMChain_zero m

/-- Normalized pushforward preserves chain dimension.  Degenerate images are
removed rather than allowed to create lower-dimensional support. -/
theorem IsMChain.normalizedMapChainHom
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (m : ℕ) (f : V → W) (c : Chain V) (hc : IsMChain m c) :
    IsMChain m (SimplexFamily.normalizedMapChainHom f c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add sigma a c hsigma ha ih =>
      have haOne : a = 1 := by
        apply ZMod.val_injective 2
        have hapos : 0 < a.val := by
          by_contra hnot
          have hzeroVal : a.val = 0 := by omega
          apply ha
          apply ZMod.val_injective 2
          simp [hzeroVal]
        have halt := ZMod.val_lt a
        have haval : a.val = 1 := by omega
        exact haval.trans (ZMod.val_one 2).symm
      subst a
      have hcSigma : IsMSimplex m sigma := by
        apply hc sigma
        have hc0 : c sigma = 0 := by
          by_contra hne
          exact hsigma (Finsupp.mem_support_iff.mpr hne)
        simp [hc0]
      have hcTail : IsMChain m c := by
        intro tau htau
        apply hc tau
        rw [Finsupp.mem_support_iff]
        have htauNe : c tau ≠ 0 := Finsupp.mem_support_iff.mp htau
        have htauSigma : tau ≠ sigma := by
          intro h
          subst tau
          exact hsigma htau
        simp [htauSigma, htauNe]
      change IsMChain m
        (SimplexFamily.normalizedMapChainHom f (singletonChain sigma + c))
      rw [map_add, SimplexFamily.normalizedMapChainHom_singleton]
      exact (isMChain_normalizedMapSimplex m f sigma hcSigma).add (ih hcTail)

/-- The geometric realization of a finite simplex. -/
def realization (sigma : Finset E) : Set E :=
  convexHull ℝ (sigma : Set E)

/-- General position of a point with respect to a simplex: the point avoids
the convex hull of every facet.  This is the paper's condition, and is weaker
than avoiding the affine span of every facet. -/
def PointInGeneralPosition (sigma : Finset E) (z : E) : Prop :=
  ∀ v ∈ sigma, z ∉ realization (sigma.erase v)

/-- General position of a one-simplex with respect to a prospective facet
`tau`: its endpoints avoid `tau`, and its segment avoids every facet of
`tau`.  When `tau` is an `(n-1)`-simplex, the erased faces are exactly its
`(n-2)`-faces, including the empty face when `n = 1`. -/
def OneSimplexInGeneralPositionWithFace
    (tau omega : Finset E) : Prop :=
  IsMSimplex 1 omega ∧
    (∀ z ∈ omega, z ∉ realization tau) ∧
    ∀ v ∈ tau, Disjoint (realization omega) (realization (tau.erase v))

/-- General position of a one-simplex with respect to a simplex: both
endpoints are in point general position and the segment is in general
position with respect to every facet. -/
def OneSimplexInGeneralPosition (sigma omega : Finset E) : Prop :=
  IsMSimplex 1 omega ∧
    (∀ z ∈ omega, PointInGeneralPosition sigma z) ∧
    ∀ v ∈ sigma,
      OneSimplexInGeneralPositionWithFace (sigma.erase v) omega

omit [DecidableEq E] in theorem realization_mono {tau sigma : Finset E} (h : tau ⊆ sigma) :
    realization tau ⊆ realization sigma := by
  exact convexHull_mono (by simpa using h)

theorem realization_erase_subset (sigma : Finset E) (v : E) :
    realization (sigma.erase v) ⊆ realization sigma :=
  realization_mono (Finset.erase_subset v sigma)

/-- For an affinely independent simplex, two faces meet exactly in the
realization of their common vertices.  This is the geometric fact that makes
the paper's codimension-two avoidance condition strong enough to separate
crossings of distinct facets. -/
theorem realization_inter_faces
    {sigma tau upsilon : Finset E} (hgeneric : IsGeneric sigma)
    (htau : tau ⊆ sigma) (hupsilon : upsilon ⊆ sigma) :
    realization tau ∩ realization upsilon = realization (tau ∩ upsilon) := by
  have h := (show AffineIndependent ℝ
      (fun x : (sigma : Set E) ↦ x.1) from hgeneric).convexHull_inter
    (R := ℝ) htau hupsilon
  simpa [realization] using h.symm

theorem realization_inter_erased_facets
    {sigma : Finset E} (hgeneric : IsGeneric sigma)
    (v w : E) :
    realization (sigma.erase v) ∩ realization (sigma.erase w) =
      realization ((sigma.erase v).erase w) := by
  rw [realization_inter_faces hgeneric
    (Finset.erase_subset v sigma) (Finset.erase_subset w sigma)]
  congr 1
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase]
  tauto

/-- Under the paper's exact general-position condition, the segment cannot
meet two distinct facets at the same point. -/
theorem disjoint_crossings_of_distinct_facets
    {sigma omega : Finset E} (hgeneric : IsGeneric sigma)
    (hgp : OneSimplexInGeneralPosition sigma omega)
    {v w : E} (hv : v ∈ sigma) (hw : w ∈ sigma) (hvw : v ≠ w) :
    Disjoint
      (realization omega ∩ realization (sigma.erase v))
      (realization omega ∩ realization (sigma.erase w)) := by
  apply Set.disjoint_left.mpr
  intro p hpv hpw
  have hpCommon : p ∈ realization ((sigma.erase v).erase w) := by
    rw [← realization_inter_erased_facets hgeneric v w]
    exact ⟨hpv.2, hpw.2⟩
  have hwErase : w ∈ sigma.erase v := by
    exact Finset.mem_erase.mpr ⟨hvw.symm, hw⟩
  have hDisjoint := (hgp.2.2 v hv).2.2 w hwErase
  exact (Set.disjoint_left.mp hDisjoint) hpv.1 hpCommon

/-- Parameters for which the segment from `x` to `y` lies in the realized
simplex.  Keeping the parameter interval explicit is essential: its two
endpoints are what the mod-two crossing argument counts. -/
def segmentParameters (sigma : Finset E) (x y : E) : Set ℝ :=
  Set.Icc 0 1 ∩
    (AffineMap.lineMap x y : ℝ → E) ⁻¹' realization sigma

omit [DecidableEq E] in @[simp]
theorem zero_mem_segmentParameters_iff (sigma : Finset E) (x y : E) :
    0 ∈ segmentParameters sigma x y ↔ x ∈ realization sigma := by
  simp [segmentParameters]

omit [DecidableEq E] in @[simp]
theorem one_mem_segmentParameters_iff (sigma : Finset E) (x y : E) :
    1 ∈ segmentParameters sigma x y ↔ y ∈ realization sigma := by
  simp [segmentParameters]

@[simp]
theorem realization_pair (x y : E) :
    realization ({x, y} : Finset E) = segment ℝ x y := by
  simp [realization, convexHull_pair]

/-- A real affine function that is nonnegative at both ends of an interval
and zero at a strict interior point must vanish at both ends. -/
theorem lineMap_eq_zero_at_endpoints_of_eq_zero_interior
    (A B a t b : ℝ) (hat : a < t) (htb : t < b)
    (ha : 0 ≤ AffineMap.lineMap A B a)
    (hb : 0 ≤ AffineMap.lineMap A B b)
    (ht : AffineMap.lineMap A B t = 0) :
    AffineMap.lineMap A B a = 0 ∧
      AffineMap.lineMap A B b = 0 := by
  simp only [AffineMap.lineMap_apply_ring'] at ha hb ht ⊢
  constructor <;> nlinarith [sq_nonneg (B - A)]

section Normed

variable [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E]

omit [DecidableEq E] in theorem isCompact_segmentParameters (sigma : Finset E) (x y : E) :
    IsCompact (segmentParameters sigma x y) := by
  exact isCompact_Icc.inter_right
    ((sigma.finite_toSet.isClosed_convexHull ℝ).preimage
      AffineMap.lineMap_continuous)

omit [DecidableEq E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in theorem convex_segmentParameters (sigma : Finset E) (x y : E) :
    Convex ℝ (segmentParameters sigma x y) := by
  exact (convex_Icc 0 1).inter
    ((convex_convexHull ℝ (sigma : Set E)).affine_preimage
      (AffineMap.lineMap x y))

omit [DecidableEq E] in
/-- A nonempty segment/simplex intersection has one-dimensional parameter
set equal to a closed interval.  This rules out disconnected or oscillating
crossing patterns before any parity argument is attempted. -/
theorem segmentParameters_eq_Icc_of_nonempty
    (sigma : Finset E) (x y : E)
    (hne : (segmentParameters sigma x y).Nonempty) :
    segmentParameters sigma x y =
      Set.Icc (sInf (segmentParameters sigma x y))
        (sSup (segmentParameters sigma x y)) := by
  exact eq_Icc_of_connected_compact
    ((convex_segmentParameters sigma x y).isConnected hne)
    (isCompact_segmentParameters sigma x y)

end Normed

section FullDimensional

variable [FiniteDimensional ℝ E]

/-- A generic finite simplex with exactly `finrank E + 1` vertices is an
affine basis of the ambient vector space.  The index type is the vertex
subtype itself, so this construction introduces no artificial ordering of
the vertices. -/
noncomputable def affineBasisOfGenericFull
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1) :
    AffineBasis (sigma : Set E) ℝ E := by
  refine ⟨(fun i ↦ i.1), hgeneric, ?_⟩
  apply hgeneric.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Fintype.card_of_finset' sigma (by simp)]
  exact hcard

omit [DecidableEq E] in @[simp]
theorem affineBasisOfGenericFull_apply
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1) (i : (sigma : Set E)) :
    affineBasisOfGenericFull sigma hgeneric hcard i = i.1 :=
  rfl

omit [DecidableEq E] in theorem range_affineBasisOfGenericFull
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1) :
    Set.range (affineBasisOfGenericFull sigma hgeneric hcard) =
      (sigma : Set E) := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact i.2
  · intro hp
    exact ⟨⟨p, hp⟩, rfl⟩

omit [DecidableEq E] in
/-- Exact barycentric half-space description of a full-dimensional generic
simplex.  This is the coordinate bridge used by the interval proof of
Lemma 10.1. -/
theorem realization_eq_nonneg_coord
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1) :
    realization sigma =
      {p | ∀ i : (sigma : Set E),
        0 ≤ (affineBasisOfGenericFull sigma hgeneric hcard).coord i p} := by
  let b := affineBasisOfGenericFull sigma hgeneric hcard
  calc
    realization sigma = convexHull ℝ (Set.range b) := by
      simpa [b, realization] using congrArg (convexHull ℝ)
        (range_affineBasisOfGenericFull sigma hgeneric hcard).symm
    _ = {p | ∀ i : (sigma : Set E), 0 ≤ b.coord i p} :=
      b.convexHull_eq_nonneg_coord

/-- Membership in the facet opposite `v` forces the `v`-coordinate to
vanish.  This direction needs only convexity of the coordinate hyperplane;
it does not replace the facet by its affine span in the definition of
general position. -/
theorem coord_eq_zero_of_mem_realization_erase
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    {v p : E} (hv : v ∈ sigma) (hp : p ∈ realization (sigma.erase v)) :
    (affineBasisOfGenericFull sigma hgeneric hcard).coord ⟨v, hv⟩ p = 0 := by
  let b := affineBasisOfGenericFull sigma hgeneric hcard
  let iv : (sigma : Set E) := ⟨v, hv⟩
  have hvertices : (sigma.erase v : Set E) ⊆
      {q | b.coord iv q = 0} := by
    intro q hq
    have hqSigma : q ∈ sigma := Finset.mem_of_mem_erase hq
    let iq : (sigma : Set E) := ⟨q, hqSigma⟩
    have hne : iv ≠ iq := by
      intro h
      apply (Finset.ne_of_mem_erase hq)
      exact (congr_arg Subtype.val h).symm
    change b.coord iv (b iq) = 0
    exact b.coord_apply_ne hne
  have hconvex : Convex ℝ {q | b.coord iv q = 0} := by
    rw [show {q | b.coord iv q = 0} =
        (b.coord iv) ⁻¹' ({0} : Set ℝ) by ext q; simp]
    exact (convex_singleton (0 : ℝ)).affine_preimage (b.coord iv)
  exact convexHull_min hvertices hconvex hp

/-- Exact facet equation in barycentric coordinates.  Both nonnegativity and
the zero coordinate are consequences of membership in the literal convex
hull of the erased vertex set. -/
theorem mem_realization_erase_imp_coord
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    {v p : E} (hv : v ∈ sigma) (hp : p ∈ realization (sigma.erase v)) :
    (∀ i : (sigma : Set E),
      0 ≤ (affineBasisOfGenericFull sigma hgeneric hcard).coord i p) ∧
    (affineBasisOfGenericFull sigma hgeneric hcard).coord ⟨v, hv⟩ p = 0 := by
  constructor
  · have hpFull : p ∈ realization sigma :=
      realization_erase_subset sigma v hp
    rw [realization_eq_nonneg_coord sigma hgeneric hcard] at hpFull
    exact hpFull
  · exact coord_eq_zero_of_mem_realization_erase sigma hgeneric hcard hv hp

/-- The converse facet equation: nonnegative barycentric coordinates with
the `v`-coordinate zero reconstruct a convex combination using only the
remaining literal vertices. -/
theorem mem_realization_erase_of_coord
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    {v p : E} (hv : v ∈ sigma)
    (hnonneg : ∀ i : (sigma : Set E),
      0 ≤ (affineBasisOfGenericFull sigma hgeneric hcard).coord i p)
    (hzero :
      (affineBasisOfGenericFull sigma hgeneric hcard).coord ⟨v, hv⟩ p = 0) :
    p ∈ realization (sigma.erase v) := by
  let b := affineBasisOfGenericFull sigma hgeneric hcard
  let w : E → ℝ := fun q ↦
    if hq : q ∈ sigma then b.coord ⟨q, hq⟩ p else 0
  have hwv : w v = 0 := by
    simpa [w, hv, b] using hzero
  have hwCoord (i : (sigma : Set E)) : w i.1 = b.coord i p := by
    dsimp only [w]
    split
    · congr
    · exact False.elim (by aesop)
  have hsumSigma : ∑ q ∈ sigma, w q = 1 := by
    calc
      ∑ q ∈ sigma, w q = ∑ i : (sigma : Set E), w i.1 :=
        Finset.sum_subtype sigma (fun _ ↦ Iff.rfl) w
      _ = ∑ i : (sigma : Set E), b.coord i p := by
        apply Fintype.sum_congr
        exact hwCoord
      _ = 1 := b.sum_coord_apply_eq_one p
  have hlinearSigma : ∑ q ∈ sigma, w q • q = p := by
    calc
      ∑ q ∈ sigma, w q • q =
          ∑ i : (sigma : Set E), w i.1 • i.1 :=
        Finset.sum_subtype sigma (fun _ ↦ Iff.rfl) (fun q ↦ w q • q)
      _ = ∑ i : (sigma : Set E), b.coord i p • b i := by
        apply Fintype.sum_congr
        intro i
        rw [hwCoord]
        rfl
      _ = p := b.linear_combination_coord_eq_self p
  rw [realization, Finset.mem_convexHull']
  refine ⟨w, ?_, ?_, ?_⟩
  · intro q hq
    have hqSigma : q ∈ sigma := Finset.mem_of_mem_erase hq
    simpa [w, hqSigma, b] using hnonneg ⟨q, hqSigma⟩
  · rw [Finset.sum_erase sigma hwv]
    exact hsumSigma
  · calc
      ∑ y ∈ sigma.erase v, w y • y = ∑ y ∈ sigma, w y • y :=
        Finset.sum_erase sigma (f := fun y ↦ w y • y)
          (a := v) (by simp [hwv])
      _ = p := hlinearSigma

/-- A point lies in the literal erased-face convex hull iff all barycentric
coordinates are nonnegative and the erased coordinate is zero. -/
theorem mem_realization_erase_iff_coord
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    {v p : E} (hv : v ∈ sigma) :
    p ∈ realization (sigma.erase v) ↔
      (∀ i : (sigma : Set E),
        0 ≤ (affineBasisOfGenericFull sigma hgeneric hcard).coord i p) ∧
      (affineBasisOfGenericFull sigma hgeneric hcard).coord ⟨v, hv⟩ p = 0 := by
  constructor
  · exact mem_realization_erase_imp_coord sigma hgeneric hcard hv
  · rintro ⟨hnonneg, hzero⟩
    exact mem_realization_erase_of_coord sigma hgeneric hcard hv hnonneg hzero

/-- A facet meets a literal segment iff one of its parameters belongs to the
simplex parameter interval and the corresponding barycentric coordinate is
zero.  This is the exact bridge from the paper's geometric intersection
number to the one-dimensional parity problem. -/
theorem facet_inter_pair_nonempty_iff_exists_parameter_coord_eq_zero
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    {v x y : E} (hv : v ∈ sigma) :
    (realization (sigma.erase v) ∩
        realization ({x, y} : Finset E)).Nonempty ↔
      ∃ t ∈ segmentParameters sigma x y,
        (affineBasisOfGenericFull sigma hgeneric hcard).coord ⟨v, hv⟩
          (AffineMap.lineMap x y t) = 0 := by
  let b := affineBasisOfGenericFull sigma hgeneric hcard
  constructor
  · rintro ⟨p, hpFacet, hpSegment⟩
    rw [realization_pair, segment_eq_image_lineMap] at hpSegment
    obtain ⟨t, ht, rfl⟩ := hpSegment
    have hcoord := (mem_realization_erase_iff_coord
      sigma hgeneric hcard hv).mp hpFacet
    refine ⟨t, ?_, hcoord.2⟩
    refine ⟨ht, ?_⟩
    rw [realization_eq_nonneg_coord sigma hgeneric hcard]
    exact hcoord.1
  · rintro ⟨t, ht, hzero⟩
    refine ⟨AffineMap.lineMap x y t, ?_, ?_⟩
    · apply (mem_realization_erase_iff_coord
        sigma hgeneric hcard hv).mpr
      have htRealization : AffineMap.lineMap x y t ∈ realization sigma := ht.2
      rw [realization_eq_nonneg_coord sigma hgeneric hcard] at htRealization
      exact ⟨htRealization, hzero⟩
    · rw [realization_pair, segment_eq_image_lineMap]
      exact ⟨t, ht.1, rfl⟩

/-- The codimension-two clause in the paper's segment general-position
definition becomes uniqueness of a vanishing barycentric coordinate at every
parameter lying in the simplex. -/
theorem unique_zero_coord_on_segmentParameters
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    {x y : E}
    (hgp : OneSimplexInGeneralPosition sigma ({x, y} : Finset E))
    {t : ℝ} (ht : t ∈ segmentParameters sigma x y)
    {i j : (sigma : Set E)}
    (hi : (affineBasisOfGenericFull sigma hgeneric hcard).coord i
      (AffineMap.lineMap x y t) = 0)
    (hj : (affineBasisOfGenericFull sigma hgeneric hcard).coord j
      (AffineMap.lineMap x y t) = 0) :
    i = j := by
  apply Subtype.ext
  by_contra hij
  have hnonneg : ∀ k : (sigma : Set E),
      0 ≤ (affineBasisOfGenericFull sigma hgeneric hcard).coord k
        (AffineMap.lineMap x y t) := by
    have htRealization : AffineMap.lineMap x y t ∈ realization sigma := ht.2
    rw [realization_eq_nonneg_coord sigma hgeneric hcard] at htRealization
    exact htRealization
  have hpSegment : AffineMap.lineMap x y t ∈
      realization ({x, y} : Finset E) := by
    rw [realization_pair, segment_eq_image_lineMap]
    exact ⟨t, ht.1, rfl⟩
  have hpFacetI : AffineMap.lineMap x y t ∈ realization (sigma.erase i.1) :=
    mem_realization_erase_of_coord sigma hgeneric hcard i.2 hnonneg hi
  have hpFacetJ : AffineMap.lineMap x y t ∈ realization (sigma.erase j.1) :=
    mem_realization_erase_of_coord sigma hgeneric hcard j.2 hnonneg hj
  have hdisjoint := disjoint_crossings_of_distinct_facets
    hgeneric hgp i.2 j.2 hij
  exact (Set.disjoint_left.mp hdisjoint)
    ⟨hpSegment, hpFacetI⟩ ⟨hpSegment, hpFacetJ⟩

/-- If an endpoint lies in the simplex, point general position makes every
barycentric coordinate of that endpoint nonzero.  Together with
nonnegativity, this means the endpoint lies in the simplex interior. -/
theorem endpoint_coord_ne_zero
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    {x y z : E} (hz : z ∈ ({x, y} : Finset E))
    (hgp : OneSimplexInGeneralPosition sigma ({x, y} : Finset E))
    (hzRealization : z ∈ realization sigma)
    (i : (sigma : Set E)) :
    (affineBasisOfGenericFull sigma hgeneric hcard).coord i z ≠ 0 := by
  intro hzero
  have hnonneg : ∀ k : (sigma : Set E),
      0 ≤ (affineBasisOfGenericFull sigma hgeneric hcard).coord k z := by
    have hzRealization' := hzRealization
    rw [realization_eq_nonneg_coord sigma hgeneric hcard] at hzRealization'
    exact hzRealization'
  have hzFacet : z ∈ realization (sigma.erase i.1) :=
    mem_realization_erase_of_coord sigma hgeneric hcard i.2 hnonneg hzero
  exact (hgp.2.1 z hz i.1 i.2) hzFacet

end FullDimensional

section FullDimensionalTopological

variable [FiniteDimensional ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E]

omit [DecidableEq E] in
/-- If the nondegenerate parameter interval starts after parameter zero,
some barycentric coordinate vanishes at its left endpoint.  The proof uses
only finiteness and continuity: if every coordinate were strictly positive,
the endpoint would be an interior point of the parameter set. -/
theorem exists_zero_coord_at_parameterInf
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    (x y : E) (hne : (segmentParameters sigma x y).Nonempty)
    (hnondegenerate : sInf (segmentParameters sigma x y) <
      sSup (segmentParameters sigma x y))
    (hneZero : sInf (segmentParameters sigma x y) ≠ 0) :
    ∃ i : (sigma : Set E),
      (affineBasisOfGenericFull sigma hgeneric hcard).coord i
        (AffineMap.lineMap x y (sInf (segmentParameters sigma x y))) = 0 := by
  let K := segmentParameters sigma x y
  let a := sInf K
  let b := sSup K
  let basis := affineBasisOfGenericFull sigma hgeneric hcard
  have hK : K = Set.Icc a b :=
    segmentParameters_eq_Icc_of_nonempty sigma x y hne
  have haK : a ∈ K := by
    rw [hK]
    exact ⟨le_rfl, hnondegenerate.le⟩
  have hbK : b ∈ K := by
    rw [hK]
    exact ⟨hnondegenerate.le, le_rfl⟩
  by_contra hnoZero
  push Not at hnoZero
  have haNonneg : ∀ i : (sigma : Set E),
      0 ≤ basis.coord i (AffineMap.lineMap x y a) := by
    have haRealization : AffineMap.lineMap x y a ∈ realization sigma := haK.2
    rw [realization_eq_nonneg_coord sigma hgeneric hcard] at haRealization
    exact haRealization
  have haPos : ∀ i : (sigma : Set E),
      0 < basis.coord i (AffineMap.lineMap x y a) := by
    intro i
    exact lt_of_le_of_ne (haNonneg i) (Ne.symm (hnoZero i))
  have hcoordContinuous (i : (sigma : Set E)) :
      Continuous (fun r : ℝ ↦
        basis.coord i (AffineMap.lineMap x y r)) := by
    simpa only [AffineMap.apply_lineMap] using
      (AffineMap.lineMap_continuous
        (p := basis.coord i x) (q := basis.coord i y))
  let U : Set ℝ := {r | ∀ i : (sigma : Set E),
    0 < basis.coord i (AffineMap.lineMap x y r)}
  have hUOpen : IsOpen U := by
    rw [show U = ⋂ i : (sigma : Set E),
        (fun r : ℝ ↦ basis.coord i (AffineMap.lineMap x y r)) ⁻¹'
          Set.Ioi 0 by
      ext r
      simp [U]]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_Ioi.preimage (hcoordContinuous i)
  have haU : a ∈ U := haPos
  have haIoo : a ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_of_le_of_ne haK.1.1 (Ne.symm hneZero)
    · exact hnondegenerate.trans_le hbK.1.2
  have haInteriorK : a ∈ interior K := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hUOpen.mem_nhds haU, isOpen_Ioo.mem_nhds haIoo] with r hrU hrIoo
    refine ⟨⟨hrIoo.1.le, hrIoo.2.le⟩, ?_⟩
    rw [realization_eq_nonneg_coord sigma hgeneric hcard]
    intro i
    exact (hrU i).le
  rw [hK, interior_Icc] at haInteriorK
  exact (lt_irrefl a) haInteriorK.1

omit [DecidableEq E] in
/-- Right-endpoint counterpart of `exists_zero_coord_at_parameterInf`. -/
theorem exists_zero_coord_at_parameterSup
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    (x y : E) (hne : (segmentParameters sigma x y).Nonempty)
    (hnondegenerate : sInf (segmentParameters sigma x y) <
      sSup (segmentParameters sigma x y))
    (hneOne : sSup (segmentParameters sigma x y) ≠ 1) :
    ∃ i : (sigma : Set E),
      (affineBasisOfGenericFull sigma hgeneric hcard).coord i
        (AffineMap.lineMap x y (sSup (segmentParameters sigma x y))) = 0 := by
  let K := segmentParameters sigma x y
  let a := sInf K
  let b := sSup K
  let basis := affineBasisOfGenericFull sigma hgeneric hcard
  have hK : K = Set.Icc a b :=
    segmentParameters_eq_Icc_of_nonempty sigma x y hne
  have haK : a ∈ K := by
    rw [hK]
    exact ⟨le_rfl, hnondegenerate.le⟩
  have hbK : b ∈ K := by
    rw [hK]
    exact ⟨hnondegenerate.le, le_rfl⟩
  by_contra hnoZero
  push Not at hnoZero
  have hbNonneg : ∀ i : (sigma : Set E),
      0 ≤ basis.coord i (AffineMap.lineMap x y b) := by
    have hbRealization : AffineMap.lineMap x y b ∈ realization sigma := hbK.2
    rw [realization_eq_nonneg_coord sigma hgeneric hcard] at hbRealization
    exact hbRealization
  have hbPos : ∀ i : (sigma : Set E),
      0 < basis.coord i (AffineMap.lineMap x y b) := by
    intro i
    exact lt_of_le_of_ne (hbNonneg i) (Ne.symm (hnoZero i))
  have hcoordContinuous (i : (sigma : Set E)) :
      Continuous (fun r : ℝ ↦
        basis.coord i (AffineMap.lineMap x y r)) := by
    simpa only [AffineMap.apply_lineMap] using
      (AffineMap.lineMap_continuous
        (p := basis.coord i x) (q := basis.coord i y))
  let U : Set ℝ := {r | ∀ i : (sigma : Set E),
    0 < basis.coord i (AffineMap.lineMap x y r)}
  have hUOpen : IsOpen U := by
    rw [show U = ⋂ i : (sigma : Set E),
        (fun r : ℝ ↦ basis.coord i (AffineMap.lineMap x y r)) ⁻¹'
          Set.Ioi 0 by
      ext r
      simp [U]]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_Ioi.preimage (hcoordContinuous i)
  have hbU : b ∈ U := hbPos
  have hbIoo : b ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact haK.1.1.trans_lt hnondegenerate
    · exact lt_of_le_of_ne hbK.1.2 hneOne
  have hbInteriorK : b ∈ interior K := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hUOpen.mem_nhds hbU, isOpen_Ioo.mem_nhds hbIoo] with r hrU hrIoo
    refine ⟨⟨hrIoo.1.le, hrIoo.2.le⟩, ?_⟩
    rw [realization_eq_nonneg_coord sigma hgeneric hcard]
    intro i
    exact (hrU i).le
  rw [hK, interior_Icc] at hbInteriorK
  exact (lt_irrefl b) hbInteriorK.2

/-- If one coordinate vanishes at both ends of a nondegenerate parameter
interval, that coordinate is identically zero along the line and therefore
cannot itself create the left boundary.  Hence an internal left boundary has
a second, distinct vanishing coordinate. -/
theorem exists_distinct_zero_coord_at_parameterInf
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    (x y : E) (hne : (segmentParameters sigma x y).Nonempty)
    (hnondegenerate : sInf (segmentParameters sigma x y) <
      sSup (segmentParameters sigma x y))
    (hneZero : sInf (segmentParameters sigma x y) ≠ 0)
    (i : (sigma : Set E))
    (hiInf : (affineBasisOfGenericFull sigma hgeneric hcard).coord i
      (AffineMap.lineMap x y (sInf (segmentParameters sigma x y))) = 0)
    (hiSup : (affineBasisOfGenericFull sigma hgeneric hcard).coord i
      (AffineMap.lineMap x y (sSup (segmentParameters sigma x y))) = 0) :
    ∃ j : (sigma : Set E), j ≠ i ∧
      (affineBasisOfGenericFull sigma hgeneric hcard).coord j
        (AffineMap.lineMap x y (sInf (segmentParameters sigma x y))) = 0 := by
  let K := segmentParameters sigma x y
  let a := sInf K
  let b := sSup K
  let basis := affineBasisOfGenericFull sigma hgeneric hcard
  have hK : K = Set.Icc a b :=
    segmentParameters_eq_Icc_of_nonempty sigma x y hne
  have haK : a ∈ K := by
    rw [hK]
    exact ⟨le_rfl, hnondegenerate.le⟩
  have hbK : b ∈ K := by
    rw [hK]
    exact ⟨hnondegenerate.le, le_rfl⟩
  have hiAll (r : ℝ) : basis.coord i (AffineMap.lineMap x y r) = 0 := by
    have hInf : AffineMap.lineMap (basis.coord i x) (basis.coord i y) a = 0 := by
      rw [← AffineMap.apply_lineMap]
      simpa [a, K, basis] using hiInf
    have hSup : AffineMap.lineMap (basis.coord i x) (basis.coord i y) b = 0 := by
      rw [← AffineMap.apply_lineMap]
      simpa [b, K, basis] using hiSup
    simp only [AffineMap.lineMap_apply_ring'] at hInf hSup
    have hprod : (b - a) * (basis.coord i y - basis.coord i x) = 0 := by
      nlinarith
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hnondegenerate.ne'
    have hslope : basis.coord i y - basis.coord i x = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hba
    have hxzero : basis.coord i x = 0 := by
      rw [hslope, mul_zero, zero_add] at hInf
      exact hInf
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring', hslope,
      mul_zero, zero_add, hxzero]
  by_contra hnoSecond
  have hnoZero (j : (sigma : Set E)) (hji : j ≠ i) :
      basis.coord j (AffineMap.lineMap x y a) ≠ 0 := by
    intro hj
    exact hnoSecond ⟨j, hji, hj⟩
  have haNonneg : ∀ j : (sigma : Set E),
      0 ≤ basis.coord j (AffineMap.lineMap x y a) := by
    have haRealization : AffineMap.lineMap x y a ∈ realization sigma := haK.2
    rw [realization_eq_nonneg_coord sigma hgeneric hcard] at haRealization
    exact haRealization
  have haPosOther (j : (sigma : Set E)) (hji : j ≠ i) :
      0 < basis.coord j (AffineMap.lineMap x y a) :=
    lt_of_le_of_ne (haNonneg j) (Ne.symm (hnoZero j hji))
  have hcoordContinuous (j : (sigma : Set E)) :
      Continuous (fun r : ℝ ↦
        basis.coord j (AffineMap.lineMap x y r)) := by
    simpa only [AffineMap.apply_lineMap] using
      (AffineMap.lineMap_continuous
        (p := basis.coord j x) (q := basis.coord j y))
  let U : Set ℝ := {r | ∀ j : (sigma : Set E), j ≠ i →
    0 < basis.coord j (AffineMap.lineMap x y r)}
  have hUOpen : IsOpen U := by
    rw [show U = ⋂ j : (sigma : Set E), ⋂ (_h : j ≠ i),
        (fun r : ℝ ↦ basis.coord j (AffineMap.lineMap x y r)) ⁻¹'
          Set.Ioi 0 by
      ext r
      simp [U]]
    exact isOpen_iInter_of_finite fun j ↦
      isOpen_iInter_of_finite fun _ ↦
        isOpen_Ioi.preimage (hcoordContinuous j)
  have haU : a ∈ U := fun j hji ↦ haPosOther j hji
  have haIoo : a ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_of_le_of_ne haK.1.1 (Ne.symm hneZero)
    · exact hnondegenerate.trans_le hbK.1.2
  have haInteriorK : a ∈ interior K := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hUOpen.mem_nhds haU, isOpen_Ioo.mem_nhds haIoo] with r hrU hrIoo
    refine ⟨⟨hrIoo.1.le, hrIoo.2.le⟩, ?_⟩
    rw [realization_eq_nonneg_coord sigma hgeneric hcard]
    intro j
    by_cases hji : j = i
    · subst j
      exact (hiAll r).ge
    · exact (hrU j hji).le
  rw [hK, interior_Icc] at haInteriorK
  exact (lt_irrefl a) haInteriorK.1

/-- Under full general position, a vanishing coordinate on a nondegenerate
parameter interval can occur only at one of the interval's two endpoints. -/
theorem parameter_eq_inf_or_sup_of_coord_eq_zero
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    {x y : E}
    (hgp : OneSimplexInGeneralPosition sigma ({x, y} : Finset E))
    (hne : (segmentParameters sigma x y).Nonempty)
    (hnondegenerate : sInf (segmentParameters sigma x y) <
      sSup (segmentParameters sigma x y))
    {t : ℝ} (ht : t ∈ segmentParameters sigma x y)
    (i : (sigma : Set E))
    (hi : (affineBasisOfGenericFull sigma hgeneric hcard).coord i
      (AffineMap.lineMap x y t) = 0) :
    t = sInf (segmentParameters sigma x y) ∨
      t = sSup (segmentParameters sigma x y) := by
  let K := segmentParameters sigma x y
  let a := sInf K
  let b := sSup K
  let basis := affineBasisOfGenericFull sigma hgeneric hcard
  have hK : K = Set.Icc a b :=
    segmentParameters_eq_Icc_of_nonempty sigma x y hne
  have haK : a ∈ K := by
    rw [hK]
    exact ⟨le_rfl, hnondegenerate.le⟩
  have hbK : b ∈ K := by
    rw [hK]
    exact ⟨hnondegenerate.le, le_rfl⟩
  have htIcc : t ∈ Set.Icc a b := hK ▸ ht
  by_cases hta : t = a
  · exact Or.inl hta
  by_cases htb : t = b
  · exact Or.inr htb
  have hat : a < t := lt_of_le_of_ne htIcc.1 (Ne.symm hta)
  have htb' : t < b := lt_of_le_of_ne htIcc.2 htb
  have haNonneg : 0 ≤ basis.coord i (AffineMap.lineMap x y a) := by
    have haRealization : AffineMap.lineMap x y a ∈ realization sigma := haK.2
    rw [realization_eq_nonneg_coord sigma hgeneric hcard] at haRealization
    exact haRealization i
  have hbNonneg : 0 ≤ basis.coord i (AffineMap.lineMap x y b) := by
    have hbRealization : AffineMap.lineMap x y b ∈ realization sigma := hbK.2
    rw [realization_eq_nonneg_coord sigma hgeneric hcard] at hbRealization
    exact hbRealization i
  have hEnds :
      basis.coord i (AffineMap.lineMap x y a) = 0 ∧
        basis.coord i (AffineMap.lineMap x y b) = 0 := by
    have hScalar := lineMap_eq_zero_at_endpoints_of_eq_zero_interior
      (basis.coord i x) (basis.coord i y) a t b hat htb'
      (by simpa only [AffineMap.apply_lineMap] using haNonneg)
      (by simpa only [AffineMap.apply_lineMap] using hbNonneg)
      (by simpa only [AffineMap.apply_lineMap, basis] using hi)
    simpa only [AffineMap.apply_lineMap] using hScalar
  by_cases haZero : a = 0
  · have hxRealization : x ∈ realization sigma := by
      have haRealization : AffineMap.lineMap x y a ∈ realization sigma := haK.2
      simpa [haZero] using haRealization
    have hneCoord := endpoint_coord_ne_zero sigma hgeneric hcard
      (x := x) (y := y) (z := x) (by simp) hgp hxRealization i
    exact (hneCoord (by simpa [haZero] using hEnds.1)).elim
  · obtain ⟨j, hji, hjZero⟩ :=
      exists_distinct_zero_coord_at_parameterInf
        sigma hgeneric hcard x y hne hnondegenerate haZero i hEnds.1 hEnds.2
    have hij := unique_zero_coord_on_segmentParameters
      sigma hgeneric hcard hgp haK hEnds.1 hjZero
    exact (hji hij.symm).elim

/-- General position rules out a singleton segment/simplex parameter set.
At a hypothetical singleton, either every coordinate is positive (and
openness gives nearby feasible parameters), or exactly one coordinate is
zero.  In the latter case its affine half-space contains parameters on at
least one side, while all other coordinates remain positive nearby. -/
theorem segmentParameters_nondegenerate_of_generalPosition
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    {x y : E}
    (hgp : OneSimplexInGeneralPosition sigma ({x, y} : Finset E))
    (hne : (segmentParameters sigma x y).Nonempty) :
    sInf (segmentParameters sigma x y) <
      sSup (segmentParameters sigma x y) := by
  let K := segmentParameters sigma x y
  let a := sInf K
  let b := sSup K
  let basis := affineBasisOfGenericFull sigma hgeneric hcard
  have hK : K = Set.Icc a b :=
    segmentParameters_eq_Icc_of_nonempty sigma x y hne
  obtain ⟨t₀, ht₀K⟩ := hne
  have ht₀Icc : t₀ ∈ Set.Icc a b := hK ▸ ht₀K
  have hab : a ≤ b := ht₀Icc.1.trans ht₀Icc.2
  by_contra hnotlt
  have habEq : a = b := le_antisymm hab (not_lt.mp hnotlt)
  have hKsingleton : K = {a} := by
    rw [hK, habEq, Set.Icc_self]
  have haK : a ∈ K := by simp [hKsingleton]
  have haBounds : a ∈ Set.Icc (0 : ℝ) 1 := haK.1
  have haNonneg : ∀ i : (sigma : Set E),
      0 ≤ basis.coord i (AffineMap.lineMap x y a) := by
    have haRealization : AffineMap.lineMap x y a ∈ realization sigma := haK.2
    rw [realization_eq_nonneg_coord sigma hgeneric hcard] at haRealization
    exact haRealization
  have hcoordContinuous (i : (sigma : Set E)) :
      Continuous (fun r : ℝ ↦
        basis.coord i (AffineMap.lineMap x y r)) := by
    simpa only [AffineMap.apply_lineMap] using
      (AffineMap.lineMap_continuous
        (p := basis.coord i x) (q := basis.coord i y))
  have hexZero : ∃ i : (sigma : Set E),
      basis.coord i (AffineMap.lineMap x y a) = 0 := by
    by_contra hnoZero
    have haPos : ∀ i : (sigma : Set E),
        0 < basis.coord i (AffineMap.lineMap x y a) := by
      intro i
      exact lt_of_le_of_ne (haNonneg i) (Ne.symm (by
        intro hi
        exact hnoZero ⟨i, hi⟩))
    let U : Set ℝ := {r | ∀ i : (sigma : Set E),
      0 < basis.coord i (AffineMap.lineMap x y r)}
    have hUOpen : IsOpen U := by
      rw [show U = ⋂ i : (sigma : Set E),
          (fun r : ℝ ↦ basis.coord i (AffineMap.lineMap x y r)) ⁻¹'
            Set.Ioi 0 by
        ext r
        simp [U]]
      exact isOpen_iInter_of_finite fun i ↦
        isOpen_Ioi.preimage (hcoordContinuous i)
    have haU : a ∈ U := haPos
    by_cases haOne : a = 1
    · have hN : U ∩ Set.Ioi (0 : ℝ) ∈ 𝓝 a :=
        inter_mem (hUOpen.mem_nhds haU)
          (Ioi_mem_nhds (by simp [haOne]))
      obtain ⟨r, ⟨hrU, hrPos⟩, hra⟩ :=
        nonempty_nhds_inter_Iio hN (by simp)
      change 0 < r at hrPos
      change r < a at hra
      have hrK : r ∈ K := by
        refine ⟨⟨hrPos.le, ?_⟩, ?_⟩
        · simpa [haOne] using hra.le
        · rw [realization_eq_nonneg_coord sigma hgeneric hcard]
          exact fun i ↦ (hrU i).le
      have hraEq : r = a := by simpa [hKsingleton] using hrK
      exact (hra.ne hraEq)
    · have haLtOne : a < 1 := lt_of_le_of_ne haBounds.2 haOne
      have hN : U ∩ Set.Iio (1 : ℝ) ∈ 𝓝 a :=
        inter_mem (hUOpen.mem_nhds haU) (Iio_mem_nhds haLtOne)
      obtain ⟨r, ⟨hrU, hrLtOne⟩, har⟩ :=
        nonempty_nhds_inter_Ioi hN (by simp)
      change r < 1 at hrLtOne
      change a < r at har
      have hrK : r ∈ K := by
        refine ⟨⟨haBounds.1.trans har.le, hrLtOne.le⟩, ?_⟩
        rw [realization_eq_nonneg_coord sigma hgeneric hcard]
        exact fun i ↦ (hrU i).le
      have hraEq : r = a := by simpa [hKsingleton] using hrK
      exact (har.ne' hraEq)
  obtain ⟨i, hiZero⟩ := hexZero
  have haZero : a ≠ 0 := by
    intro ha
    have hxRealization : x ∈ realization sigma := by
      have haRealization : AffineMap.lineMap x y a ∈ realization sigma := haK.2
      simpa [ha] using haRealization
    exact (endpoint_coord_ne_zero sigma hgeneric hcard
      (x := x) (y := y) (z := x) (by simp) hgp hxRealization i)
      (by simpa [ha] using hiZero)
  have haOne : a ≠ 1 := by
    intro ha
    have hyRealization : y ∈ realization sigma := by
      have haRealization : AffineMap.lineMap x y a ∈ realization sigma := haK.2
      simpa [ha] using haRealization
    exact (endpoint_coord_ne_zero sigma hgeneric hcard
      (x := x) (y := y) (z := y) (by simp) hgp hyRealization i)
      (by simpa [ha] using hiZero)
  have haPos : 0 < a := lt_of_le_of_ne haBounds.1 (Ne.symm haZero)
  have haLtOne : a < 1 := lt_of_le_of_ne haBounds.2 haOne
  have hotherPos (j : (sigma : Set E)) (hji : j ≠ i) :
      0 < basis.coord j (AffineMap.lineMap x y a) := by
    have hjNe : basis.coord j (AffineMap.lineMap x y a) ≠ 0 := by
      intro hjZero
      have hij := unique_zero_coord_on_segmentParameters
        sigma hgeneric hcard hgp haK hiZero hjZero
      exact hji hij.symm
    exact lt_of_le_of_ne (haNonneg j) (Ne.symm hjNe)
  let U : Set ℝ := {r | ∀ j : (sigma : Set E), j ≠ i →
    0 < basis.coord j (AffineMap.lineMap x y r)}
  have hUOpen : IsOpen U := by
    rw [show U = ⋂ j : (sigma : Set E), ⋂ (_h : j ≠ i),
        (fun r : ℝ ↦ basis.coord j (AffineMap.lineMap x y r)) ⁻¹'
          Set.Ioi 0 by
      ext r
      simp [U]]
    exact isOpen_iInter_of_finite fun j ↦
      isOpen_iInter_of_finite fun _ ↦
        isOpen_Ioi.preimage (hcoordContinuous j)
  have haU : a ∈ U := fun j hji ↦ hotherPos j hji
  have hiScalar : AffineMap.lineMap (basis.coord i x) (basis.coord i y) a = 0 := by
    simpa only [AffineMap.apply_lineMap] using hiZero
  have hside : 0 ≤ basis.coord i x ∨ 0 ≤ basis.coord i y := by
    by_cases hxNonneg : 0 ≤ basis.coord i x
    · exact Or.inl hxNonneg
    · right
      by_contra hyNonneg
      have hxNeg : basis.coord i x < 0 := lt_of_not_ge hxNonneg
      have hyNeg : basis.coord i y < 0 := lt_of_not_ge hyNonneg
      rw [AffineMap.lineMap_apply_ring] at hiScalar
      have hleft : (1 - a) * basis.coord i x < 0 :=
        mul_neg_of_pos_of_neg (sub_pos.mpr haLtOne) hxNeg
      have hright : a * basis.coord i y < 0 :=
        mul_neg_of_pos_of_neg haPos hyNeg
      nlinarith
  rcases hside with hxNonneg | hyNonneg
  · have hN : U ∩ Set.Ioi (0 : ℝ) ∈ 𝓝 a :=
      inter_mem (hUOpen.mem_nhds haU) (Ioi_mem_nhds haPos)
    obtain ⟨r, ⟨hrU, hrPos⟩, hra⟩ :=
      nonempty_nhds_inter_Iio hN (by simp)
    change 0 < r at hrPos
    change r < a at hra
    have hiNonneg : 0 ≤ basis.coord i (AffineMap.lineMap x y r) := by
      let f : ℝ →ᵃ[ℝ] ℝ :=
        AffineMap.lineMap (basis.coord i x) (basis.coord i y)
      have hconvex : Convex ℝ (f ⁻¹' Set.Ici 0) :=
        (convex_Ici 0).affine_preimage f
      have hrSegment : r ∈ segment ℝ 0 a := by
        rw [segment_eq_Icc haPos.le]
        exact ⟨hrPos.le, hra.le⟩
      have hxHalfspace : 0 ∈ f ⁻¹' Set.Ici 0 := by
        change 0 ≤ f 0
        simpa [f] using hxNonneg
      have haHalfspace : a ∈ f ⁻¹' Set.Ici 0 := by
        change 0 ≤ f a
        exact hiScalar.ge
      have hrHalfspace := hconvex.segment_subset
        hxHalfspace haHalfspace hrSegment
      change 0 ≤ f r at hrHalfspace
      simpa only [f, AffineMap.apply_lineMap] using hrHalfspace
    have hrK : r ∈ K := by
      refine ⟨⟨hrPos.le, hra.le.trans haLtOne.le⟩, ?_⟩
      rw [realization_eq_nonneg_coord sigma hgeneric hcard]
      intro j
      by_cases hji : j = i
      · simpa [hji] using hiNonneg
      · exact (hrU j hji).le
    have hraEq : r = a := by simpa [hKsingleton] using hrK
    exact (hra.ne hraEq)
  · have hN : U ∩ Set.Iio (1 : ℝ) ∈ 𝓝 a :=
      inter_mem (hUOpen.mem_nhds haU) (Iio_mem_nhds haLtOne)
    obtain ⟨r, ⟨hrU, hrLtOne⟩, har⟩ :=
      nonempty_nhds_inter_Ioi hN (by simp)
    change r < 1 at hrLtOne
    change a < r at har
    have hiNonneg : 0 ≤ basis.coord i (AffineMap.lineMap x y r) := by
      let f : ℝ →ᵃ[ℝ] ℝ :=
        AffineMap.lineMap (basis.coord i x) (basis.coord i y)
      have hconvex : Convex ℝ (f ⁻¹' Set.Ici 0) :=
        (convex_Ici 0).affine_preimage f
      have hrSegment : r ∈ segment ℝ a 1 := by
        rw [segment_eq_Icc haLtOne.le]
        exact ⟨har.le, hrLtOne.le⟩
      have haHalfspace : a ∈ f ⁻¹' Set.Ici 0 := by
        change 0 ≤ f a
        exact hiScalar.ge
      have hyHalfspace : 1 ∈ f ⁻¹' Set.Ici 0 := by
        change 0 ≤ f 1
        simpa [f] using hyNonneg
      have hrHalfspace := hconvex.segment_subset
        haHalfspace hyHalfspace hrSegment
      change 0 ≤ f r at hrHalfspace
      simpa only [f, AffineMap.apply_lineMap] using hrHalfspace
    have hrK : r ∈ K := by
      refine ⟨⟨haPos.le.trans har.le, hrLtOne.le⟩, ?_⟩
      rw [realization_eq_nonneg_coord sigma hgeneric hcard]
      intro j
      by_cases hji : j = i
      · simpa [hji] using hiNonneg
      · exact (hrU j hji).le
    have hraEq : r = a := by simpa [hKsingleton] using hrK
    exact (har.ne' hraEq)

end FullDimensionalTopological

/-- Point intersection number `sigma · z`, extended by the same membership
formula to every point. -/
noncomputable def pointIntersectionNumber (sigma : Finset E) (z : E) : ZMod 2 :=
  if z ∈ realization sigma then 1 else 0

/-- Facet/segment intersection number `tau · omega`, extended by the same
nonempty-intersection formula to arbitrary finite point sets. -/
noncomputable def faceOneSimplexIntersectionNumber
    (tau omega : Finset E) : ZMod 2 :=
  if (realization tau ∩ realization omega).Nonempty then 1 else 0

omit [DecidableEq E] in theorem pointIntersectionNumber_eq_one_iff
    (sigma : Finset E) (z : E) :
    pointIntersectionNumber sigma z = 1 ↔ z ∈ realization sigma := by
  simp [pointIntersectionNumber]

omit [DecidableEq E] in theorem pointIntersectionNumber_eq_zero_iff
    (sigma : Finset E) (z : E) :
    pointIntersectionNumber sigma z = 0 ↔ z ∉ realization sigma := by
  simp [pointIntersectionNumber]

omit [DecidableEq E] in theorem faceOneSimplexIntersectionNumber_eq_one_iff
    (tau omega : Finset E) :
    faceOneSimplexIntersectionNumber tau omega = 1 ↔
      (realization tau ∩ realization omega).Nonempty := by
  simp [faceOneSimplexIntersectionNumber]

omit [DecidableEq E] in theorem faceOneSimplexIntersectionNumber_eq_zero_iff
    (tau omega : Finset E) :
    faceOneSimplexIntersectionNumber tau omega = 0 ↔
      ¬(realization tau ∩ realization omega).Nonempty := by
  simp [faceOneSimplexIntersectionNumber]

/-- The point-intersection kernel on a literal zero-simplex.  The cardinality
guard makes its intended dimension explicit even for a nonhomogeneous chain. -/
noncomputable def pointSimplexIntersectionNumber
    (sigma zeta : Finset E) : ZMod 2 :=
  if zeta.card = 1 ∧ (realization sigma ∩ realization zeta).Nonempty then 1 else 0

omit [DecidableEq E] in @[simp]
theorem pointSimplexIntersectionNumber_singleton
    (sigma : Finset E) (z : E) :
    pointSimplexIntersectionNumber sigma {z} =
      pointIntersectionNumber sigma z := by
  rw [pointSimplexIntersectionNumber, pointIntersectionNumber]
  simp only [Finset.card_singleton, true_and]
  congr 1
  simp [realization, Set.Nonempty]

/-- Pair two finite `F₂`-chains using an arbitrary simplex kernel. -/
noncomputable def chainPairing
    (kernel : Finset E → Finset E → ZMod 2)
    (c d : Chain E) : ZMod 2 :=
  c.sum fun sigma a ↦
    d.sum fun tau b ↦ a * b * kernel sigma tau

omit [AddCommGroup E] [Module ℝ E] in @[simp]
theorem chainPairing_zero_left
    (kernel : Finset E → Finset E → ZMod 2) (d : Chain E) :
    chainPairing kernel 0 d = 0 := by
  simp [chainPairing]

omit [AddCommGroup E] [Module ℝ E] in @[simp]
theorem chainPairing_zero_right
    (kernel : Finset E → Finset E → ZMod 2) (c : Chain E) :
    chainPairing kernel c 0 = 0 := by
  simp [chainPairing]

omit [AddCommGroup E] [Module ℝ E] in @[simp]
theorem chainPairing_singleton_singleton
    (kernel : Finset E → Finset E → ZMod 2)
    (sigma tau : Finset E) :
    chainPairing kernel (singletonChain sigma) (singletonChain tau) =
      kernel sigma tau := by
  simp [chainPairing, singletonChain]

omit [AddCommGroup E] [Module ℝ E] in theorem chainPairing_add_left
    (kernel : Finset E → Finset E → ZMod 2)
    (c c' d : Chain E) :
    chainPairing kernel (c + c') d =
      chainPairing kernel c d + chainPairing kernel c' d := by
  simp [chainPairing, Finsupp.sum_add_index, add_mul]

omit [AddCommGroup E] [Module ℝ E] in theorem chainPairing_add_right
    (kernel : Finset E → Finset E → ZMod 2)
    (c d d' : Chain E) :
    chainPairing kernel c (d + d') =
      chainPairing kernel c d + chainPairing kernel c d' := by
  rw [chainPairing]
  calc
    c.sum (fun sigma a ↦
        (d + d').sum fun tau b ↦ a * b * kernel sigma tau) =
        c.sum (fun sigma a ↦
          (d.sum fun tau b ↦ a * b * kernel sigma tau) +
            d'.sum fun tau b ↦ a * b * kernel sigma tau) := by
      apply Finsupp.sum_congr
      intro sigma a
      apply Finsupp.sum_add_index'
      · intro tau
        simp
      · intro tau b b'
        simp [mul_add, add_mul]
    _ =
        (c.sum fun sigma a ↦
          d.sum fun tau b ↦ a * b * kernel sigma tau) +
        c.sum fun sigma a ↦
          d'.sum fun tau b ↦ a * b * kernel sigma tau := by
      exact Finsupp.sum_add

omit [AddCommGroup E] [Module ℝ E] in theorem chainPairing_finsetSum_left
    {α : Type*} (kernel : Finset E → Finset E → ZMod 2)
    (s : Finset α) (f : α → Chain E) (d : Chain E) :
    chainPairing kernel (∑ x ∈ s, f x) d =
      ∑ x ∈ s, chainPairing kernel (f x) d := by
  induction s using Finset.induction with
  | empty => simp
  | @insert x s hxs ih =>
      simp [hxs, chainPairing_add_left, ih]

omit [AddCommGroup E] [Module ℝ E] in theorem chainPairing_finsetSum_right
    {α : Type*} (kernel : Finset E → Finset E → ZMod 2)
    (c : Chain E) (s : Finset α) (f : α → Chain E) :
    chainPairing kernel c (∑ x ∈ s, f x) =
      ∑ x ∈ s, chainPairing kernel c (f x) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert x s hxs ih =>
      simp [hxs, chainPairing_add_right, ih]

/-- Intersection of an arbitrary chain with a zero-chain. -/
noncomputable def pointChainIntersection (c d : Chain E) : ZMod 2 :=
  chainPairing pointSimplexIntersectionNumber c d

/-- Intersection of an arbitrary chain with a one-chain.  Homogeneity and
general position are recorded separately, exactly as in the paper. -/
noncomputable def oneChainIntersection (c d : Chain E) : ZMod 2 :=
  chainPairing faceOneSimplexIntersectionNumber c d

@[simp]
theorem pointChainIntersection_singleton
    (sigma : Finset E) (z : E) :
    pointChainIntersection (singletonChain sigma) (singletonChain {z}) =
      pointIntersectionNumber sigma z := by
  simp [pointChainIntersection]

@[simp]
theorem oneChainIntersection_singleton
    (tau omega : Finset E) :
    oneChainIntersection (singletonChain tau) (singletonChain omega) =
      faceOneSimplexIntersectionNumber tau omega := by
  simp [oneChainIntersection]

/-- Intersecting the boundary of one simplex with one one-simplex is the
sum of the facet/segment intersection numbers. -/
theorem oneChainIntersection_boundary_singleton
    (sigma omega : Finset E) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) =
      ∑ v ∈ sigma,
        faceOneSimplexIntersectionNumber (sigma.erase v) omega := by
  rw [boundary_singletonChain, boundarySimplex, oneChainIntersection,
    chainPairing_finsetSum_left]
  simp

/-- Intersecting one simplex with the boundary of a literal one-simplex is
the sum of its two endpoint intersection numbers. -/
theorem pointChainIntersection_singleton_boundary
    (sigma omega : Finset E) (homega : IsMSimplex 1 omega) :
    pointChainIntersection (singletonChain sigma)
        (boundary (singletonChain omega)) =
      ∑ z ∈ omega, pointIntersectionNumber sigma z := by
  have hcard : omega.card = 2 := by
    simpa [IsMSimplex] using homega
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  have heraseX : ({x, y} : Finset E).erase x = {y} := by
    ext p
    simp [hxy]
  have heraseY : ({x, y} : Finset E).erase y = {x} := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [boundary_singletonChain, boundarySimplex, pointChainIntersection,
    chainPairing_finsetSum_right]
  simp only [Finset.sum_insert, Finset.mem_singleton, hxy,
    not_false_eq_true, Finset.sum_singleton, heraseX, heraseY,
    chainPairing_singleton_singleton,
    pointSimplexIntersectionNumber_singleton]
  exact add_comm _ _

/-- The simplex-level equality in Lemma 10.1 has exactly the paper's
boundary-pairing interpretation.  This lemma isolates the chain algebra from
the still-geometric parity statement. -/
theorem lemma10_1_pairing_iff_facet_endpoint_sum
    (sigma omega : Finset E) (homega : IsMSimplex 1 omega) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) =
      pointChainIntersection (singletonChain sigma)
        (boundary (singletonChain omega)) ↔
      (∑ v ∈ sigma,
          faceOneSimplexIntersectionNumber (sigma.erase v) omega) =
        ∑ z ∈ omega, pointIntersectionNumber sigma z := by
  rw [oneChainIntersection_boundary_singleton,
    pointChainIntersection_singleton_boundary sigma omega homega]

/-- In characteristic two, the indicator sum of two distinct members of a
finite set vanishes. -/
theorem sum_two_distinct_indicators_zmod2
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : α) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    (∑ v ∈ s, if v = a ∨ v = b then (1 : ZMod 2) else 0) = 0 := by
  have hba : b ≠ a := Ne.symm hab
  calc
    (∑ v ∈ s, if v = a ∨ v = b then (1 : ZMod 2) else 0) =
        (∑ v ∈ s, if v = a then (1 : ZMod 2) else 0) +
          ∑ v ∈ s, if v = b then (1 : ZMod 2) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hva : v = a <;> by_cases hvb : v = b <;>
        simp [hva, hvb, hab, hba]
    _ = 0 := by
      simp [ha, hb]
      exact ZMod.natCast_self 2

/-- The geometric parity statement underlying Lemma 10.1 for one literal
one-simplex.  The proof reduces the segment/simplex intersection to a compact
parameter interval.  Each internal endpoint contributes exactly one facet;
an endpoint equal to `0` or `1` contributes the corresponding endpoint of the
one-simplex instead. -/
theorem facet_endpoint_parity_pair
    [FiniteDimensional ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E]
    (sigma : Finset E) (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    (x y : E)
    (hgp : OneSimplexInGeneralPosition sigma ({x, y} : Finset E)) :
    (∑ v ∈ sigma,
        faceOneSimplexIntersectionNumber (sigma.erase v) ({x, y} : Finset E)) =
      pointIntersectionNumber sigma x + pointIntersectionNumber sigma y := by
  by_cases hne : (segmentParameters sigma x y).Nonempty
  · let K := segmentParameters sigma x y
    let a := sInf K
    let b := sSup K
    let basis := affineBasisOfGenericFull sigma hgeneric hcard
    have hnondegenerate : a < b := by
      simpa [a, b, K] using
        segmentParameters_nondegenerate_of_generalPosition
          sigma hgeneric hcard hgp hne
    have hK : K = Set.Icc a b := by
      simpa [a, b, K] using
        segmentParameters_eq_Icc_of_nonempty sigma x y hne
    have haK : a ∈ K := by
      rw [hK]
      exact ⟨le_rfl, hnondegenerate.le⟩
    have hbK : b ∈ K := by
      rw [hK]
      exact ⟨hnondegenerate.le, le_rfl⟩
    have hactive (v : E) (hv : v ∈ sigma) :
        (realization (sigma.erase v) ∩
            realization ({x, y} : Finset E)).Nonempty ↔
          basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y a) = 0 ∨
            basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y b) = 0 := by
      rw [facet_inter_pair_nonempty_iff_exists_parameter_coord_eq_zero
        sigma hgeneric hcard hv]
      change (∃ t ∈ segmentParameters sigma x y,
          basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y t) = 0) ↔ _
      constructor
      · rintro ⟨t, ht, htZero⟩
        rcases parameter_eq_inf_or_sup_of_coord_eq_zero
            sigma hgeneric hcard hgp hne
              (by simpa [a, b, K] using hnondegenerate)
              ht ⟨v, hv⟩ (by simpa [basis] using htZero) with htInf | htSup
        · left
          subst t
          simpa [a, K, basis] using htZero
        · right
          subst t
          simpa [b, K, basis] using htZero
      · rintro (haZero | hbZero)
        · exact ⟨a, by simpa [K] using haK, haZero⟩
        · exact ⟨b, by simpa [K] using hbK, hbZero⟩
    have hface (v : E) (hv : v ∈ sigma) :
        faceOneSimplexIntersectionNumber
            (sigma.erase v) ({x, y} : Finset E) =
          if basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y a) = 0 ∨
              basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y b) = 0
            then 1 else 0 := by
      simp only [faceOneSimplexIntersectionNumber, hactive v hv]
    have hxiff : x ∈ realization sigma ↔ a = 0 := by
      rw [← zero_mem_segmentParameters_iff]
      change 0 ∈ K ↔ a = 0
      rw [hK]
      constructor
      · intro h
        exact le_antisymm h.1 haK.1.1
      · intro haZero
        rw [haZero]
        exact ⟨le_rfl, by simpa [haZero] using hnondegenerate.le⟩
    have hyiff : y ∈ realization sigma ↔ b = 1 := by
      rw [← one_mem_segmentParameters_iff]
      change 1 ∈ K ↔ b = 1
      rw [hK]
      constructor
      · intro h
        exact le_antisymm hbK.1.2 h.2
      · intro hbOne
        rw [hbOne]
        exact ⟨by simpa [hbOne] using hnondegenerate.le, le_rfl⟩
    have hxNumber : pointIntersectionNumber sigma x =
        if a = 0 then 1 else 0 := by
      simp only [pointIntersectionNumber, hxiff]
    have hyNumber : pointIntersectionNumber sigma y =
        if b = 1 then 1 else 0 := by
      simp only [pointIntersectionNumber, hyiff]
    have hcoordA_ne_zero_of_eq_zero (haZero : a = 0)
        (v : E) (hv : v ∈ sigma) :
        basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y a) ≠ 0 := by
      have hxRealization : x ∈ realization sigma := hxiff.mpr haZero
      have hxCoord := endpoint_coord_ne_zero sigma hgeneric hcard
        (x := x) (y := y) (z := x) (by simp) hgp hxRealization ⟨v, hv⟩
      intro hzero
      apply hxCoord
      simpa [basis, haZero] using hzero
    have hcoordB_ne_zero_of_eq_one (hbOne : b = 1)
        (v : E) (hv : v ∈ sigma) :
        basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y b) ≠ 0 := by
      have hyRealization : y ∈ realization sigma := hyiff.mpr hbOne
      have hyCoord := endpoint_coord_ne_zero sigma hgeneric hcard
        (x := x) (y := y) (z := y) (by simp) hgp hyRealization ⟨v, hv⟩
      intro hzero
      apply hyCoord
      simpa [basis, hbOne] using hzero
    by_cases haZero : a = 0
    · by_cases hbOne : b = 1
      · calc
          (∑ v ∈ sigma,
              faceOneSimplexIntersectionNumber
                (sigma.erase v) ({x, y} : Finset E)) = 0 := by
              apply Finset.sum_eq_zero
              intro v hv
              rw [hface v hv, if_neg]
              rintro (hA | hB)
              · exact hcoordA_ne_zero_of_eq_zero haZero v hv hA
              · exact hcoordB_ne_zero_of_eq_one hbOne v hv hB
          _ = pointIntersectionNumber sigma x +
                pointIntersectionNumber sigma y := by
              rw [hxNumber, hyNumber]
              simp [haZero, hbOne]
              exact (ZMod.natCast_self 2).symm
      · obtain ⟨ib, hib⟩ := exists_zero_coord_at_parameterSup
          sigma hgeneric hcard x y hne
            (by simpa [a, b, K] using hnondegenerate)
            (by simpa [b, K] using hbOne)
        have hib' : basis.coord ib (AffineMap.lineMap x y b) = 0 := by
          simpa [basis, b, K] using hib
        have hzeroB_iff (v : E) (hv : v ∈ sigma) :
            basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y b) = 0 ↔
              v = ib.1 := by
          constructor
          · intro hvZero
            have hvi := unique_zero_coord_on_segmentParameters
              sigma hgeneric hcard hgp hbK hvZero hib'
            exact congrArg Subtype.val hvi
          · intro hvi
            subst v
            simpa using hib'
        calc
          (∑ v ∈ sigma,
              faceOneSimplexIntersectionNumber
                (sigma.erase v) ({x, y} : Finset E)) =
              ∑ v ∈ sigma, if v = ib.1 then (1 : ZMod 2) else 0 := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [hface v hv]
                apply if_congr
                · constructor
                  · rintro (hA | hB)
                    · exact (hcoordA_ne_zero_of_eq_zero haZero v hv hA).elim
                    · exact (hzeroB_iff v hv).mp hB
                  · intro hvi
                    exact Or.inr ((hzeroB_iff v hv).mpr hvi)
                · rfl
                · rfl
          _ = 1 := by simp
          _ = pointIntersectionNumber sigma x +
                pointIntersectionNumber sigma y := by
              rw [hxNumber, hyNumber]
              simp [haZero, hbOne]
    · obtain ⟨ia, hia⟩ := exists_zero_coord_at_parameterInf
        sigma hgeneric hcard x y hne
          (by simpa [a, b, K] using hnondegenerate)
          (by simpa [a, K] using haZero)
      have hia' : basis.coord ia (AffineMap.lineMap x y a) = 0 := by
        simpa [basis, a, K] using hia
      have hzeroA_iff (v : E) (hv : v ∈ sigma) :
          basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y a) = 0 ↔
            v = ia.1 := by
        constructor
        · intro hvZero
          have hvi := unique_zero_coord_on_segmentParameters
            sigma hgeneric hcard hgp haK hvZero hia'
          exact congrArg Subtype.val hvi
        · intro hvi
          subst v
          simpa using hia'
      by_cases hbOne : b = 1
      · calc
          (∑ v ∈ sigma,
              faceOneSimplexIntersectionNumber
                (sigma.erase v) ({x, y} : Finset E)) =
              ∑ v ∈ sigma, if v = ia.1 then (1 : ZMod 2) else 0 := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [hface v hv]
                apply if_congr
                · constructor
                  · rintro (hA | hB)
                    · exact (hzeroA_iff v hv).mp hA
                    · exact (hcoordB_ne_zero_of_eq_one hbOne v hv hB).elim
                  · intro hvi
                    exact Or.inl ((hzeroA_iff v hv).mpr hvi)
                · rfl
                · rfl
          _ = 1 := by simp
          _ = pointIntersectionNumber sigma x +
                pointIntersectionNumber sigma y := by
              rw [hxNumber, hyNumber]
              simp [haZero, hbOne]
      · obtain ⟨ib, hib⟩ := exists_zero_coord_at_parameterSup
          sigma hgeneric hcard x y hne
            (by simpa [a, b, K] using hnondegenerate)
            (by simpa [b, K] using hbOne)
        have hib' : basis.coord ib (AffineMap.lineMap x y b) = 0 := by
          simpa [basis, b, K] using hib
        have hzeroB_iff (v : E) (hv : v ∈ sigma) :
            basis.coord ⟨v, hv⟩ (AffineMap.lineMap x y b) = 0 ↔
              v = ib.1 := by
          constructor
          · intro hvZero
            have hvi := unique_zero_coord_on_segmentParameters
              sigma hgeneric hcard hgp hbK hvZero hib'
            exact congrArg Subtype.val hvi
          · intro hvi
            subst v
            simpa using hib'
        have hiab : ia ≠ ib := by
          intro hiab
          subst ib
          obtain ⟨j, hji, hjZero⟩ :=
            exists_distinct_zero_coord_at_parameterInf
              sigma hgeneric hcard x y hne
                (by simpa [a, b, K] using hnondegenerate)
                (by simpa [a, K] using haZero) ia hia hib
          have hjiEq := unique_zero_coord_on_segmentParameters
            sigma hgeneric hcard hgp haK hjZero hia'
          exact hji hjiEq
        have hiabVal : ia.1 ≠ ib.1 := by
          intro hval
          exact hiab (Subtype.ext hval)
        calc
          (∑ v ∈ sigma,
              faceOneSimplexIntersectionNumber
                (sigma.erase v) ({x, y} : Finset E)) =
              ∑ v ∈ sigma,
                if v = ia.1 ∨ v = ib.1 then (1 : ZMod 2) else 0 := by
                  apply Finset.sum_congr rfl
                  intro v hv
                  rw [hface v hv]
                  apply if_congr
                  · exact or_congr (hzeroA_iff v hv) (hzeroB_iff v hv)
                  · rfl
                  · rfl
          _ = 0 := sum_two_distinct_indicators_zmod2
            sigma ia.1 ib.1 ia.2 ib.2 hiabVal
          _ = pointIntersectionNumber sigma x +
                pointIntersectionNumber sigma y := by
              rw [hxNumber, hyNumber]
              simp [haZero, hbOne]
  · have hxOutside : x ∉ realization sigma := by
      intro hx
      exact hne ⟨0, (zero_mem_segmentParameters_iff sigma x y).2 hx⟩
    have hyOutside : y ∉ realization sigma := by
      intro hy
      exact hne ⟨1, (one_mem_segmentParameters_iff sigma x y).2 hy⟩
    calc
      (∑ v ∈ sigma,
          faceOneSimplexIntersectionNumber
            (sigma.erase v) ({x, y} : Finset E)) = 0 := by
              apply Finset.sum_eq_zero
              intro v hv
              rw [faceOneSimplexIntersectionNumber, if_neg]
              rw [facet_inter_pair_nonempty_iff_exists_parameter_coord_eq_zero
                sigma hgeneric hcard hv]
              rintro ⟨t, ht, htZero⟩
              exact hne ⟨t, ht⟩
      _ = pointIntersectionNumber sigma x +
            pointIntersectionNumber sigma y := by
          simp [pointIntersectionNumber, hxOutside, hyOutside]

/-- Full-cardinality form of the paper's Lemma 10.1.  This is the actual
boundary/intersection equality, not merely a rewriting equivalence. -/
theorem lemma10_1_fullCard
    [FiniteDimensional ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E]
    (sigma omega : Finset E)
    (hgeneric : IsGeneric sigma)
    (hcard : sigma.card = Module.finrank ℝ E + 1)
    (hgp : OneSimplexInGeneralPosition sigma omega) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) =
      pointChainIntersection (singletonChain sigma)
        (boundary (singletonChain omega)) := by
  have homegaCard : omega.card = 2 := by
    simpa [IsMSimplex] using hgp.1
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp homegaCard
  rw [oneChainIntersection_boundary_singleton,
    pointChainIntersection_singleton_boundary sigma ({x, y} : Finset E) hgp.1]
  rw [facet_endpoint_parity_pair sigma hgeneric hcard x y hgp]
  simp [hxy]

/-- Lemma 10.1 in dimension-indexed form: a generic `n`-simplex in an
`n`-dimensional real vector space satisfies the boundary/intersection
identity against every one-simplex in the paper's exact general position. -/
theorem lemma10_1
    [FiniteDimensional ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E]
    (n : ℕ) (sigma omega : Finset E)
    (hdim : Module.finrank ℝ E = n)
    (hsigma : IsMSimplex n sigma)
    (hgeneric : IsGeneric sigma)
    (hgp : OneSimplexInGeneralPosition sigma omega) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) =
      pointChainIntersection (singletonChain sigma)
        (boundary (singletonChain omega)) := by
  apply lemma10_1_fullCard sigma omega hgeneric
  · simpa [IsMSimplex, hdim] using hsigma
  · exact hgp

/-- General position for an `n`-chain and a zero-chain, including the
homogeneity conditions suppressed by the paper's typed terminology. -/
def PointChainsInGeneralPosition
    (n : ℕ) (c d : Chain E) : Prop :=
  IsMChain n c ∧ IsMChain 0 d ∧
    ∀ sigma ∈ c.support, ∀ zeta ∈ d.support, ∀ z,
      zeta = {z} → PointInGeneralPosition sigma z

/-- General position for an `n`-chain and a one-chain. -/
def OneChainsInGeneralPosition
    (n : ℕ) (c d : Chain E) : Prop :=
  IsMChain n c ∧ IsMChain 1 d ∧
    ∀ sigma ∈ c.support, ∀ omega ∈ d.support,
      OneSimplexInGeneralPosition sigma omega

end EuclideanIntersection
end BeyondSperner
