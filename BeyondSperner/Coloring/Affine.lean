import BeyondSperner.Coloring.Matroid.General
import BeyondSperner.OrientedMatroid.Realizable
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.StdBasis

/-!
# Affine colorings in barycentric coordinates

This file formalizes the coordinate-normal-form content of Theorem 10.8.
An affine point is represented by its barycentric coordinate vector, so all
points lie in the affine hyperplane `∑ i, x i = 1`, and the reference
simplex has vertices `Pi.single i 1`.

Unlike a perturbation argument, the proof labels repeated color vectors by
their source vertices and uses the already proved general oriented-matroid
coloring theorem.  A selected matroid basis is then converted back to an
actual linearly (hence affinely) independent point family and a literal
nonnegative coefficient representation.  Thus repeated input colors are
allowed; the conclusion proves that no repetition survives in the selected
point set.
-/

namespace BeyondSperner
namespace AffineColoring

open Classical Set
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]
  [DecidableEq I] [DecidableEq V]

def HasUnitSum (x : I → ℝ) : Prop := ∑ i, x i = 1

/-- The standard simplex in barycentric coordinates. -/
def IsStandardSimplexPoint (x : I → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ HasUnitSum x

variable (D : SimplexFamily I V)

abbrev Label := D.Vertex ⊕ (I ⊕ Unit)

def basisLabel : I ↪ Label D where
  toFun i := Sum.inr (Sum.inl i)
  inj' := fun _ _ h ↦ Sum.inl.inj (Sum.inr.inj h)

def distinguishedLabel : Label D := Sum.inr (Sum.inr ())

omit [Fintype I] [Fintype V] [DecidableEq I] in theorem distinguishedLabel_notMem_basisLabel :
    distinguishedLabel D ∉ Set.range (basisLabel D) := by
  rintro ⟨i, hi⟩
  have h := Sum.inr.inj hi
  exact Sum.inl_ne_inr h

def vector (c : D.Vertex → I → ℝ) (z : I → ℝ) : Label D → I → ℝ
  | Sum.inl v => c v
  | Sum.inr (Sum.inl i) => Pi.single i 1
  | Sum.inr (Sum.inr _) => z

omit [Fintype I] [Fintype V] in @[simp] theorem vector_basisLabel (c : D.Vertex → I → ℝ) (z : I → ℝ) (i : I) :
    vector D c z (basisLabel D i) = Pi.single i 1 := rfl

omit [Fintype I] [Fintype V] in @[simp] theorem vector_distinguishedLabel (c : D.Vertex → I → ℝ) (z : I → ℝ) :
    vector D c z (distinguishedLabel D) = z := rfl

omit [Fintype V] in theorem vector_unitSum (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hc : ∀ v, HasUnitSum (c v)) (hz : HasUnitSum z) :
    ∀ m, HasUnitSum (vector D c z m) := by
  rintro (v | i | u)
  · exact hc v
  · simp [HasUnitSum, vector]
  · exact hz

noncomputable def basisCoefficients (z : I → ℝ) : Label D → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) => z i
  | Sum.inr (Sum.inr _) => 0

omit [Fintype I] [Fintype V] [DecidableEq I] in theorem basisCoefficients_nonneg (z : I → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∀ m, 0 ≤ basisCoefficients D z m := by
  rintro (v | i | u) <;> simp [basisCoefficients, hz]

omit [Fintype I] [Fintype V] [DecidableEq I] in theorem basisCoefficients_support (z : I → ℝ) :
    RealizableOrientedMatroid.coefficientSupport (basisCoefficients D z) ⊆
      Set.range (basisLabel D) := by
  rintro (v | i | u) h
  · exact (h rfl).elim
  · exact ⟨i, rfl⟩
  · exact (h rfl).elim

theorem combination_basisCoefficients (c : D.Vertex → I → ℝ) (z : I → ℝ) :
    RealizableOrientedMatroid.combination (vector D c z) (basisCoefficients D z) = z := by
  funext i
  simp [RealizableOrientedMatroid.combination, vector, basisCoefficients,
    Pi.single_apply]

theorem no_nonnegative_dependence_of_unitSum
    (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hunit : ∀ m, HasUnitSum (vector D c z m))
    (a : Label D → ℝ) (ha : ∀ m, 0 ≤ a m)
    (hcomb : RealizableOrientedMatroid.combination (vector D c z) a = 0) :
    a = 0 := by
  have hsum : ∑ m, a m = 0 := by
    calc
      ∑ m, a m = ∑ m, ∑ i, a m * vector D c z m i := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← Finset.mul_sum]
        have hm : ∑ i, vector D c z m i = 1 := hunit m
        rw [hm, mul_one]
      _ = ∑ i, ∑ m, a m * vector D c z m i := Finset.sum_comm
      _ = ∑ i, RealizableOrientedMatroid.combination (vector D c z) a i := by
        simp [RealizableOrientedMatroid.combination]
      _ = 0 := by rw [hcomb]; simp
  funext m
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ ↦ ha j)).mp hsum m (Finset.mem_univ m)

omit [DecidableEq I] in
/-- A finitely supported nonnegative coefficient vector of total mass one
is a literal convex combination of the image points.  Coefficients of
labels with equal images are combined fiberwise. -/
theorem mem_convexHull_image_of_coefficients
    {M : Type*} [Fintype M] [DecidableEq M]
    (v : M → I → ℝ) (S : Finset M) (a : M → ℝ) (z : I → ℝ)
    (haNonneg : ∀ m, 0 ≤ a m)
    (haSupport : RealizableOrientedMatroid.coefficientSupport a ⊆ (S : Set M))
    (haSum : ∑ m, a m = 1)
    (haCombination : RealizableOrientedMatroid.combination v a = z) :
    z ∈ convexHull ℝ (S.image v : Set (I → ℝ)) := by
  let w : (I → ℝ) → ℝ := fun y ↦ ∑ m ∈ S with v m = y, a m
  apply Finset.mem_convexHull'.2
  refine ⟨w, ?_, ?_, ?_⟩
  · intro y hy
    exact Finset.sum_nonneg fun m _ ↦ haNonneg m
  · calc
      ∑ y ∈ S.image v, w y = ∑ m ∈ S, a m := by
        exact Finset.sum_fiberwise_of_maps_to
          (fun m hm ↦ Finset.mem_image_of_mem v hm) a
      _ = ∑ m, a m := by
        apply Finset.sum_subset S.subset_univ
        intro m _ hmS
        by_contra ham
        exact hmS (haSupport
          (RealizableOrientedMatroid.mem_coefficientSupport.mpr ham))
      _ = 1 := haSum
  · calc
      ∑ y ∈ S.image v, w y • y = ∑ y ∈ S.image v,
          ∑ m ∈ S with v m = y, a m • v m := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro m hm
        have hmy : v m = y := (Finset.mem_filter.mp hm).2
        rw [hmy]
      _ = ∑ m ∈ S, a m • v m := by
        exact Finset.sum_fiberwise_of_maps_to
          (fun m hm ↦ Finset.mem_image_of_mem v hm) (fun m ↦ a m • v m)
      _ = RealizableOrientedMatroid.combination v a := by
        rw [RealizableOrientedMatroid.combination]
        apply Finset.sum_subset S.subset_univ
        intro m _ hmS
        have ham : a m = 0 := by
          by_contra ham
          exact hmS (haSupport
            (RealizableOrientedMatroid.mem_coefficientSupport.mpr ham))
        simp [ham]
      _ = z := haCombination

/-- An injective image identifies a finite label set with its literal point
set. -/
noncomputable def imageEquivOfInjOn
    {M E : Type*} [DecidableEq M] [DecidableEq E]
    (S : Finset M) (v : M → E) (hv : Set.InjOn v S) :
    ↥(S : Set M) ≃ ↥(S.image v : Set E) :=
  Equiv.ofBijective
    (fun m ↦ ⟨v m, Finset.mem_image.mpr ⟨m, m.2, rfl⟩⟩)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      apply hv x.2 y.2
      exact congrArg Subtype.val hxy,
    by
      intro y
      obtain ⟨m, hmS, hmy⟩ := Finset.mem_image.mp y.2
      refine ⟨⟨m, hmS⟩, ?_⟩
      apply Subtype.ext
      exact hmy⟩

/-- Affine independence descends from an injectively labelled finite
family to the literal image point set. -/
theorem affineIndependent_literalImage
    {M E : Type*} [DecidableEq M] [DecidableEq E]
    [AddCommGroup E] [Module ℝ E]
    (S : Finset M) (v : M → E) (hv : Set.InjOn v S)
    (hAI : AffineIndependent ℝ (fun m : ↥(S : Set M) ↦ v m)) :
    AffineIndependent ℝ (fun y : ↥(S.image v : Set E) ↦ y.1) := by
  let e := imageEquivOfInjOn S v hv
  have hcomp := hAI.comp_embedding e.symm.toEmbedding
  convert hcomp using 1
  funext y
  exact (congrArg Subtype.val (e.apply_symm_apply y)).symm

noncomputable def framework (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hc : ∀ v, HasUnitSum (c v)) (hz : IsStandardSimplexPoint z) :
    MatroidColoring.Framework I (Label D) where
  matroid := RealizableOrientedMatroid.data (vector D c z)
  vertex := basisLabel D
  distinguished := distinguishedLabel D
  basis_isBasis := by
    apply RealizableOrientedMatroid.isBasis_range_of_basis
      (vector D c z) (basisLabel D) (Pi.basisFun ℝ I)
    intro i
    rw [vector_basisLabel, Pi.basisFun_apply]
  distinguished_notMem_basis := distinguishedLabel_notMem_basisLabel D
  acyclic := by
    apply (RealizableOrientedMatroid.isAcyclic_iff_no_nonnegative_dependence
      (vector D c z)).2
    exact no_nonnegative_dependence_of_unitSum D c z
      (vector_unitSum D c z hc hz.2)
  distinguished_mem_convexHull := by
    apply (RealizableOrientedMatroid.memConvexHull_iff_exists_nonnegative_combination
      (vector D c z) (distinguishedLabel_notMem_basisLabel D)).2
    refine ⟨basisCoefficients D z, basisCoefficients_nonneg D z hz.1,
      basisCoefficients_support D z, ?_⟩
    rw [combination_basisCoefficients]
    rfl

noncomputable def coloring (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hc : ∀ v, HasUnitSum (c v)) (hz : IsStandardSimplexPoint z) :
    MatroidColoring.Coloring D (framework D c z hc hz) :=
  fun v => ⟨Sum.inl v, by simp [framework, distinguishedLabel]⟩

noncomputable def completedLabels
    (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hc : ∀ v, HasUnitSum (c v)) (hz : IsStandardSimplexPoint z)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    Finset (Label D) :=
  MatroidColoring.completedImage D (framework D c z hc hz)
    (coloring D c z hc hz) C tau htau

/-- The literal point set in formula (40): colors on `tau`, together with
the standard vertices whose indices lie outside `C`. -/
noncomputable def completedPoints
    (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hc : ∀ v, HasUnitSum (c v)) (hz : IsStandardSimplexPoint z)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    Finset (I → ℝ) :=
  (completedLabels D c z hc hz C tau htau).image (vector D c z)

/-- The right-hand side of formula (40), written directly as a point set. -/
noncomputable def completedPointFormula
    (c : D.Vertex → I → ℝ) (C : Finset I) (tau : Finset V)
    (htau : tau ∈ D.complex C) : Finset (I → ℝ) :=
  tau.attach.image (fun v ↦
      c ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩) ∪
    (Finset.univ \ C).image (fun i ↦ Pi.single i 1)

/-- The label-based construction used in the proof is literally formula
(40), not merely an isomorphic copy of it. -/
theorem completedPoints_eq_formula
    (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hc : ∀ v, HasUnitSum (c v)) (hz : IsStandardSimplexPoint z)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    completedPoints D c z hc hz C tau htau =
      completedPointFormula D c C tau htau := by
  simp only [completedPoints, completedLabels, completedPointFormula,
    MatroidColoring.completedImage, MatroidColoring.colorImage,
    framework, coloring, basisLabel, Finset.image_union, Finset.image_image]
  rfl

/-- The literal coordinate conclusion of Theorem 10.8 for `(C,tau)`.

The selected point set has exactly `|I|` elements, is indexed by an
affinely independent family, and carries an explicit convex coefficient
vector for `z` supported on the formula-(40) label set. -/
def IsSolution
    (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hc : ∀ v, HasUnitSum (c v)) (hz : IsStandardSimplexPoint z)
    (C : Finset I) (tau : Finset V) : Prop :=
  ∃ htau : tau ∈ D.complex C,
    C.Nonempty ∧ tau.card = C.card ∧
      let S := completedLabels D c z hc hz C tau htau
      let X : Set (Label D) := S
      S.card = Fintype.card I ∧
        (completedPoints D c z hc hz C tau htau).card = Fintype.card I ∧
        z ∈ convexHull ℝ
          (completedPoints D c z hc hz C tau htau : Set (I → ℝ)) ∧
        AffineIndependent ℝ
          (fun y : ↥(completedPoints D c z hc hz C tau htau : Set (I → ℝ)) ↦ y.1) ∧
        LinearIndependent ℝ
          (fun m : X ↦ vector D c z m) ∧
        AffineIndependent ℝ
          (fun m : X ↦ vector D c z m) ∧
        ∃ a : Label D → ℝ,
          (∀ m, 0 ≤ a m) ∧
          RealizableOrientedMatroid.coefficientSupport a ⊆ (S : Set (Label D)) ∧
          ∑ m, a m = 1 ∧
          RealizableOrientedMatroid.combination (vector D c z) a = z

/-- Theorem 10.8 in barycentric-coordinate normal form.  The arbitrary-affine-
basis version below transports this result through barycentric coordinates.
No general-position or intersection-number hypothesis is used in this proof. -/
theorem theorem10_8_coordinate
    (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hc : ∀ v, HasUnitSum (c v)) (hz : IsStandardSimplexPoint z)
    (hchain : D.IsChainSimplex) :
    ∃ C : Finset I, ∃ tau : Finset V, IsSolution D c z hc hz C tau := by
  let F := framework D c z hc hz
  let color := coloring D c z hc hz
  obtain ⟨C, tau, htau, hC, hcard, hgood⟩ :=
    MatroidColoring.theorem8_5 D F hchain color
  let S : Finset (Label D) := completedLabels D c z hc hz C tau htau
  let X : Set (Label D) := S
  have hSeq : S = MatroidColoring.completedImage D F color C tau htau := rfl
  have hXeq : X =
      (MatroidColoring.completedImage D F color C tau htau : Set (Label D)) := by
    rw [show X = (S : Set (Label D)) by rfl, hSeq]
  have hScard : S.card = Fintype.card I := by
    apply F.card_eq_card_index_of_isBasis S
    simpa [hSeq] using hgood.1
  have hLI : LinearIndependent ℝ
      (fun m : X ↦ vector D c z m) := by
    apply (RealizableOrientedMatroid.isIndependent_iff_linearIndependent
      (vector D c z) X).1
    rw [hXeq]
    simpa [F, framework] using hgood.1.1
  have hPointCard : (completedPoints D c z hc hz C tau htau).card =
      Fintype.card I := by
    rw [completedPoints, Finset.card_image_of_injOn]
    · exact hScard
    · intro x hx y hy hxy
      let x' : X := ⟨x, hx⟩
      let y' : X := ⟨y, hy⟩
      have hsub : x' = y' := hLI.injective hxy
      exact congrArg Subtype.val hsub
  have hinjOn : Set.InjOn (vector D c z) S := by
    intro x hx y hy hxy
    let x' : X := ⟨x, hx⟩
    let y' : X := ⟨y, hy⟩
    have hxy' : vector D c z x' = vector D c z y' := hxy
    exact congrArg Subtype.val (hLI.injective hxy')
  have hPointAI : AffineIndependent ℝ
      (fun y : ↥(completedPoints D c z hc hz C tau htau : Set (I → ℝ)) ↦ y.1) := by
    exact affineIndependent_literalImage S (vector D c z) hinjOn
      hLI.affineIndependent
  have hbNotS : distinguishedLabel D ∉ S := by
    rw [hSeq]
    intro hb
    rcases Finset.mem_union.mp hb with hbColor | hbBasis
    · obtain ⟨v, _, hvb⟩ := Finset.mem_image.mp hbColor
      exact (color ⟨v.1,
        MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩).2 hvb
    · obtain ⟨i, _, hib⟩ := Finset.mem_image.mp hbBasis
      exact F.distinguished_notMem_basis ⟨i, hib⟩
  obtain ⟨a, haNonneg, haSupport, haCombination⟩ :=
    (RealizableOrientedMatroid.memConvexHull_iff_exists_nonnegative_combination
      (vector D c z) hbNotS).1 (by simpa [F, framework, hSeq] using hgood.2)
  have haCombinationZ :
      RealizableOrientedMatroid.combination (vector D c z) a = z := by
    simpa using haCombination
  have haSum : ∑ m, a m = 1 := by
    calc
      ∑ m, a m = ∑ m, ∑ i, a m * vector D c z m i := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← Finset.mul_sum]
        have hm : ∑ i, vector D c z m i = 1 :=
          vector_unitSum D c z hc hz.2 m
        rw [hm, mul_one]
      _ = ∑ i, ∑ m, a m * vector D c z m i := Finset.sum_comm
      _ = ∑ i, RealizableOrientedMatroid.combination (vector D c z) a i := by
        simp [RealizableOrientedMatroid.combination]
      _ = ∑ i, z i := by rw [haCombinationZ]
      _ = 1 := hz.2
  have hzConvex : z ∈ convexHull ℝ
      (completedPoints D c z hc hz C tau htau : Set (I → ℝ)) := by
    exact mem_convexHull_image_of_coefficients (I := I)
      (vector D c z) S a z haNonneg haSupport haSum haCombinationZ
  refine ⟨C, tau, htau, hC, hcard, ?_⟩
  change S.card = Fintype.card I ∧ _
  exact ⟨hScard, hPointCard, hzConvex, hPointAI,
    hLI, hLI.affineIndependent, a,
    haNonneg, haSupport, haSum, haCombinationZ⟩

section AffineTransport

variable {P : Type*} [AddCommGroup P] [Module ℝ P]

/-- Barycentric-coordinate affine map associated with an affine basis. -/
noncomputable def coordinateMap (b : AffineBasis I ℝ P) : P →ᵃ[ℝ] (I → ℝ) :=
  AffineMap.pi fun i ↦ b.coord i

omit [Fintype I] [DecidableEq I] in @[simp]
theorem coordinateMap_apply (b : AffineBasis I ℝ P) (p : P) (i : I) :
    coordinateMap b p i = b.coord i p := rfl

omit [Fintype I] in @[simp]
theorem coordinateMap_basis (b : AffineBasis I ℝ P) (i : I) :
    coordinateMap b (b i) = Pi.single i 1 := by
  funext j
  rw [coordinateMap_apply, b.coord_apply]
  by_cases h : i = j
  · simp [h]
  · simp [Ne.symm h]

omit [DecidableEq I] in theorem coordinateMap_injective (b : AffineBasis I ℝ P) :
    Function.Injective (coordinateMap b) := by
  intro x y hxy
  apply b.ext_elem
  intro i
  exact congrFun hxy i

/-- Formula (40) in an arbitrary affine space with affine basis `b`. -/
noncomputable def affineCompletedPointFormula
    (b : AffineBasis I ℝ P) (c : D.Vertex → P)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) : Finset P :=
  tau.attach.image (fun v ↦
      c ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩) ∪
    (Finset.univ \ C).image b

omit [Fintype V] in
/-- Barycentric coordinates carry the arbitrary-basis formula (40) to its
standard-coordinate version exactly. -/
theorem image_affineCompletedPointFormula_coordinateMap
    (b : AffineBasis I ℝ P) (c : D.Vertex → P)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    (affineCompletedPointFormula D b c C tau htau).image (coordinateMap b) =
      completedPointFormula D (fun v i ↦ b.coord i (c v)) C tau htau := by
  simp only [affineCompletedPointFormula, completedPointFormula,
    Finset.image_union, Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro i hi
  exact coordinateMap_basis b i

/-- The literal arbitrary-affine-basis conclusion of Theorem 10.8. -/
def IsAffineSolution
    (b : AffineBasis I ℝ P) (c : D.Vertex → P) (z : P)
    (C : Finset I) (tau : Finset V) : Prop :=
  ∃ htau : tau ∈ D.complex C,
    C.Nonempty ∧ tau.card = C.card ∧
      let S := affineCompletedPointFormula D b c C tau htau
      S.card = Fintype.card I ∧
        z ∈ convexHull ℝ (S : Set P) ∧
        AffineIndependent ℝ (fun p : ↥(S : Set P) ↦ p.1)

/-- Theorem 10.8 in the paper's arbitrary affine-basis form.  The proof
transports to barycentric coordinates, applies `theorem10_8_coordinate`,
and transports cardinality, convex-hull membership, and affine
independence back along the injective affine coordinate map. -/
theorem theorem10_8
    (b : AffineBasis I ℝ P) (c : D.Vertex → P) (z : P)
    (hz : z ∈ convexHull ℝ (Set.range b))
    (hchain : D.IsChainSimplex) :
    ∃ C : Finset I, ∃ tau : Finset V,
      IsAffineSolution D b c z C tau := by
  let cc : D.Vertex → I → ℝ := fun v i ↦ b.coord i (c v)
  let zz : I → ℝ := fun i ↦ b.coord i z
  have hcc : ∀ v, HasUnitSum (cc v) := by
    intro v
    exact b.sum_coord_apply_eq_one (c v)
  have hzzNonneg : ∀ i, 0 ≤ zz i := by
    have hz' := hz
    rw [b.convexHull_eq_nonneg_coord] at hz'
    exact hz'
  have hzz : IsStandardSimplexPoint zz :=
    ⟨hzzNonneg, b.sum_coord_apply_eq_one z⟩
  obtain ⟨C, tau, hsol⟩ :=
    theorem10_8_coordinate D cc zz hcc hzz hchain
  rcases hsol with ⟨htau, hC, hcard, hdata⟩
  dsimp only at hdata
  rcases hdata with
    ⟨hLabelCard, hQCard, hzQ, hQAI, hQLI, hQAILabel,
      a, haNonneg, haSupport, haSum, haCombination⟩
  let S : Finset P := affineCompletedPointFormula D b c C tau htau
  let Q : Finset (I → ℝ) := completedPoints D cc zz hcc hzz C tau htau
  have himage : S.image (coordinateMap b) = Q := by
    calc
      S.image (coordinateMap b) =
          completedPointFormula D cc C tau htau := by
        exact image_affineCompletedPointFormula_coordinateMap D b c C tau htau
      _ = Q := (completedPoints_eq_formula D cc zz hcc hzz C tau htau).symm
  have hSCard : S.card = Fintype.card I := by
    calc
      S.card = (S.image (coordinateMap b)).card :=
        (Finset.card_image_of_injOn (coordinateMap_injective b).injOn).symm
      _ = Q.card := congrArg Finset.card himage
      _ = Fintype.card I := hQCard
  have hzImage : coordinateMap b z ∈
      convexHull ℝ (S.image (coordinateMap b) : Set (I → ℝ)) := by
    rw [himage]
    exact hzQ
  have hzConvex : z ∈ convexHull ℝ (S : Set P) := by
    have hzInImage : coordinateMap b z ∈
        coordinateMap b '' convexHull ℝ (S : Set P) := by
      rw [(coordinateMap b).image_convexHull]
      simpa only [Finset.coe_image] using hzImage
    obtain ⟨p, hp, hpz⟩ := hzInImage
    have hpEq : p = z := coordinateMap_injective b hpz
    simpa [hpEq] using hp
  have hImageAI : AffineIndependent ℝ
      (fun y : ↥(S.image (coordinateMap b) : Set (I → ℝ)) ↦ y.1) := by
    rw [himage]
    exact hQAI
  have hinjOn : Set.InjOn (coordinateMap b) S :=
    (coordinateMap_injective b).injOn
  let e := imageEquivOfInjOn S (coordinateMap b) hinjOn
  have hMappedAI : AffineIndependent ℝ
      (fun p : ↥(S : Set P) ↦ coordinateMap b p.1) := by
    have hcomp := hImageAI.comp_embedding e.toEmbedding
    convert hcomp using 1
    funext p
    rfl
  have hSAI : AffineIndependent ℝ (fun p : ↥(S : Set P) ↦ p.1) := by
    apply ((coordinateMap b).affineIndependent_iff
      (coordinateMap_injective b)).1
    exact hMappedAI
  exact ⟨C, tau, htau, hC, hcard, hSCard, hzConvex, hSAI⟩

end AffineTransport

end AffineColoring
end BeyondSperner
