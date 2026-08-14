import BeyondSperner.Coloring.Affine

/-!
# Inward tangent colorings

This file develops the algebraic core of Theorem 10.10.  The key point is
not hidden in a positivity interface: after applying Theorem 10.8 at the
barycenter, we sum the centered barycentric coordinates outside the selected
index set.  Every selected color contributes a nonnegative number, whereas
every remaining reference vertex contributes the same strictly positive
number.  Hence all coefficients of the remaining reference vertices vanish.
-/

namespace BeyondSperner
namespace AffineColoring

open Classical Set
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]
  [DecidableEq I] [DecidableEq V] [Nonempty I]

/-- The barycenter of the standard simplex in barycentric coordinates. -/
noncomputable def barycentricCenter : I → ℝ :=
  fun _ ↦ (Fintype.card I : ℝ)⁻¹

omit [DecidableEq I] in theorem barycentricCenter_isStandardSimplexPoint :
    IsStandardSimplexPoint (barycentricCenter (I := I)) := by
  have hcardPos : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  constructor
  · intro i
    exact (inv_pos.mpr hcardPos).le
  · simp [HasUnitSum, barycentricCenter, ne_of_gt hcardPos]

variable (D : SimplexFamily I V)

/-- The old-vertex labels belonging to a simplex `tau` of `D(C)`. -/
noncomputable def simplexColorLabels
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    Finset (Label D) :=
  tau.attach.image fun v ↦
    Sum.inl ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩

/-- The formal reference-vertex labels indexed outside `C`. -/
noncomputable def outsideBasisLabels (C : Finset I) : Finset (Label D) :=
  (Finset.univ \ C).image (basisLabel D)

omit [Nonempty I] in
/-- The completed label set used in Theorem 10.8 splits literally into its
color labels and its reference-vertex labels. -/
theorem completedLabels_eq_color_union_basis
    (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (hc : ∀ v, HasUnitSum (c v)) (hz : IsStandardSimplexPoint z)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    completedLabels D c z hc hz C tau htau =
      simplexColorLabels D C tau htau ∪ outsideBasisLabels D C := by
  simp [completedLabels, MatroidColoring.completedImage,
    MatroidColoring.colorImage, framework, coloring, simplexColorLabels,
    outsideBasisLabels, basisLabel]

/-- The literal set of colors on `tau`. -/
noncomputable def simplexColorPoints
    (c : D.Vertex → I → ℝ)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    Finset (I → ℝ) :=
  tau.attach.image fun v ↦
    c ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩

omit [Fintype V] [Nonempty I] in theorem image_simplexColorLabels_vector
    (c : D.Vertex → I → ℝ) (z : I → ℝ)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    (simplexColorLabels D C tau htau).image (vector D c z) =
      simplexColorPoints D c C tau htau := by
  rw [simplexColorLabels, simplexColorPoints, Finset.image_image]
  apply Finset.image_congr
  intro v hv
  rfl

/-- Sum of the barycentric coordinates centered at the standard barycenter,
over the indices outside `C`. -/
noncomputable def centeredOutsideSum (C : Finset I) (x : I → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ \ C, (x i - barycentricCenter (I := I) i)

/-- A reference vertex indexed outside `C` has centered outside-coordinate
sum `|C| / |I|`. -/
theorem centeredOutsideSum_basis (C : Finset I) {k : I}
    (hk : k ∈ Finset.univ \ C) :
    centeredOutsideSum C (Pi.single k 1) =
      (C.card : ℝ) * (Fintype.card I : ℝ)⁻¹ := by
  have hcardNat : (Finset.univ \ C).card + C.card = Fintype.card I :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
  have hcardReal :
      ((Finset.univ \ C).card : ℝ) + (C.card : ℝ) = Fintype.card I := by
    exact_mod_cast hcardNat
  have hcardNe : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsingle : ∑ i ∈ Finset.univ \ C, Pi.single k 1 i = (1 : ℝ) := by
    simp [Pi.single_apply, hk]
  rw [centeredOutsideSum]
  simp_rw [barycentricCenter]
  rw [Finset.sum_sub_distrib, hsingle]
  simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    1 - ((Finset.univ \ C).card : ℝ) * (Fintype.card I : ℝ)⁻¹ =
        (((Finset.univ \ C).card : ℝ) + (C.card : ℝ)) *
            (Fintype.card I : ℝ)⁻¹ -
          ((Finset.univ \ C).card : ℝ) * (Fintype.card I : ℝ)⁻¹ := by
      rw [hcardReal, mul_inv_cancel₀ hcardNe]
    _ = (C.card : ℝ) * (Fintype.card I : ℝ)⁻¹ := by ring

theorem centeredOutsideSum_basis_pos (C : Finset I) (hC : C.Nonempty)
    {k : I} (hk : k ∈ Finset.univ \ C) :
    0 < centeredOutsideSum C (Pi.single k 1) := by
  rw [centeredOutsideSum_basis C hk]
  have hCPos : (0 : ℝ) < C.card := by
    exact_mod_cast Finset.card_pos.mpr hC
  have hIPos : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  exact mul_pos hCPos (inv_pos.mpr hIPos)

/-- Coordinate form of the algebraic core of Theorem 10.10.

The boundary hypothesis is exactly the centered-coordinate version of the
inward-tangent condition for vertices of a simplex in `D(C)`.  The conclusion
contains no formal reference vertices: the standard barycenter is already in
the convex hull of the colors on `tau`. -/
theorem theorem10_10_coordinate_core
    (c : D.Vertex → I → ℝ)
    (hc : ∀ v, HasUnitSum (c v))
    (hchain : D.IsChainSimplex)
    (hboundary : ∀ (C : Finset I) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C,
        0 ≤ c v i - barycentricCenter (I := I) i) :
    ∃ C : Finset I, ∃ tau : Finset V, ∃ htau : tau ∈ D.complex C,
      C.Nonempty ∧ tau.card = C.card ∧
        barycentricCenter (I := I) ∈
          convexHull ℝ (simplexColorPoints D c C tau htau : Set (I → ℝ)) := by
  let z : I → ℝ := barycentricCenter (I := I)
  have hz : IsStandardSimplexPoint z :=
    barycentricCenter_isStandardSimplexPoint (I := I)
  obtain ⟨C, tau, hsol⟩ := theorem10_8_coordinate D c z hc hz hchain
  rcases hsol with ⟨htau, hC, htauCard, hdata⟩
  dsimp only at hdata
  rcases hdata with
    ⟨_hLabelCard, _hPointCard, _hzConvex, _hPointAI, _hLI,
      _hAILabel, a, haNonneg, haSupport, haSum, haCombination⟩
  let S : Finset (Label D) := completedLabels D c z hc hz C tau htau
  let L : Finset (Label D) := simplexColorLabels D C tau htau
  let B : Finset (Label D) := outsideBasisLabels D C
  let g : Label D → ℝ := fun m ↦ centeredOutsideSum C (vector D c z m)
  have hS : S = L ∪ B := by
    exact completedLabels_eq_color_union_basis D c z hc hz C tau htau
  have haZeroOutside {m : Label D} (hm : m ∉ S) : a m = 0 := by
    by_contra ham
    exact hm (haSupport
      (RealizableOrientedMatroid.mem_coefficientSupport.mpr ham))
  have htermNonneg : ∀ m : Label D, 0 ≤ a m * g m := by
    intro m
    by_cases hmS : m ∈ S
    · rw [hS] at hmS
      rcases Finset.mem_union.mp hmS with hmL | hmB
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hmL
        apply mul_nonneg (haNonneg _)
        change 0 ≤ centeredOutsideSum C
          (c ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩)
        rw [centeredOutsideSum]
        apply Finset.sum_nonneg
        intro i hi
        exact hboundary C tau htau
          ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩
          v.2 i hi
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmB
        exact mul_nonneg (haNonneg _)
          (centeredOutsideSum_basis_pos C hC hi).le
    · rw [haZeroOutside hmS]
      simp
  have hcombinationCoord (i : I) :
      ∑ m, a m * vector D c z m i = z i := by
    have hi := congrFun haCombination i
    simpa [RealizableOrientedMatroid.combination, smul_eq_mul] using hi
  have hcenteredCoord (i : I) :
      ∑ m, a m * (vector D c z m i - z i) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hcombinationCoord, ← Finset.sum_mul, haSum]
    ring
  have htotal : ∑ m, a m * g m = 0 := by
    simp_rw [g, centeredOutsideSum, z, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ ↦ hcenteredCoord i
  have htermZero (m : Label D) : a m * g m = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ htermNonneg j)).mp htotal m (Finset.mem_univ m)
  have haBasisZero : ∀ i ∈ Finset.univ \ C, a (basisLabel D i) = 0 := by
    intro i hi
    have hzero := htermZero (basisLabel D i)
    have hgPos : 0 < g (basisLabel D i) := by
      exact centeredOutsideSum_basis_pos C hC hi
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hgPos)
  have haSupportColors :
      RealizableOrientedMatroid.coefficientSupport a ⊆ (L : Set (Label D)) := by
    intro m hm
    have hmS : m ∈ S := haSupport hm
    rw [hS] at hmS
    rcases Finset.mem_union.mp hmS with hmL | hmB
    · exact hmL
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmB
      exact False.elim ((RealizableOrientedMatroid.mem_coefficientSupport.mp hm)
        (haBasisZero i hi))
  have hzColors : z ∈ convexHull ℝ
      (L.image (vector D c z) : Set (I → ℝ)) := by
    exact mem_convexHull_image_of_coefficients (I := I)
      (vector D c z) L a z haNonneg haSupportColors haSum haCombination
  refine ⟨C, tau, htau, hC, htauCard, ?_⟩
  rw [image_simplexColorLabels_vector D c z C tau htau] at hzColors
  exact hzColors

section AffineVersion

variable {P : Type*} [AddCommGroup P] [Module ℝ P]

/-- The normalization imposed in Section 10 before Theorem 10.10: the
reference simplex has barycenter zero. -/
def IsCenteredAffineBasis (b : AffineBasis I ℝ P) : Prop :=
  ∑ i, b i = 0

omit [DecidableEq I] in
/-- For a centered affine basis, the barycentric coordinates of zero are
all `1 / |I|`. -/
theorem coord_zero_eq_inv_card (b : AffineBasis I ℝ P)
    (hb : IsCenteredAffineBasis b) (i : I) :
    b.coord i 0 = (Fintype.card I : ℝ)⁻¹ := by
  let w : I → ℝ := fun _ ↦ (Fintype.card I : ℝ)⁻¹
  have hcardPos : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hw : ∑ j, w j = 1 := by
    simp [w, ne_of_gt hcardPos]
  have hcomb : Finset.univ.affineCombination ℝ b w = 0 := by
    rw [Finset.affineCombination_eq_linear_combination Finset.univ b w hw]
    simp only [w]
    rw [← Finset.smul_sum, hb, smul_zero]
  calc
    b.coord i 0 = b.coord i (Finset.univ.affineCombination ℝ b w) := by rw [hcomb]
    _ = w i := b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
    _ = (Fintype.card I : ℝ)⁻¹ := rfl

omit [DecidableEq I] in theorem coordinateMap_zero_eq_barycentricCenter
    (b : AffineBasis I ℝ P) (hb : IsCenteredAffineBasis b) :
    coordinateMap b 0 = barycentricCenter (I := I) := by
  funext i
  exact coord_zero_eq_inv_card b hb i

/-- Literal color set in the ambient affine space. -/
noncomputable def affineSimplexColorPoints
    (c : D.Vertex → P)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    Finset P :=
  tau.attach.image fun v ↦
    c ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩

omit [Fintype V] [DecidableEq I] [Nonempty I] in
/-- Barycentric coordinates carry the literal ambient color set to the
coordinate color set exactly. -/
theorem image_affineSimplexColorPoints_coordinateMap
    (b : AffineBasis I ℝ P) (c : D.Vertex → P)
    (C : Finset I) (tau : Finset V) (htau : tau ∈ D.complex C) :
    (affineSimplexColorPoints D c C tau htau).image (coordinateMap b) =
      simplexColorPoints D (fun v i ↦ b.coord i (c v)) C tau htau := by
  rw [affineSimplexColorPoints, simplexColorPoints, Finset.image_image]
  apply Finset.image_congr
  intro v hv
  rfl

/-- The paper's inward-tangent boundary condition, stated using the actual
vertex position `p v`: whenever that position lies on the `i`th reference
face, adding the color vector stays in the inward half-space. -/
def IsInwardTangentColoring
    (b : AffineBasis I ℝ P) (p c : D.Vertex → P) : Prop :=
  ∀ v i, b.coord i (p v) = 0 → 0 ≤ b.coord i (c v +ᵥ p v)

omit [Fintype V] in
/-- Remove the artificial reference vertices from a Theorem 10.8 solution at
the center of the reference simplex.

This is the coefficient argument used in Theorem 10.10, stated against the
public `IsAffineSolution` interface rather than the stronger coordinate
solution structure.  Convex-hull membership supplies nonnegative weights.
The centered outside-coordinate sum is nonnegative on every color, strictly
positive on every artificial basis vertex, and zero at the target.  Hence
every artificial-vertex weight is zero. -/
theorem zero_mem_colorHull_of_affineSolution
    (b : AffineBasis I ℝ P) (hb : IsCenteredAffineBasis b)
    (c : D.Vertex → P)
    (C : Finset I) (tau : Finset V)
    (hsol : IsAffineSolution D b c 0 C tau)
    (hboundary : ∀ (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C,
        0 ≤ b.coord i (c v) - barycentricCenter (I := I) i) :
    ∃ htau : tau ∈ D.complex C,
      C.Nonempty ∧ tau.card = C.card ∧
        (0 : P) ∈ convexHull ℝ
          (affineSimplexColorPoints D c C tau htau : Set P) := by
  rcases hsol with ⟨htau, hC, htauCard, hdata⟩
  dsimp only at hdata
  rcases hdata with ⟨_hSCard, hzero, _hAI⟩
  let Q : Finset P := affineSimplexColorPoints D c C tau htau
  let B : Finset P := (Finset.univ \ C).image b
  let S : Finset P := affineCompletedPointFormula D b c C tau htau
  let g : P → ℝ := fun q ↦ centeredOutsideSum C (coordinateMap b q)
  have hS : S = Q ∪ B := rfl
  rw [Finset.convexHull_eq] at hzero
  obtain ⟨w, hwNonneg, hwSum, hwCenter⟩ := hzero
  change (∀ y ∈ S, 0 ≤ w y) at hwNonneg
  change ∑ y ∈ S, w y = 1 at hwSum
  change S.centerMass w id = 0 at hwCenter
  have hwCombination : ∑ q ∈ S, w q • q = 0 := by
    have hcm := (S.centerMass_eq_of_sum_1 id hwSum).symm.trans hwCenter
    simpa only [id_eq] using hcm
  have hcoordLinear (q : P) (i : I) :
      b.coord i q - barycentricCenter (I := I) i =
        (b.coord i).linear q := by
    rw [show barycentricCenter (I := I) i = b.coord i 0 by
      symm
      exact coord_zero_eq_inv_card b hb i]
    have hmap := (b.coord i).map_vadd (0 : P) q
    rw [vadd_eq_add] at hmap
    simpa using sub_eq_iff_eq_add.mpr hmap
  have htotal : ∑ q ∈ S, w q * g q = 0 := by
    simp_rw [g, centeredOutsideSum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    calc
      ∑ q ∈ S,
          w q * (coordinateMap b q i - barycentricCenter (I := I) i) =
          ∑ q ∈ S, (b.coord i).linear (w q • q) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [coordinateMap_apply, hcoordLinear,
              LinearMap.map_smul, smul_eq_mul]
      _ = (b.coord i).linear (∑ q ∈ S, w q • q) := by
        rw [map_sum]
      _ = 0 := by rw [hwCombination, map_zero]
  have htermNonneg : ∀ q ∈ S, 0 ≤ w q * g q := by
    intro q hq
    apply mul_nonneg (hwNonneg q hq)
    rw [hS] at hq
    rcases Finset.mem_union.mp hq with hqQ | hqB
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hqQ
      change 0 ≤ centeredOutsideSum C
        (coordinateMap b
          (c ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩))
      rw [centeredOutsideSum]
      apply Finset.sum_nonneg
      intro i hi
      exact hboundary htau
        ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩
        v.2 i hi
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hqB
      change 0 ≤ centeredOutsideSum C (coordinateMap b (b i))
      rw [coordinateMap_basis b i]
      exact (centeredOutsideSum_basis_pos C hC hi).le
  have htermZero {q : P} (hq : q ∈ S) : w q * g q = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg htermNonneg).mp htotal q hq
  have hwBasisZero : ∀ i ∈ Finset.univ \ C, w (b i) = 0 := by
    intro i hi
    have hbiS : b i ∈ S := by
      rw [hS]
      exact Finset.mem_union_right Q (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hzero := htermZero hbiS
    have hgPos : 0 < g (b i) := by
      change 0 < centeredOutsideSum C (coordinateMap b (b i))
      rw [coordinateMap_basis b i]
      exact centeredOutsideSum_basis_pos C hC hi
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hgPos)
  have hQsub : Q ⊆ S := by
    rw [hS]
    exact Finset.subset_union_left
  have hwOutsideZero : ∀ q ∈ S, q ∉ Q → w q = 0 := by
    intro q hqS hqQ
    rw [hS] at hqS
    rcases Finset.mem_union.mp hqS with hqQ' | hqB
    · exact (hqQ hqQ').elim
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hqB
      exact hwBasisZero i hi
  have hwSumQ : ∑ q ∈ Q, w q = 1 := by
    calc
      ∑ q ∈ Q, w q = ∑ q ∈ S, w q :=
        Finset.sum_subset hQsub (fun q hqS hqQ ↦ hwOutsideZero q hqS hqQ)
      _ = 1 := hwSum
  have hwCombinationQ : ∑ q ∈ Q, w q • q = 0 := by
    calc
      ∑ q ∈ Q, w q • q = ∑ q ∈ S, w q • q :=
        Finset.sum_subset hQsub (fun q hqS hqQ ↦ by
          rw [hwOutsideZero q hqS hqQ, zero_smul])
      _ = 0 := hwCombination
  refine ⟨htau, hC, htauCard, ?_⟩
  change (0 : P) ∈ convexHull ℝ (Q : Set P)
  rw [Finset.convexHull_eq]
  refine ⟨w, ?_, hwSumQ, ?_⟩
  · intro q hq
    exact hwNonneg q (hQsub hq)
  · rw [Q.centerMass_eq_of_sum_1 id hwSumQ]
    exact hwCombinationQ

omit [Fintype V] in
/-- The geometric inward-tangent condition implies the centered-coordinate
nonnegativity condition used by the coefficient argument in Theorem 10.10. -/
theorem centeredBoundary_of_inward
    (b : AffineBasis I ℝ P) (hb : IsCenteredAffineBasis b)
    (p c : D.Vertex → P)
    (hface : ∀ (C : Finset I) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hinward : IsInwardTangentColoring D b p c) :
    ∀ (C : Finset I) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C,
        0 ≤ b.coord i (c v) - barycentricCenter (I := I) i := by
  intro C tau htau v hv i hi
  have hpZero : b.coord i (p v) = 0 := hface C tau htau v hv i hi
  have hIn : 0 ≤ b.coord i (c v +ᵥ p v) := hinward v i hpZero
  have hLinearNonneg : 0 ≤ (b.coord i).linear (c v) := by
    rw [AffineMap.map_vadd, hpZero] at hIn
    simpa [vadd_eq_add] using hIn
  have hCoordLinear :
      b.coord i (c v) - b.coord i 0 = (b.coord i).linear (c v) := by
    have hmap := (b.coord i).map_vadd (0 : P) (c v)
    rw [vadd_eq_add] at hmap
    simpa using sub_eq_iff_eq_add.mpr hmap
  rw [show barycentricCenter (I := I) i = b.coord i 0 by
    symm
    exact coord_zero_eq_inv_card b hb i]
  rw [hCoordLinear]
  exact hLinearNonneg

omit [Fintype V] in
/-- Theorem 10.10 before top-simplex extension, supplied with any proof of
the public Theorem 10.8 `IsAffineSolution` conclusion at the origin. -/
theorem theorem10_10_core_of_affineSolution
    (b : AffineBasis I ℝ P) (hb : IsCenteredAffineBasis b)
    (p c : D.Vertex → P)
    (hface : ∀ (C : Finset I) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hinward : IsInwardTangentColoring D b p c)
    (hsolution : ∃ C : Finset I, ∃ tau : Finset V,
      IsAffineSolution D b c 0 C tau) :
    ∃ C : Finset I, ∃ tau : Finset V, ∃ htau : tau ∈ D.complex C,
      C.Nonempty ∧ tau.card = C.card ∧
        (0 : P) ∈ convexHull ℝ
          (affineSimplexColorPoints D c C tau htau : Set P) := by
  obtain ⟨C, tau, hsol⟩ := hsolution
  exact ⟨C, tau, zero_mem_colorHull_of_affineSolution D b hb c C tau hsol
    (fun htau v hv i hi ↦
      centeredBoundary_of_inward D b hb p c hface hinward
        C tau htau v hv i hi)⟩

/-- Theorem 10.10 before extending `tau` to a top-dimensional simplex.
The face-compatibility hypothesis says precisely that a vertex of `D(C)`
lies on every reference face indexed outside `C`. -/
theorem theorem10_10_core
    (b : AffineBasis I ℝ P) (hb : IsCenteredAffineBasis b)
    (p c : D.Vertex → P)
    (hchain : D.IsChainSimplex)
    (hface : ∀ (C : Finset I) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hinward : IsInwardTangentColoring D b p c) :
    ∃ C : Finset I, ∃ tau : Finset V, ∃ htau : tau ∈ D.complex C,
      C.Nonempty ∧ tau.card = C.card ∧
        (0 : P) ∈ convexHull ℝ
          (affineSimplexColorPoints D c C tau htau : Set P) := by
  let cc : D.Vertex → I → ℝ := fun v i ↦ b.coord i (c v)
  have hcc : ∀ v, HasUnitSum (cc v) := by
    intro v
    exact b.sum_coord_apply_eq_one (c v)
  have hboundary : ∀ (C : Finset I) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C,
        0 ≤ cc v i - barycentricCenter (I := I) i :=
    centeredBoundary_of_inward D b hb p c hface hinward
  obtain ⟨C, tau, htau, hC, htauCard, hz⟩ :=
    theorem10_10_coordinate_core D cc hcc hchain hboundary
  let S : Finset P := affineSimplexColorPoints D c C tau htau
  let Q : Finset (I → ℝ) := simplexColorPoints D cc C tau htau
  have himage : S.image (coordinateMap b) = Q :=
    image_affineSimplexColorPoints_coordinateMap D b c C tau htau
  have hzeroImage : coordinateMap b 0 ∈
      convexHull ℝ (S.image (coordinateMap b) : Set (I → ℝ)) := by
    rw [coordinateMap_zero_eq_barycentricCenter b hb, himage]
    exact hz
  have hzeroPreimage : coordinateMap b 0 ∈
      coordinateMap b '' convexHull ℝ (S : Set P) := by
    rw [(coordinateMap b).image_convexHull]
    simpa only [Finset.coe_image] using hzeroImage
  obtain ⟨q, hq, hqzero⟩ := hzeroPreimage
  have hqEq : q = 0 := coordinateMap_injective b hqzero
  refine ⟨C, tau, htau, hC, htauCard, ?_⟩
  simpa [S, hqEq] using hq

omit [Fintype I] [Fintype V] [DecidableEq I] [Nonempty I] [AddCommGroup P] [Module ℝ P] in
/-- The color set is monotone when a simplex is enlarged inside the ambient
simplex-family.  The proof keeps the two vertex-membership certificates
explicit rather than identifying them definitionally. -/
theorem affineSimplexColorPoints_mono
    (c : D.Vertex → P)
    {C A : Finset I} {tau sigma : Finset V}
    (htau : tau ∈ D.complex C) (hsigma : sigma ∈ D.complex A)
    (hsub : tau ⊆ sigma) :
    affineSimplexColorPoints D c C tau htau ⊆
      affineSimplexColorPoints D c A sigma hsigma := by
  intro y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  apply Finset.mem_image.mpr
  refine ⟨⟨v.1, hsub v.2⟩, by simp, ?_⟩
  rfl

omit [Fintype V] [DecidableEq I] [Nonempty I] in
/-- Extend the lower-dimensional color-hull conclusion of Theorem 10.10 to
a top simplex.  This step depends only on ambient inclusion and purity, not
on how the core witness was obtained. -/
theorem theorem10_10_of_core
    (c : D.Vertex → P)
    (hcore : ∃ C : Finset I, ∃ tau : Finset V,
      ∃ htau : tau ∈ D.complex C,
        C.Nonempty ∧ tau.card = C.card ∧
          (0 : P) ∈ convexHull ℝ
            (affineSimplexColorPoints D c C tau htau : Set P))
    (hAmbient : ∀ (C : Finset I) (tau : Finset V),
      tau ∈ D.complex C → tau ∈ D.complex Finset.univ)
    (hPure : (D.complex Finset.univ).IsPureOfCardinality (Fintype.card I)) :
    ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
      sigma.card = Fintype.card I ∧
        (0 : P) ∈ convexHull ℝ
          (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set P) := by
  obtain ⟨C, tau, htau, _hC, _htauCard, hzero⟩ := hcore
  have htauAmbient : tau ∈ D.complex Finset.univ := hAmbient C tau htau
  obtain ⟨sigma, hsigma, hsub, hsigmaCard⟩ := hPure tau htauAmbient
  refine ⟨sigma, hsigma, hsigmaCard, ?_⟩
  exact convexHull_mono
    (by simpa using affineSimplexColorPoints_mono D c htau hsigma hsub) hzero

/-- Theorem 10.10 for a chain-simplex family whose face complexes embed in
the ambient complex and whose ambient complex is pure of cardinality `|I|`.
These two hypotheses are genuine triangulation obligations; they are not
consequences of `SimplexFamily` or `IsChainSimplex` alone. -/
theorem theorem10_10
    (b : AffineBasis I ℝ P) (hb : IsCenteredAffineBasis b)
    (p c : D.Vertex → P)
    (hchain : D.IsChainSimplex)
    (hface : ∀ (C : Finset I) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hinward : IsInwardTangentColoring D b p c)
    (hAmbient : ∀ (C : Finset I) (tau : Finset V),
      tau ∈ D.complex C → tau ∈ D.complex Finset.univ)
    (hPure : (D.complex Finset.univ).IsPureOfCardinality (Fintype.card I)) :
    ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
      sigma.card = Fintype.card I ∧
        (0 : P) ∈ convexHull ℝ
          (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set P) := by
  exact theorem10_10_of_core D c
    (theorem10_10_core D b hb p c hchain hface hinward) hAmbient hPure

end AffineVersion
end AffineColoring
end BeyondSperner
