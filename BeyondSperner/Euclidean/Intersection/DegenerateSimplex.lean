import BeyondSperner.Euclidean.AffineGeometry
import BeyondSperner.Euclidean.Intersection.GeneralPosition

/-!
# The nongeneric-simplex analysis of Lemma 10.4

This file proves both parts of Lemma 10.4.  For every nongeneric
top-dimensional simplex, its point intersection with the boundary of a
general-position edge vanishes.  The boundary intersection is split by
affine dimension.  The strict lower-dimensional branch uses Carathéodory;
the exact-codimension-one branch uses affine-dependence coefficients to
prove directly that a general-position intersection point lies in exactly
two facets.  This replaces the paper's induction inside an affine
hyperplane and avoids an implicit identification of that hyperplane with
`ℝ^(n-1)`.
-/

namespace BeyondSperner
namespace EuclideanIntersection

open Classical Filter Set
open scoped Topology
open SimplexFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Point general position with respect to every facet of `sigma`; this is
the codimension-two avoidance condition governing the parity core of Lemma
10.4. -/
def PointInGeneralPositionWithBoundary (sigma : Finset E) (p : E) : Prop :=
  ∀ v ∈ sigma, PointInGeneralPosition (sigma.erase v) p

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A proper subset of a finite set is contained in a set obtained by
erasing one element. -/
theorem exists_erase_superset_of_card_lt
    {tau sigma : Finset E} (hsub : tau ⊆ sigma)
    (hcard : tau.card < sigma.card) :
    ∃ v ∈ sigma, tau ⊆ sigma.erase v := by
  have hnsub : ¬sigma ⊆ tau := by
    intro hsigmaTau
    exact (not_le_of_gt hcard) (Finset.card_le_card hsigmaTau)
  obtain ⟨v, hvSigma, hvTau⟩ := Finset.not_subset.mp hnsub
  refine ⟨v, hvSigma, ?_⟩
  intro x hxTau
  simp only [Finset.mem_erase]
  exact ⟨fun hxv ↦ hvTau (hxv ▸ hxTau), hsub hxTau⟩

omit [FiniteDimensional ℝ E] in
/-- If the affine dimension of a finite simplex is strictly smaller than
`card - 1`, every point of its realization lies in a facet.  This is the
precise Carathéodory consequence used twice in Lemma 10.4. -/
theorem exists_mem_realization_erase_of_finrank_add_one_lt_card
    {sigma : Finset E} {x : E}
    (hdim : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) + 1 < sigma.card)
    (hx : x ∈ realization sigma) :
    ∃ v ∈ sigma, x ∈ realization (sigma.erase v) := by
  obtain ⟨tau, htauSigma, htauCard, hxTau⟩ :=
    AffineGeometry.lemma10_3
      (m := Module.finrank ℝ (vectorSpan ℝ (sigma : Set E))) rfl hx
  obtain ⟨v, hvSigma, htauErase⟩ :=
    exists_erase_superset_of_card_lt htauSigma (by simpa [htauCard] using hdim)
  exact ⟨v, hvSigma, realization_mono htauErase hxTau⟩

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- A nongeneric `n`-simplex has affine dimension at most `n - 1`. -/
theorem finrank_vectorSpan_le_pred_of_not_isGeneric
    (n : ℕ) (sigma : Finset E)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma) :
    Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) ≤ n - 1 := by
  have hcard : Fintype.card sigma = n + 1 := by
    simpa [IsMSimplex] using hsigma
  have hleRange :=
    finrank_vectorSpan_range_le ℝ ((↑) : sigma → E) hcard
  have hiff :=
    affineIndependent_iff_finrank_vectorSpan_eq ℝ ((↑) : sigma → E) hcard
  rw [Subtype.range_coe_subtype] at hleRange hiff
  have hne : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) ≠ n := by
    intro heq
    apply hng
    exact hiff.mpr heq
  exact Nat.le_sub_one_of_lt (lt_of_le_of_ne hleRange hne)

omit [FiniteDimensional ℝ E] in
/-- Every point of a nongeneric `n`-simplex lies in one of its facets. -/
theorem exists_mem_realization_facet_of_not_isGeneric
    (n : ℕ) (sigma : Finset E)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    {x : E} (hx : x ∈ realization sigma) :
    ∃ v ∈ sigma, x ∈ realization (sigma.erase v) := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hcard : sigma.card = 1 := by
      simpa [IsMSimplex] using hsigma
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hcard
    apply hng
    let : Subsingleton ↥((({z} : Finset E) : Set E)) :=
      ⟨fun a b ↦ Subtype.ext (by
        have ha : a.1 = z := by simpa using a.property
        have hb : b.1 = z := by simpa using b.property
        exact ha.trans hb.symm)⟩
    exact affineIndependent_of_subsingleton ℝ _
  apply exists_mem_realization_erase_of_finrank_add_one_lt_card
  · have hdim :=
      finrank_vectorSpan_le_pred_of_not_isGeneric n sigma hsigma hng
    have hcard : sigma.card = n + 1 := hsigma
    omega
  · exact hx

omit [FiniteDimensional ℝ E] in
/-- An endpoint in point general position cannot lie in a nongeneric
top-dimensional simplex: Carathéodory puts any such point in a facet. -/
theorem not_mem_realization_of_not_isGeneric_of_pointGeneralPosition
    (n : ℕ) (sigma : Finset E)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    {z : E} (hgp : PointInGeneralPosition sigma z) :
    z ∉ realization sigma := by
  intro hz
  obtain ⟨v, hv, hzFacet⟩ :=
    exists_mem_realization_facet_of_not_isGeneric n sigma hsigma hng hz
  exact hgp v hv hzFacet

omit [FiniteDimensional ℝ E] in
/-- The endpoint half of Lemma 10.4 holds for every nongeneric simplex,
independently of whether its affine dimension drops by one or by more. -/
theorem point_boundary_eq_zero_of_not_isGeneric
    (n : ℕ) (sigma omega : Finset E)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    (hgp : OneSimplexInGeneralPosition sigma omega) :
    pointChainIntersection (singletonChain sigma)
        (boundary (singletonChain omega)) = 0 := by
  rw [pointChainIntersection_singleton_boundary sigma omega hgp.1]
  apply Finset.sum_eq_zero
  intro z hz
  rw [pointIntersectionNumber_eq_zero_iff]
  exact not_mem_realization_of_not_isGeneric_of_pointGeneralPosition
    n sigma hsigma hng (hgp.2.1 z hz)

omit [FiniteDimensional ℝ E] in
/-- A point of an edge in general position satisfies the codimension-two
avoidance condition with respect to the simplex boundary. -/
theorem pointInGeneralPositionWithBoundary_of_mem_edge
    (sigma omega : Finset E) (p : E)
    (hgp : OneSimplexInGeneralPosition sigma omega)
    (hp : p ∈ realization omega) :
    PointInGeneralPositionWithBoundary sigma p := by
  intro v hv w hw hpSmallFace
  exact Set.disjoint_left.mp ((hgp.2.2 v hv).2.2 w hw) hp hpSmallFace

omit [FiniteDimensional ℝ E] in
/-- If a codimension-one facet contains a point which avoids all of its
facets, then that facet is affinely independent. -/
theorem isGeneric_erase_of_mem_of_pointInGeneralPositionWithBoundary
    (n : ℕ) (sigma : Finset E) (hn : 0 < n)
    (hsigma : IsMSimplex n sigma) (p v : E)
    (hgp : PointInGeneralPositionWithBoundary sigma p)
    (hv : v ∈ sigma) (hp : p ∈ realization (sigma.erase v)) :
    IsGeneric (sigma.erase v) := by
  have hfacet : IsMSimplex (n - 1) (sigma.erase v) := by
    have hcard : sigma.card = n + 1 := hsigma
    rw [IsMSimplex, Finset.card_erase_of_mem hv, hcard]
    omega
  by_contra hng
  obtain ⟨w, hw, hpSmallFace⟩ :=
    exists_mem_realization_facet_of_not_isGeneric
      (n - 1) (sigma.erase v) hfacet hng hp
  exact hgp v hv w hw hpSmallFace

omit [FiniteDimensional ℝ E] [DecidableEq E] in
/-- A nongeneric finite family admits a nonzero affine dependence, written
as a zero-sum linear combination of its literal vertices. -/
theorem exists_nonzero_affineDependence
    (sigma : Finset E) (hng : ¬IsGeneric sigma) :
    ∃ a : E → ℝ,
      (∑ i ∈ sigma, a i) = 0 ∧
      (∑ i ∈ sigma, a i • i) = 0 ∧
      ∃ i ∈ sigma, a i ≠ 0 := by
  obtain ⟨a, haLinear, haSum, i, hi, hai⟩ :=
    exists_nontrivial_relation_sum_zero_of_not_affine_ind hng
  exact ⟨a, haSum, haLinear, i, hi, hai⟩

omit [FiniteDimensional ℝ E] in
/-- A point lying in one facet and avoiding all codimension-two faces has
strictly positive barycentric weights on that facet and zero weight at the
omitted vertex.  No affine independence is assumed here; it follows
separately from the same avoidance hypothesis. -/
theorem exists_positive_facet_weights
    (sigma : Finset E) (p v : E)
    (hgp : PointInGeneralPositionWithBoundary sigma p)
    (hv : v ∈ sigma) (hp : p ∈ realization (sigma.erase v)) :
    ∃ w : E → ℝ,
      (∑ i ∈ sigma, w i) = 1 ∧
      (∑ i ∈ sigma, w i • i) = p ∧
      w v = 0 ∧
      ∀ i ∈ sigma, i ≠ v → 0 < w i := by
  rw [realization, Finset.mem_convexHull'] at hp
  obtain ⟨c, hcNonneg, hcSum, hcVector⟩ := hp
  let w : E → ℝ := fun x ↦ if x = v then 0 else c x
  have hwv : w v = 0 := by simp [w]
  have hwErase (x : E) (hx : x ∈ sigma.erase v) : w x = c x := by
    simp [w, (Finset.mem_erase.mp hx).1]
  have hwSumErase : (∑ i ∈ sigma.erase v, w i) = 1 := by
    calc
      (∑ i ∈ sigma.erase v, w i) = ∑ i ∈ sigma.erase v, c i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hwErase i hi
      _ = 1 := hcSum
  have hwVectorErase : (∑ i ∈ sigma.erase v, w i • i) = p := by
    calc
      (∑ i ∈ sigma.erase v, w i • i) =
          ∑ i ∈ sigma.erase v, c i • i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hwErase i hi]
      _ = p := hcVector
  have hwSum : (∑ i ∈ sigma, w i) = 1 := by
    rw [← Finset.sum_erase sigma hwv]
    exact hwSumErase
  have hwVector : (∑ i ∈ sigma, w i • i) = p := by
    have hwvVector : w v • v = 0 := by simp [hwv]
    rw [← Finset.sum_erase (f := fun x ↦ w x • x) sigma hwvVector]
    exact hwVectorErase
  refine ⟨w, hwSum, hwVector, hwv, ?_⟩
  intro i hi hiv
  have hiErase : i ∈ sigma.erase v := Finset.mem_erase.mpr ⟨hiv, hi⟩
  have hwiNonneg : 0 ≤ w i := by
    rw [hwErase i hiErase]
    exact hcNonneg i hiErase
  exact lt_of_le_of_ne hwiNonneg fun hwi ↦ by
    have hwiZero : w i = 0 := hwi.symm
    have hwSumSmall :
        (∑ x ∈ (sigma.erase v).erase i, w x) = 1 := by
      rw [Finset.sum_erase _ hwiZero]
      exact hwSumErase
    have hwiVector : w i • i = 0 := by simp [hwiZero]
    have hwVectorSmall :
        (∑ x ∈ (sigma.erase v).erase i, w x • x) = p := by
      rw [Finset.sum_erase (f := fun x ↦ w x • x) _ hwiVector]
      exact hwVectorErase
    apply hgp v hv i hiErase
    rw [realization, Finset.mem_convexHull']
    refine ⟨w, ?_, hwSumSmall, hwVectorSmall⟩
    intro x hx
    rw [hwErase x (Finset.erase_subset i _ hx)]
    exact hcNonneg x (Finset.erase_subset i _ hx)

omit [FiniteDimensional ℝ E] in
/-- A point in the affine span of a finite set has normalized affine
weights indexed by the literal vertices of that set. -/
theorem exists_subtype_affine_weights_of_mem_affineSpan
    (tau : Finset E) (x : E)
    (hx : x ∈ affineSpan ℝ (tau : Set E)) :
    ∃ w : tau → ℝ,
      (∑ i, w i) = 1 ∧ (∑ i, w i • (i.1 : E)) = x := by
  have hxRange : x ∈ affineSpan ℝ
      (Set.range ((↑) : tau → E)) := by
    rw [Subtype.range_coe_subtype]
    exact hx
  rw [mem_affineSpan_iff_eq_affineCombination ℝ E] at hxRange
  obtain ⟨s, c, hcSum, hxCombination⟩ := hxRange
  let w : tau → ℝ := fun i ↦ if i ∈ s then c i else 0
  have hsAttach : s ⊆ tau.attach := by
    intro i hi
    exact Finset.mem_attach tau i
  have hwSum : (∑ i, w i) = 1 := by
    simpa [w, Finset.inter_eq_right.mpr hsAttach] using hcSum
  have hxLinear : (∑ i ∈ s, c i • (i.1 : E)) = x := by
    rw [Finset.affineCombination_eq_linear_combination s _ c hcSum] at hxCombination
    exact hxCombination.symm
  have hwVector : (∑ i, w i • (i.1 : E)) = x := by
    simpa [w, Finset.inter_eq_right.mpr hsAttach] using hxLinear
  exact ⟨w, hwSum, hwVector⟩

omit [FiniteDimensional ℝ E] in
/-- A point of a simplex which avoids every facet has a representation with
all vertex weights strictly positive. -/
theorem exists_positive_subtype_weights_of_pointGeneralPosition
    (tau : Finset E) (x : E)
    (hgp : PointInGeneralPosition tau x)
    (hx : x ∈ realization tau) :
    ∃ w : tau → ℝ,
      (∑ i, w i) = 1 ∧
      (∑ i, w i • (i.1 : E)) = x ∧
      ∀ i, 0 < w i := by
  rw [realization, Finset.mem_convexHull'] at hx
  obtain ⟨c, hcNonneg, hcSum, hcVector⟩ := hx
  let w : tau → ℝ := fun i ↦ c i.1
  have hwSum : (∑ i, w i) = 1 := by
    rw [← Finset.sum_attach] at hcSum
    simpa [w] using hcSum
  have hwVector : (∑ i, w i • (i.1 : E)) = x := by
    rw [← Finset.sum_attach] at hcVector
    simpa [w] using hcVector
  refine ⟨w, hwSum, hwVector, ?_⟩
  intro i
  have hwiNonneg : 0 ≤ w i := hcNonneg i.1 i.2
  exact lt_of_le_of_ne hwiNonneg fun hwi ↦ by
    have hci : c i.1 = 0 := by simpa [w] using hwi.symm
    have hcSumErase : (∑ y ∈ tau.erase i.1, c y) = 1 := by
      rw [Finset.sum_erase tau hci]
      exact hcSum
    have hciVector : c i.1 • i.1 = 0 := by simp [hci]
    have hcVectorErase : (∑ y ∈ tau.erase i.1, c y • y) = x := by
      rw [Finset.sum_erase (f := fun y ↦ c y • y) tau hciVector]
      exact hcVector
    apply hgp i.1 i.2
    rw [realization, Finset.mem_convexHull']
    exact ⟨c, fun y hy ↦ hcNonneg y (Finset.erase_subset i.1 tau hy),
      hcSumErase, hcVectorErase⟩

omit [FiniteDimensional ℝ E] in
/-- In a nonzero affine dependence, the coefficient at `v` cannot vanish
when the complementary facet is affinely independent. -/
theorem affineDependence_coeff_ne_zero_of_isGeneric_erase
    (sigma : Finset E) (v : E) (_hv : v ∈ sigma)
    (a : E → ℝ)
    (haSum : (∑ i ∈ sigma, a i) = 0)
    (haVector : (∑ i ∈ sigma, a i • i) = 0)
    (haNonzero : ∃ i ∈ sigma, a i ≠ 0)
    (hfacet : IsGeneric (sigma.erase v)) :
    a v ≠ 0 := by
  intro hav
  have haSumErase : (∑ i ∈ sigma.erase v, a i) = 0 := by
    rw [Finset.sum_erase sigma hav]
    exact haSum
  have havVector : a v • v = 0 := by simp [hav]
  have haVectorErase : (∑ i ∈ sigma.erase v, a i • i) = 0 := by
    rw [Finset.sum_erase (f := fun x ↦ a x • x) sigma havVector]
    exact haVector
  have haZero := hfacet.eq_zero_of_sum_eq_zero_subtype haSumErase haVectorErase
  obtain ⟨i, hi, hai⟩ := haNonzero
  by_cases hiv : i = v
  · exact hai (hiv ▸ hav)
  · exact hai (haZero i (Finset.mem_erase.mpr ⟨hiv, hi⟩))

omit [FiniteDimensional ℝ E] in
/-- Orient a nonzero affine dependence so that its coefficient at the
omitted vertex is strictly positive. -/
theorem exists_affineDependence_pos_at
    (sigma : Finset E) (v : E) (hv : v ∈ sigma)
    (hng : ¬IsGeneric sigma) (hfacet : IsGeneric (sigma.erase v)) :
    ∃ a : E → ℝ,
      (∑ i ∈ sigma, a i) = 0 ∧
      (∑ i ∈ sigma, a i • i) = 0 ∧
      0 < a v := by
  obtain ⟨a, haSum, haVector, haNonzero⟩ :=
    exists_nonzero_affineDependence sigma hng
  have havNe := affineDependence_coeff_ne_zero_of_isGeneric_erase
    sigma v hv a haSum haVector haNonzero hfacet
  by_cases hav : 0 < a v
  · exact ⟨a, haSum, haVector, hav⟩
  · refine ⟨fun x ↦ -a x, ?_, ?_, ?_⟩
    · rw [Finset.sum_neg_distrib, haSum, neg_zero]
    · simp only [neg_smul, Finset.sum_neg_distrib]
      exact neg_eq_zero.mpr haVector
    · exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hav) havNe)

omit [FiniteDimensional ℝ E] in
/-- Once the facet opposite `v` is affinely independent, every affine
dependence of the full vertex set is a scalar multiple of one dependence
whose `v` coefficient is nonzero.  Equivalently, every two normalized
affine representations differ along this one direction. -/
theorem affine_weights_eq_add_smul_dependence
    (sigma : Finset E) (v : E)
    (a w q : E → ℝ)
    (haSum : (∑ i ∈ sigma, a i) = 0)
    (haVector : (∑ i ∈ sigma, a i • i) = 0)
    (hav : a v ≠ 0)
    (hwSum : (∑ i ∈ sigma, w i) = 1)
    (hwVector : (∑ i ∈ sigma, w i • i) =
      ∑ i ∈ sigma, q i • i)
    (hqSum : (∑ i ∈ sigma, q i) = 1)
    (hfacet : IsGeneric (sigma.erase v)) :
    ∃ s : ℝ, ∀ i ∈ sigma, q i = w i + s * a i := by
  let s : ℝ := (q v - w v) / a v
  let d : E → ℝ := fun i ↦ q i - w i - s * a i
  have hdv : d v = 0 := by
    dsimp [d, s]
    field_simp [hav]
    ring
  have hdSum : (∑ i ∈ sigma, d i) = 0 := by
    simp only [d, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, haSum, mul_zero, sub_zero, hqSum, hwSum, sub_self]
  have hdVector : (∑ i ∈ sigma, d i • i) = 0 := by
    simp only [d, sub_smul, mul_smul, Finset.sum_sub_distrib]
    rw [← Finset.smul_sum, haVector, smul_zero, sub_zero, hwVector, sub_self]
  have hdSumErase : (∑ i ∈ sigma.erase v, d i) = 0 := by
    rw [Finset.sum_erase sigma hdv]
    exact hdSum
  have hdvVector : d v • v = 0 := by simp [hdv]
  have hdVectorErase : (∑ i ∈ sigma.erase v, d i • i) = 0 := by
    rw [Finset.sum_erase (f := fun x ↦ d x • x) sigma hdvVector]
    exact hdVector
  have hdZero := hfacet.eq_zero_of_sum_eq_zero_subtype hdSumErase hdVectorErase
  refine ⟨s, ?_⟩
  intro i hi
  have hdi : d i = 0 := by
    by_cases hiv : i = v
    · simpa [hiv] using hdv
    · exact hdZero i (Finset.mem_erase.mpr ⟨hiv, hi⟩)
  dsimp [d] at hdi
  linarith

omit [FiniteDimensional ℝ E] in
/-- Starting at a strictly positive representation on one facet, moving
along the unique affine-dependence direction reaches a second, distinct
facet while preserving nonnegative weights. -/
theorem exists_second_facet_of_affineDependence
    (sigma : Finset E) (p v : E) (hv : v ∈ sigma)
    (a w : E → ℝ)
    (haSum : (∑ i ∈ sigma, a i) = 0)
    (haVector : (∑ i ∈ sigma, a i • i) = 0)
    (havPos : 0 < a v)
    (hwSum : (∑ i ∈ sigma, w i) = 1)
    (hwVector : (∑ i ∈ sigma, w i • i) = p)
    (hwv : w v = 0)
    (hwPos : ∀ i ∈ sigma, i ≠ v → 0 < w i)
    (hgp : PointInGeneralPositionWithBoundary sigma p)
    (hfacet : IsGeneric (sigma.erase v)) :
    ∃ u ∈ sigma, u ≠ v ∧ p ∈ realization (sigma.erase u) ∧
      ∀ r ∈ sigma, p ∈ realization (sigma.erase r) → r = v ∨ r = u := by
  let negative : Finset E := sigma.filter fun i ↦ a i < 0
  have hnegative : negative.Nonempty := by
    by_contra hempty
    have haNonneg : ∀ i ∈ sigma, 0 ≤ a i := by
      intro i hi
      exact le_of_not_gt fun hai ↦ hempty ⟨i, by simp [negative, hi, hai]⟩
    have hsumPos : 0 < ∑ i ∈ sigma, a i :=
      Finset.sum_pos' haNonneg ⟨v, hv, havPos⟩
    linarith
  obtain ⟨u, huNegative, huMin⟩ :=
    Finset.exists_min_image negative (fun i ↦ w i / (-a i)) hnegative
  have huSigma : u ∈ sigma := (Finset.mem_filter.mp huNegative).1
  have hauNeg : a u < 0 := (Finset.mem_filter.mp huNegative).2
  have huv : u ≠ v := by
    intro huv
    subst u
    linarith
  have hwuPos : 0 < w u := hwPos u huSigma huv
  let t : ℝ := w u / (-a u)
  have htPos : 0 < t := div_pos hwuPos (neg_pos.mpr hauNeg)
  let w' : E → ℝ := fun i ↦ w i + t * a i
  have hw'Nonneg : ∀ i ∈ sigma, 0 ≤ w' i := by
    intro i hi
    by_cases hai : a i < 0
    · have hiNegative : i ∈ negative := Finset.mem_filter.mpr ⟨hi, hai⟩
      have hratio := huMin i hiNegative
      have hdenomPos : 0 < -a i := neg_pos.mpr hai
      have hbound : t * (-a i) ≤ w i := by
        change (w u / -a u) * (-a i) ≤ w i
        exact (le_div_iff₀ hdenomPos).mp hratio
      change 0 ≤ w i + t * a i
      linarith
    · have haiNonneg : 0 ≤ a i := le_of_not_gt hai
      have hwiNonneg : 0 ≤ w i := by
        by_cases hiv : i = v
        · simp [hiv, hwv]
        · exact (hwPos i hi hiv).le
      exact add_nonneg hwiNonneg (mul_nonneg htPos.le haiNonneg)
  have hw'u : w' u = 0 := by
    have hauNe : a u ≠ 0 := ne_of_lt hauNeg
    dsimp [w', t]
    field_simp [hauNe]
    ring
  have hw'Sum : (∑ i ∈ sigma, w' i) = 1 := by
    simp only [w', Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    rw [haSum, mul_zero, add_zero, hwSum]
  have hw'Vector : (∑ i ∈ sigma, w' i • i) = p := by
    simp only [w', add_smul, mul_smul, Finset.sum_add_distrib]
    rw [← Finset.smul_sum]
    rw [haVector, smul_zero, add_zero, hwVector]
  have hpFacetU : p ∈ realization (sigma.erase u) := by
    rw [realization, Finset.mem_convexHull']
    have hw'SumErase : (∑ i ∈ sigma.erase u, w' i) = 1 := by
      rw [Finset.sum_erase sigma hw'u]
      exact hw'Sum
    have hw'uVector : w' u • u = 0 := by simp [hw'u]
    have hw'VectorErase : (∑ i ∈ sigma.erase u, w' i • i) = p := by
      rw [Finset.sum_erase (f := fun x ↦ w' x • x) sigma hw'uVector]
      exact hw'Vector
    exact ⟨w', fun i hi ↦ hw'Nonneg i (Finset.erase_subset u sigma hi),
      hw'SumErase, hw'VectorErase⟩
  refine ⟨u, huSigma, huv, hpFacetU, ?_⟩
  intro r hrSigma hpFacetR
  by_cases hrv : r = v
  · exact Or.inl hrv
  right
  obtain ⟨q, hqSum, hqVector, hqr, hqPos⟩ :=
    exists_positive_facet_weights sigma p r hgp hrSigma hpFacetR
  have havNe : a v ≠ 0 := ne_of_gt havPos
  obtain ⟨s, hqFormula⟩ := affine_weights_eq_add_smul_dependence
    sigma v a w q haSum haVector havNe hwSum
      (by rw [hwVector, hqVector]) hqSum hfacet
  have hqvPos : 0 < q v := hqPos v hv (Ne.symm hrv)
  have hsPos : 0 < s := by
    have hformulaV := hqFormula v hv
    rw [hwv] at hformulaV
    nlinarith
  have harNeg : a r < 0 := by
    by_contra har
    have harNonneg : 0 ≤ a r := le_of_not_gt har
    have hwrPos : 0 < w r := hwPos r hrSigma hrv
    have hformulaR := hqFormula r hrSigma
    rw [hqr] at hformulaR
    nlinarith
  have hrNegative : r ∈ negative := Finset.mem_filter.mpr ⟨hrSigma, harNeg⟩
  have htLeS : t ≤ s := by
    have hmin := huMin r hrNegative
    have hformulaR := hqFormula r hrSigma
    rw [hqr] at hformulaR
    have harNe : a r ≠ 0 := ne_of_lt harNeg
    have hsRatio : s = w r / (-a r) := by
      field_simp [harNe] at hformulaR ⊢
      nlinarith
    simpa [t, hsRatio] using hmin
  have hsLeT : s ≤ t := by
    have hquNonneg : 0 ≤ q u := by
      by_cases hur : u = r
      · simp [hur, hqr]
      · exact (hqPos u huSigma hur).le
    have hformulaU := hqFormula u huSigma
    have hauNe : a u ≠ 0 := ne_of_lt hauNeg
    have hbound : s ≤ w u / (-a u) := by
      rw [hformulaU] at hquNonneg
      apply (le_div_iff₀ (neg_pos.mpr hauNeg)).mpr
      nlinarith
    simpa [t] using hbound
  have hst : s = t := le_antisymm hsLeT htLeS
  have hquZero : q u = 0 := by
    rw [hqFormula u huSigma, hst]
    exact hw'u
  by_contra hur
  exact (ne_of_gt (hqPos u huSigma (Ne.symm hur))) hquZero

omit [FiniteDimensional ℝ E] in
/-- A point of a nongeneric `n`-simplex which avoids every codimension-two
face lies in exactly two of its facets.  This is the coefficient-interval
parity statement replacing the paper's induction inside the affine
hyperplane. -/
theorem exists_exactly_two_facets_of_not_isGeneric
    (n : ℕ) (sigma : Finset E) (p : E) (hn : 0 < n)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    (hgp : PointInGeneralPositionWithBoundary sigma p)
    (hp : p ∈ realization sigma) :
    ∃ v ∈ sigma, ∃ u ∈ sigma, u ≠ v ∧
      ∀ r ∈ sigma,
        p ∈ realization (sigma.erase r) ↔ r = v ∨ r = u := by
  obtain ⟨v, hv, hpFacetV⟩ :=
    exists_mem_realization_facet_of_not_isGeneric n sigma hsigma hng hp
  have hfacetV :=
    isGeneric_erase_of_mem_of_pointInGeneralPositionWithBoundary
      n sigma hn hsigma p v hgp hv hpFacetV
  obtain ⟨w, hwSum, hwVector, hwv, hwPos⟩ :=
    exists_positive_facet_weights sigma p v hgp hv hpFacetV
  obtain ⟨a, haSum, haVector, havPos⟩ :=
    exists_affineDependence_pos_at sigma v hv hng hfacetV
  obtain ⟨u, hu, huv, hpFacetU, honly⟩ :=
    exists_second_facet_of_affineDependence sigma p v hv a w
      haSum haVector havPos hwSum hwVector hwv hwPos hgp hfacetV
  refine ⟨v, hv, u, hu, huv, ?_⟩
  intro r hr
  constructor
  · exact honly r hr
  · rintro (rfl | rfl)
    · exact hpFacetV
    · exact hpFacetU

omit [FiniteDimensional ℝ E] in
/-- The number modulo two of facets containing a codimension-two-general
point of a nongeneric simplex is zero. -/
theorem facet_point_parity_of_not_isGeneric
    (n : ℕ) (sigma : Finset E) (p : E) (hn : 0 < n)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    (hgp : PointInGeneralPositionWithBoundary sigma p) :
    (∑ v ∈ sigma, pointIntersectionNumber (sigma.erase v) p) = 0 := by
  by_cases hp : p ∈ realization sigma
  · obtain ⟨v, hv, u, hu, huv, hiff⟩ :=
      exists_exactly_two_facets_of_not_isGeneric
        n sigma p hn hsigma hng hgp hp
    calc
      (∑ r ∈ sigma, pointIntersectionNumber (sigma.erase r) p) =
          ∑ r ∈ sigma, if r = v ∨ r = u then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [pointIntersectionNumber]
        simp only [hiff r hr]
      _ = 0 := sum_two_distinct_indicators_zmod2 sigma v u hv hu (Ne.symm huv)
  · apply Finset.sum_eq_zero
    intro v hv
    rw [pointIntersectionNumber_eq_zero_iff]
    intro hpFacet
    exact hp (realization_erase_subset sigma v hpFacet)

/-- If the affine dimension drops by at least two, a general-position edge
is disjoint from every facet of the simplex. -/
theorem disjoint_realization_facet_of_finrank_add_two_le
    (n : ℕ) (sigma omega : Finset E)
    (hsigma : IsMSimplex n sigma)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) + 2 ≤ n)
    (hgp : OneSimplexInGeneralPosition sigma omega) :
    ∀ v ∈ sigma, Disjoint (realization omega) (realization (sigma.erase v)) := by
  intro v hv
  apply Set.disjoint_left.mpr
  intro x hxOmega hxFacet
  let rho := sigma.erase v
  have hrhoCard : rho.card = n := by
    have hcard : sigma.card = n + 1 := hsigma
    change (sigma.erase v).card = n
    rw [Finset.card_erase_of_mem hv, hcard]
    omega
  have hrhoSubset : (rho : Set E) ⊆ (sigma : Set E) := by
    exact_mod_cast Finset.erase_subset v sigma
  have hspanMono :
      vectorSpan ℝ (rho : Set E) ≤ vectorSpan ℝ (sigma : Set E) :=
    vectorSpan_mono ℝ hrhoSubset
  have hdimRho :
      Module.finrank ℝ (vectorSpan ℝ (rho : Set E)) + 1 < rho.card := by
    have hfinrankMono := Submodule.finrank_mono hspanMono
    omega
  obtain ⟨w, hwRho, hxSmallFace⟩ :=
    exists_mem_realization_erase_of_finrank_add_one_lt_card hdimRho hxFacet
  have hfaceGP := hgp.2.2 v hv
  exact Set.disjoint_left.mp (hfaceGP.2.2 w hwRho) hxOmega hxSmallFace

/-- The boundary half of Lemma 10.4 in the strict lower-dimensional case. -/
theorem boundary_point_eq_zero_of_finrank_add_two_le
    (n : ℕ) (sigma omega : Finset E)
    (hsigma : IsMSimplex n sigma)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) + 2 ≤ n)
    (hgp : OneSimplexInGeneralPosition sigma omega) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) = 0 := by
  rw [oneChainIntersection_boundary_singleton]
  apply Finset.sum_eq_zero
  intro v hv
  rw [faceOneSimplexIntersectionNumber_eq_zero_iff]
  rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty]
  exact (disjoint_realization_facet_of_finrank_add_two_le
    n sigma omega hsigma hdim hgp v hv).symm

omit [FiniteDimensional ℝ E] in
/-- Point intersection of the abstract boundary with a literal point,
expanded as the sum of facet-membership indicators. -/
theorem pointChainIntersection_boundary_singleton_point
    (sigma : Finset E) (p : E) :
    pointChainIntersection (boundary (singletonChain sigma))
        (singletonChain {p}) =
      ∑ v ∈ sigma, pointIntersectionNumber (sigma.erase v) p := by
  rw [boundary_singletonChain, boundarySimplex, pointChainIntersection,
    chainPairing_finsetSum_left]
  simp

omit [FiniteDimensional ℝ E] in
/-- Point intersection of the boundary at a codimension-two-general point
vanishes for every nongeneric simplex. -/
theorem boundary_pointIntersection_eq_zero_of_not_isGeneric
    (n : ℕ) (sigma : Finset E) (p : E) (hn : 0 < n)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    (hgp : PointInGeneralPositionWithBoundary sigma p) :
    pointChainIntersection (boundary (singletonChain sigma))
        (singletonChain {p}) = 0 := by
  rw [pointChainIntersection_boundary_singleton_point]
  exact facet_point_parity_of_not_isGeneric n sigma p hn hsigma hng hgp

omit [FiniteDimensional ℝ E] in
/-- A general-position edge contained in the affine span of a generic
simplex is disjoint from that simplex.  The scalar-parameter proof is
relative-dimensional: it uses normalized affine weights in the affine span,
so it does not incorrectly appeal to ambient interior. -/
theorem disjoint_realization_of_generic_of_edge_subset_affineSpan
    (tau omega : Finset E)
    (_hgeneric : IsGeneric tau)
    (hgp : OneSimplexInGeneralPositionWithFace tau omega)
    (hcontained : realization omega ⊆
      (affineSpan ℝ (tau : Set E) : Set E)) :
    Disjoint (realization omega) (realization tau) := by
  have homegaCard : omega.card = 2 := by
    simpa [IsMSimplex] using hgp.1
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp homegaCard
  apply Set.disjoint_left.mpr
  intro q hqOmega hqTau
  let K := segmentParameters tau x y
  have hqSegment : q ∈ segment ℝ x y := by
    simpa [realization_pair] using hqOmega
  rw [segment_eq_image_lineMap] at hqSegment
  obtain ⟨r₀, hr₀Icc, hr₀q⟩ := hqSegment
  have hKNonempty : K.Nonempty := by
    refine ⟨r₀, hr₀Icc, ?_⟩
    simpa [hr₀q] using hqTau
  let a := sInf K
  let b := sSup K
  have hK : K = Set.Icc a b :=
    segmentParameters_eq_Icc_of_nonempty tau x y hKNonempty
  have hr₀K : r₀ ∈ K := by
    exact ⟨hr₀Icc, by simpa [hr₀q] using hqTau⟩
  have hr₀ab : r₀ ∈ Set.Icc a b := hK ▸ hr₀K
  have hab : a ≤ b := hr₀ab.1.trans hr₀ab.2
  have haK : a ∈ K := by
    rw [hK]
    exact ⟨le_rfl, hab⟩
  have hzeroNotK : 0 ∉ K := by
    rw [zero_mem_segmentParameters_iff]
    exact hgp.2.1 x (by simp)
  have honeNotK : 1 ∉ K := by
    rw [one_mem_segmentParameters_iff]
    exact hgp.2.1 y (by simp)
  have haPos : 0 < a := by
    exact lt_of_le_of_ne haK.1.1 fun ha0 ↦ hzeroNotK (ha0 ▸ haK)
  have haLtOne : a < 1 := by
    exact lt_of_le_of_ne haK.1.2 fun ha1 ↦ honeNotK (ha1 ▸ haK)
  let q₀ := AffineMap.lineMap x y a
  have hq₀Tau : q₀ ∈ realization tau := haK.2
  have hq₀Omega : q₀ ∈ realization ({x, y} : Finset E) := by
    rw [realization_pair, segment_eq_image_lineMap]
    exact ⟨a, haK.1, rfl⟩
  have hq₀GP : PointInGeneralPosition tau q₀ := by
    intro i hi hq₀Face
    exact Set.disjoint_left.mp (hgp.2.2 i hi) hq₀Omega hq₀Face
  obtain ⟨w, hwSum, hwVector, hwPos⟩ :=
    exists_positive_subtype_weights_of_pointGeneralPosition tau q₀ hq₀GP hq₀Tau
  have hxOmega : x ∈ realization ({x, y} : Finset E) := by
    apply subset_convexHull ℝ
    simp
  have hxSpan : x ∈ affineSpan ℝ (tau : Set E) := hcontained hxOmega
  obtain ⟨c, hcSum, hcVector⟩ :=
    exists_subtype_affine_weights_of_mem_affineSpan tau x hxSpan
  let coeff : ℝ → tau → ℝ := fun r i ↦
    (1 - r / a) * c i + (r / a) * w i
  have hcoeffContinuous (i : tau) : Continuous (fun r ↦ coeff r i) := by
    dsimp [coeff]
    fun_prop
  let U : Set ℝ := {r | ∀ i : tau, 0 < coeff r i}
  have hUOpen : IsOpen U := by
    rw [show U = ⋂ i : tau, (fun r ↦ coeff r i) ⁻¹' Set.Ioi 0 by
      ext r
      simp [U]]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_Ioi.preimage (hcoeffContinuous i)
  have haU : a ∈ U := by
    intro i
    simpa [coeff, haPos.ne'] using hwPos i
  have haIoo : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨haPos, haLtOne⟩
  have hN : U ∩ Set.Ioo (0 : ℝ) 1 ∈ 𝓝 a :=
    inter_mem (hUOpen.mem_nhds haU) (isOpen_Ioo.mem_nhds haIoo)
  obtain ⟨r, ⟨hrU, hrIoo⟩, hra⟩ :=
    nonempty_nhds_inter_Iio hN (by simp)
  have hcoeffSum : (∑ i, coeff r i) = 1 := by
    simp only [coeff, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcSum, hwSum]
    field_simp [haPos.ne']
    ring
  have hcoeffVector :
      (∑ i, coeff r i • (i.1 : E)) = AffineMap.lineMap x y r := by
    simp only [coeff, add_smul, mul_smul, Finset.sum_add_distrib,
      ← Finset.smul_sum, hcVector, hwVector, q₀]
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]
    have hxCoeff : (1 - r / a) + (r / a) * (1 - a) = 1 - r := by
      field_simp [haPos.ne']
      ring
    have hyCoeff : (r / a) * a = r := by
      field_simp [haPos.ne']
    rw [hxCoeff, hyCoeff]
  have hrTau : AffineMap.lineMap x y r ∈ realization tau := by
    rw [realization]
    apply mem_convexHull_of_exists_fintype (coeff r) ((↑) : tau → E)
    · exact fun i ↦ (hrU i).le
    · exact hcoeffSum
    · exact fun i ↦ by simp
    · exact hcoeffVector
  have hrK : r ∈ K := ⟨⟨hrIoo.1.le, hrIoo.2.le⟩, hrTau⟩
  have har : a ≤ r := by
    have : r ∈ Set.Icc a b := hK ▸ hrK
    exact this.1
  exact (not_le_of_gt hra) har

omit [FiniteDimensional ℝ E] in
/-- Two distinct points of a nondegenerate segment lying in an affine
subspace force the whole segment into that affine subspace. -/
theorem realization_pair_subset_affineSubspace_of_two_points
    (x y p q : E) (_hxy : x ≠ y)
    (H : AffineSubspace ℝ E)
    (hpSegment : p ∈ realization ({x, y} : Finset E))
    (hqSegment : q ∈ realization ({x, y} : Finset E))
    (hpH : p ∈ H) (hqH : q ∈ H) (hpq : p ≠ q) :
    realization ({x, y} : Finset E) ⊆ (H : Set E) := by
  rw [realization_pair, segment_eq_image_lineMap] at hpSegment hqSegment ⊢
  obtain ⟨r, hr, hrp⟩ := hpSegment
  obtain ⟨s, hs, hsq⟩ := hqSegment
  have hrs : r ≠ s := by
    intro hrs
    apply hpq
    rw [← hrp, ← hsq, hrs]
  have hscaled : (s - r) • (y - x) ∈ H.direction := by
    have hvsub := AffineSubspace.vsub_mem_direction hqH hpH
    have heq : q - p = (s - r) • (y - x) := by
      rw [← hrp, ← hsq, AffineMap.lineMap_apply_module,
        AffineMap.lineMap_apply_module]
      module
    rw [vsub_eq_sub, heq] at hvsub
    exact hvsub
  have hdirection : y - x ∈ H.direction := by
    have hinv := H.direction.smul_mem (s - r)⁻¹ hscaled
    simpa [smul_smul, sub_ne_zero.mpr (Ne.symm hrs)] using hinv
  have hxH : x ∈ H := by
    have hmove := AffineSubspace.vadd_mem_of_mem_direction
      (H.direction.smul_mem (-r) hdirection) hpH
    have heq : (-r) • (y - x) + p = x := by
      rw [← hrp, AffineMap.lineMap_apply_module]
      module
    simpa only [vadd_eq_add, heq] using hmove
  have hyH : y ∈ H := by
    have hmove := AffineSubspace.vadd_mem_of_mem_direction hdirection hxH
    simpa using hmove
  rintro z ⟨t, ht, rfl⟩
  exact AffineMap.lineMap_mem t hxH hyH

omit [FiniteDimensional ℝ E] in
/-- Unless the entire edge lies in an affine subspace, its intersection
with that subspace has at most one point. -/
theorem segment_inter_affineSubspace_subsingleton_of_not_subset
    (omega : Finset E) (H : AffineSubspace ℝ E)
    (homega : IsMSimplex 1 omega)
    (hnotContained : ¬realization omega ⊆ (H : Set E)) :
    (realization omega ∩ (H : Set E)).Subsingleton := by
  have hcard : omega.card = 2 := by simpa [IsMSimplex] using homega
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  intro p hp q hq
  by_contra hpq
  apply hnotContained
  exact realization_pair_subset_affineSubspace_of_two_points
    x y p q hxy H hp.1 hq.1 hp.2 hq.2 hpq

omit [FiniteDimensional ℝ E] in
/-- If a generic facet of full relative dimension lies in the affine span
of `sigma`, then it spans that same affine subspace. -/
theorem affineSpan_erase_eq_of_finrank_vectorSpan_eq_pred
    (n : ℕ) (sigma : Finset E) (v : E) (hn : 0 < n)
    (hsigma : IsMSimplex n sigma) (hv : v ∈ sigma)
    (hfacet : IsGeneric (sigma.erase v))
    (hdim : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) = n - 1) :
    affineSpan ℝ (sigma.erase v : Set E) = affineSpan ℝ (sigma : Set E) := by
  let H := affineSpan ℝ (sigma : Set E)
  let : FiniteDimensional ℝ H.direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ sigma.finite_toSet
  have hrange : Set.range ((↑) : {x // x ∈ sigma.erase v} → E) =
      (sigma.erase v : Set E) := Subtype.range_coe_subtype
  rw [← hrange]
  change affineSpan ℝ (Set.range ((↑) : {x // x ∈ sigma.erase v} → E)) = H
  apply hfacet.affineSpan_eq_of_le_of_card_eq_finrank_add_one
  · rw [Subtype.range_coe_subtype]
    exact affineSpan_mono ℝ (by exact_mod_cast Finset.erase_subset v sigma)
  · have hcard : (sigma.erase v).card = n := by
      have hsigmaCard : sigma.card = n + 1 := hsigma
      rw [Finset.card_erase_of_mem hv, hsigmaCard]
      omega
    change Fintype.card ↥((sigma.erase v : Finset E) : Set E) =
      Module.finrank ℝ (affineSpan ℝ (sigma : Set E)).direction + 1
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Set.ncard_coe_finset, hcard, direction_affineSpan, hdim]
    omega

omit [FiniteDimensional ℝ E] in
/-- The last case of the paper's Lemma 10.4: if the edge lies in the
codimension-one affine span of the nongeneric simplex, it misses every
facet, hence its boundary intersection is zero. -/
theorem boundary_point_eq_zero_of_edge_subset_affineSpan
    (n : ℕ) (sigma omega : Finset E) (hn : 0 < n)
    (hsigma : IsMSimplex n sigma)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) = n - 1)
    (hgp : OneSimplexInGeneralPosition sigma omega)
    (hcontained : realization omega ⊆
      (affineSpan ℝ (sigma : Set E) : Set E)) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) = 0 := by
  rw [oneChainIntersection_boundary_singleton]
  apply Finset.sum_eq_zero
  intro v hv
  rw [faceOneSimplexIntersectionNumber_eq_zero_iff]
  rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty]
  apply Disjoint.symm
  by_contra hnotDisjoint
  rw [Set.not_disjoint_iff_nonempty_inter] at hnotDisjoint
  obtain ⟨p, hpOmega, hpFacet⟩ := hnotDisjoint
  have hpBoundaryGP :=
    pointInGeneralPositionWithBoundary_of_mem_edge sigma omega p hgp hpOmega
  have hfacet := isGeneric_erase_of_mem_of_pointInGeneralPositionWithBoundary
    n sigma hn hsigma p v hpBoundaryGP hv hpFacet
  have hspanEq := affineSpan_erase_eq_of_finrank_vectorSpan_eq_pred
    n sigma v hn hsigma hv hfacet hdim
  have hcontainedFacet : realization omega ⊆
      (affineSpan ℝ (sigma.erase v : Set E) : Set E) := by
    rw [hspanEq]
    exact hcontained
  have hdis := disjoint_realization_of_generic_of_edge_subset_affineSpan
    (sigma.erase v) omega hfacet (hgp.2.2 v hv) hcontainedFacet
  exact Set.disjoint_left.mp hdis hpOmega hpFacet

omit [FiniteDimensional ℝ E] in
/-- If every meeting of the edge with the affine hull of `sigma` is already
an endpoint of the edge, general position excludes every facet intersection.
This covers both the disjoint-hyperplane and endpoint-only cases in the
paper's codimension-one analysis. -/
theorem boundary_point_eq_zero_of_affineSpan_inter_subset_vertices
    (sigma omega : Finset E)
    (hinter : realization omega ∩
        (affineSpan ℝ (sigma : Set E) : Set E) ⊆ (omega : Set E))
    (hgp : OneSimplexInGeneralPosition sigma omega) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) = 0 := by
  rw [oneChainIntersection_boundary_singleton]
  apply Finset.sum_eq_zero
  intro v hv
  rw [faceOneSimplexIntersectionNumber_eq_zero_iff]
  intro hnonempty
  obtain ⟨x, hxFacet, hxOmega⟩ := hnonempty
  have hfacetSpan :
      realization (sigma.erase v) ⊆
        (affineSpan ℝ (sigma : Set E) : Set E) := by
    intro y hy
    apply (affineSpan_mono ℝ (by exact_mod_cast Finset.erase_subset v sigma))
    exact convexHull_subset_affineSpan (sigma.erase v : Set E) hy
  have hxVertex : x ∈ omega := hinter ⟨hxOmega, hfacetSpan hxFacet⟩
  exact hgp.2.1 x hxVertex v hv hxFacet

omit [FiniteDimensional ℝ E] in
/-- Under a unique intersection `p` with the affine hull of `sigma`, a
facet meets the edge exactly when it contains `p`. -/
theorem faceOneSimplexIntersectionNumber_eq_point_of_unique_affineSpan_inter
    (sigma omega : Finset E) (p v : E)
    (hinter : realization omega ∩
        (affineSpan ℝ (sigma : Set E) : Set E) = {p}) :
    faceOneSimplexIntersectionNumber (sigma.erase v) omega =
      pointIntersectionNumber (sigma.erase v) p := by
  have hfacetSpan :
      realization (sigma.erase v) ⊆
        (affineSpan ℝ (sigma : Set E) : Set E) := by
    intro y hy
    apply (affineSpan_mono ℝ (by exact_mod_cast Finset.erase_subset v sigma))
    exact convexHull_subset_affineSpan (sigma.erase v : Set E) hy
  have hpInter : p ∈ realization omega ∩
      (affineSpan ℝ (sigma : Set E) : Set E) := by
    rw [hinter]
    simp
  have hiff :
      (realization (sigma.erase v) ∩ realization omega).Nonempty ↔
        p ∈ realization (sigma.erase v) := by
    constructor
    · rintro ⟨x, hxFacet, hxOmega⟩
      have hxSingleton : x ∈ ({p} : Set E) := by
        rw [← hinter]
        exact ⟨hxOmega, hfacetSpan hxFacet⟩
      have hxp : x = p := by simpa using hxSingleton
      simpa [hxp] using hxFacet
    · intro hpFacet
      exact ⟨p, hpFacet, hpInter.1⟩
  simp only [faceOneSimplexIntersectionNumber, pointIntersectionNumber, hiff]

omit [FiniteDimensional ℝ E] in
/-- The unique-hyperplane-intersection case reduces exactly to point
intersection of the boundary chain at that point.  Thus the only remaining
codimension-one core is the parity of the facets containing `p`. -/
theorem boundary_oneIntersection_eq_boundary_pointIntersection_of_unique_affineSpan_inter
    (sigma omega : Finset E) (p : E)
    (hinter : realization omega ∩
        (affineSpan ℝ (sigma : Set E) : Set E) = {p}) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) =
      pointChainIntersection (boundary (singletonChain sigma))
        (singletonChain {p}) := by
  rw [oneChainIntersection_boundary_singleton,
    pointChainIntersection_boundary_singleton_point]
  apply Finset.sum_congr rfl
  intro v hv
  exact faceOneSimplexIntersectionNumber_eq_point_of_unique_affineSpan_inter
    sigma omega p v hinter

omit [FiniteDimensional ℝ E] in
/-- In the unique affine-hull intersection case of Lemma 10.4, the boundary
intersection vanishes.  The proof now uses the direct coefficient-interval
parity theorem above rather than an unformalized induction after identifying
the hyperplane with `ℝ^(n-1)`. -/
theorem boundary_oneIntersection_eq_zero_of_unique_affineSpan_inter
    (n : ℕ) (sigma omega : Finset E) (p : E) (hn : 0 < n)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    (hgp : OneSimplexInGeneralPosition sigma omega)
    (hinter : realization omega ∩
        (affineSpan ℝ (sigma : Set E) : Set E) = {p}) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) = 0 := by
  rw [boundary_oneIntersection_eq_boundary_pointIntersection_of_unique_affineSpan_inter
    sigma omega p hinter]
  apply boundary_pointIntersection_eq_zero_of_not_isGeneric n sigma p hn hsigma hng
  apply pointInGeneralPositionWithBoundary_of_mem_edge sigma omega p hgp
  have hpInter : p ∈ realization omega ∩
      (affineSpan ℝ (sigma : Set E) : Set E) := by
    rw [hinter]
    simp
  exact hpInter.1

omit [FiniteDimensional ℝ E] in
/-- If the edge is not contained in the affine span of `sigma`, its
intersection with that span is empty or a singleton.  Endpoint singletons
are excluded directly by general position; a nonvertex singleton is handled
by the facet-point parity theorem. -/
theorem boundary_point_eq_zero_of_edge_not_subset_affineSpan
    (n : ℕ) (sigma omega : Finset E) (hn : 0 < n)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    (hgp : OneSimplexInGeneralPosition sigma omega)
    (hnotContained : ¬realization omega ⊆
      (affineSpan ℝ (sigma : Set E) : Set E)) :
    oneChainIntersection (boundary (singletonChain sigma))
        (singletonChain omega) = 0 := by
  let S := realization omega ∩
    (affineSpan ℝ (sigma : Set E) : Set E)
  have hSSubsingleton : S.Subsingleton :=
    segment_inter_affineSubspace_subsingleton_of_not_subset
      omega (affineSpan ℝ (sigma : Set E)) hgp.1 hnotContained
  by_cases hS : S.Nonempty
  · obtain ⟨p, hpS⟩ := hS
    by_cases hpVertex : p ∈ omega
    · refine boundary_point_eq_zero_of_affineSpan_inter_subset_vertices
        sigma omega ?_ hgp
      intro q hq
      have hqp : q = p := hSSubsingleton hq hpS
      simpa [hqp] using hpVertex
    · have hSeq : S = {p} := by
        ext q
        constructor
        · intro hq
          simpa using hSSubsingleton hq hpS
        · intro hqp
          simpa using hqp ▸ hpS
      exact boundary_oneIntersection_eq_zero_of_unique_affineSpan_inter
        n sigma omega p hn hsigma hng hgp hSeq
  · refine boundary_point_eq_zero_of_affineSpan_inter_subset_vertices
      sigma omega ?_ hgp
    intro q hq
    exact (hS ⟨q, hq⟩).elim

omit [FiniteDimensional ℝ E] in
/-- Lemma 10.4 in the exact codimension-one branch. -/
theorem lemma10_4_of_finrank_eq_pred
    (n : ℕ) (sigma omega : Finset E) (hn : 0 < n)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) = n - 1)
    (hgp : OneSimplexInGeneralPosition sigma omega) :
    oneChainIntersection (boundary (singletonChain sigma))
          (singletonChain omega) = 0 ∧
      pointChainIntersection (singletonChain sigma)
          (boundary (singletonChain omega)) = 0 := by
  constructor
  · by_cases hcontained : realization omega ⊆
        (affineSpan ℝ (sigma : Set E) : Set E)
    · exact boundary_point_eq_zero_of_edge_subset_affineSpan
        n sigma omega hn hsigma hdim hgp hcontained
    · exact boundary_point_eq_zero_of_edge_not_subset_affineSpan
        n sigma omega hn hsigma hng hgp hcontained
  · exact point_boundary_eq_zero_of_not_isGeneric
      n sigma omega hsigma hng hgp

/-- Lemma 10.4 for the branch where the affine dimension of `sigma` is at
most `n - 2`.  Both claimed intersection numbers have now been proved, not
postulated through a compatibility interface. -/
theorem lemma10_4_of_finrank_add_two_le
    (n : ℕ) (sigma omega : Finset E)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) + 2 ≤ n)
    (hgp : OneSimplexInGeneralPosition sigma omega) :
    oneChainIntersection (boundary (singletonChain sigma))
          (singletonChain omega) = 0 ∧
      pointChainIntersection (singletonChain sigma)
          (boundary (singletonChain omega)) = 0 := by
  exact ⟨boundary_point_eq_zero_of_finrank_add_two_le
      n sigma omega hsigma hdim hgp,
    point_boundary_eq_zero_of_not_isGeneric n sigma omega hsigma hng hgp⟩

/-- Lemma 10.4 in full.  Unlike the paper's proof, the exact-codimension-one
case is discharged directly by affine-dependence coefficients; no appeal to
an unformalized identification of a hyperplane with `ℝ^(n-1)` remains. -/
theorem lemma10_4
    (n : ℕ) (sigma omega : Finset E)
    (_hdimAmbient : Module.finrank ℝ E = n)
    (hsigma : IsMSimplex n sigma) (hng : ¬IsGeneric sigma)
    (hgp : OneSimplexInGeneralPosition sigma omega) :
    oneChainIntersection (boundary (singletonChain sigma))
          (singletonChain omega) = 0 ∧
      pointChainIntersection (singletonChain sigma)
          (boundary (singletonChain omega)) = 0 := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hcard : sigma.card = 1 := by
      simpa [IsMSimplex, hn0] using hsigma
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hcard
    apply hng
    let : Subsingleton ↥((({z} : Finset E) : Set E)) :=
      ⟨fun a b ↦ Subtype.ext (by
        have ha : a.1 = z := by simpa using a.property
        have hb : b.1 = z := by simpa using b.property
        exact ha.trans hb.symm)⟩
    exact affineIndependent_of_subsingleton ℝ _
  have hdimLe :=
    finrank_vectorSpan_le_pred_of_not_isGeneric n sigma hsigma hng
  by_cases hlow :
      Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) + 2 ≤ n
  · exact lemma10_4_of_finrank_add_two_le
      n sigma omega hsigma hng hlow hgp
  · have heq :
        Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) = n - 1 := by
      omega
    exact lemma10_4_of_finrank_eq_pred
      n sigma omega hn hsigma hng heq hgp

end EuclideanIntersection
end BeyondSperner
