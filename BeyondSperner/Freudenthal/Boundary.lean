import BeyondSperner.Freudenthal.Connectivity

/-!
# Coordinate-face chains in the Freudenthal induction

The complex-level coordinate-face identifications in
`FreudenthalFaces` are not by themselves sufficient for equations (19)--(21)
of Ivanov's proof: the lower-dimensional chains live on `Point N n`, the
face chains live on a subtype of `Point N (n+1)`, and the boundary formula
lives in the ambient chain group on `Point N (n+1)`.

This file supplies the two injective pushforwards and proves that they neither
lose nor merge simplex coefficients.  Thus all later boundary identities are
literal equalities in one ambient `F₂`-chain group.
-/

namespace BeyondSperner

open Classical

namespace IntegerSimplex

/-- Inclusion of a bundled coordinate-face point into the ambient integer
simplex. -/
def zeroFaceInclusion {N n : ℕ} (k : Fin (n + 2)) :
    ZeroFacePoint (N := N) k ↪ Point N (n + 1) :=
  Function.Embedding.subtype _

/-- Insertion of a zero coordinate, packaged as an embedding. -/
def insertZeroPointEmbedding {N n : ℕ} (k : Fin (n + 2)) :
    Point N n ↪ Point N (n + 1) where
  toFun := insertZeroPoint k
  inj' := insertZeroPoint_injective k

/-- Passing through the bundled face subtype is exactly direct insertion of
the zero coordinate. -/
theorem zeroFaceEquiv_trans_inclusion {N n : ℕ} (k : Fin (n + 2)) :
    (zeroFaceEquiv (N := N) k).toEmbedding.trans
        (zeroFaceInclusion k) =
      insertZeroPointEmbedding k := by
  rfl

/-- In a finite index set with at least two elements, deleting one element
from `univ` remembers which element was deleted. -/
theorem univ_erase_injective_fin {m : ℕ} :
    Function.Injective
      (fun k : Fin m ↦ (Finset.univ : Finset (Fin m)).erase k) := by
  intro k l hkl
  by_contra hne
  have hkMem : k ∈ (Finset.univ : Finset (Fin m)).erase l := by
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ k⟩
  change (Finset.univ : Finset (Fin m)).erase k =
    Finset.univ.erase l at hkl
  rw [← hkl] at hkMem
  exact (Finset.mem_erase.mp hkMem).1 rfl

/-- The codimension-one subsets of `Fin (n+2)` are exactly the sets obtained
by erasing one index.  The `n+2` parameter is deliberate: it also makes the
erase parametrization injective, so subsequent sums have no multiplicity
ambiguity. -/
theorem boundaryIndices_univ_fin (n : ℕ) :
    SimplexFamily.boundaryIndices
        (Finset.univ : Finset (Fin (n + 2))) =
      (Finset.univ : Finset (Fin (n + 2))).image
        (fun k ↦ (Finset.univ : Finset (Fin (n + 2))).erase k) := by
  ext B
  constructor
  · intro hB
    have hBData := Finset.mem_filter.mp hB
    have hBSub : B ⊆ (Finset.univ : Finset (Fin (n + 2))) :=
      Finset.mem_powerset.mp hBData.1
    have hBNe : B ≠ (Finset.univ : Finset (Fin (n + 2))) := by
      intro hEq
      rw [hEq] at hBData
      simp at hBData
    obtain ⟨k, _, hkB⟩ := Finset.exists_of_ssubset
      ((Finset.ssubset_iff_subset_ne).2 ⟨hBSub, hBNe⟩)
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ i⟩
      intro hik
      subst i
      exact hkB hi
    · rw [Finset.card_erase_of_mem (Finset.mem_univ k)]
      simp only [Finset.card_univ, Fintype.card_fin]
      have hcard : B.card + 1 = n + 2 := by
        simpa using hBData.2
      omega
  · intro hB
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hB
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr (Finset.erase_subset _ _)
    · simp

/-- The Scarf top chain is the fixed-cardinality chain of its associated
complex. -/
theorem associatedTopChain_eq_complexCardChain (N n : ℕ) :
    associatedTopChain N n =
      SimplexFamily.complexCardChain
        ((pointOrders N n).associatedComplex Finset.univ) (n + 1) := by
  rw [associatedTopChain,
    SimplexFamily.topChain_eq_complexCardChain]
  simp [IndexedLinearOrders.associatedFamily]

/-- The concrete facet sum is the fixed-cardinality chain of the generated
Freudenthal complex. -/
theorem freudenthalTopChain_eq_complexCardChain (N n : ℕ) :
    freudenthalTopChain N n =
      SimplexFamily.complexCardChain (freudenthalComplex N n) (n + 1) := by
  rw [freudenthalTopChain, FacetChain.sum,
    SimplexFamily.complexCardChain, freudenthalFacets_eq_topSimplices]

/-- The ambient chain carried by the `k`-th Freudenthal coordinate face. -/
noncomputable def freudenthalCoordinateFaceChain (N n : ℕ)
    (k : Fin (n + 2)) :
    SimplexFamily.Chain (Point N (n + 1)) :=
  SimplexFamily.mapChainHom (zeroFaceInclusion k)
    (SimplexFamily.complexCardChain
      (freudenthalCoordinateFaceComplex N n k) (n + 1))

/-- The ambient chain carried by the `k`-th Scarf coordinate face. -/
noncomputable def scarfCoordinateFaceChain (N n : ℕ)
    (k : Fin (n + 2)) :
    SimplexFamily.Chain (Point N (n + 1)) :=
  SimplexFamily.mapChainHom (zeroFaceInclusion k)
    (SimplexFamily.complexCardChain
      (scarfCoordinateFaceComplex N n k) (n + 1))

/-- Coordinates which vanish at every vertex of a finite simplex.  For a
codimension-one Freudenthal simplex this is the exact ambient-boundary
incidence set appearing on the right side of formula (19). -/
noncomputable def commonZeroCoordinates {N d : ℕ}
    (rho : Finset (Point N d)) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun k ↦ ∀ a ∈ rho, (a.1 k).val = 0

theorem mem_commonZeroCoordinates_iff {N d : ℕ}
    (rho : Finset (Point N d)) (k : Fin (d + 1)) :
    k ∈ commonZeroCoordinates rho ↔
      ∀ a ∈ rho, (a.1 k).val = 0 := by
  simp [commonZeroCoordinates]

/-- Coefficient formula for one ambient Freudenthal coordinate-face chain.
It explicitly records all three necessary conditions: ambient-complex
membership, the correct face cardinality, and vanishing of that coordinate
at every vertex. -/
@[simp]
theorem freudenthalCoordinateFaceChain_apply
    (N n : ℕ) (k : Fin (n + 2))
    (rho : Finset (Point N (n + 1))) :
    freudenthalCoordinateFaceChain N n k rho =
      if rho ∈ freudenthalComplex N (n + 1) ∧
          rho.card = n + 1 ∧ k ∈ commonZeroCoordinates rho then
        1
      else 0 := by
  by_cases hk : k ∈ commonZeroCoordinates rho
  · have hzero : ∀ a ∈ rho, (a.1 k).val = 0 :=
      (mem_commonZeroCoordinates_iff rho k).1 hk
    let sigma : Finset (ZeroFacePoint (N := N) k) :=
      bundleZeroFaceSimplex k rho
    have himage : sigma.image Subtype.val = rho :=
      image_bundleZeroFaceSimplex k rho hzero
    have himage' : sigma.image (zeroFaceInclusion k) = rho := by
      simpa [zeroFaceInclusion] using himage
    have hcard : sigma.card = rho.card := by
      rw [← Finset.card_image_of_injective sigma Subtype.val_injective,
        himage]
    rw [freudenthalCoordinateFaceChain, ← himage',
      SimplexFamily.mapChainHom_apply_image,
      SimplexFamily.complexCardChain_apply]
    have hmem : sigma ∈ freudenthalCoordinateFaceComplex N n k ↔
        rho ∈ freudenthalComplex N (n + 1) := by
      rw [mem_freudenthalCoordinateFaceComplex_iff, himage]
    rw [himage']
    simp only [hmem, hcard, hk, and_true]
  · have hnotImage : ¬∃ sigma : Finset (ZeroFacePoint (N := N) k),
        sigma.image (zeroFaceInclusion k) = rho := by
      rintro ⟨sigma, hsigma⟩
      apply hk
      apply (mem_commonZeroCoordinates_iff rho k).2
      intro a ha
      rw [← hsigma] at ha
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
      exact b.2
    rw [freudenthalCoordinateFaceChain,
      SimplexFamily.mapChainHom_apply_eq_zero_of_not_exists
        (zeroFaceInclusion k) _ rho hnotImage]
    simp [hk]

/-- Pointwise value of the sum of all coordinate-face chains.  Outside the
ambient complex or outside codimension one it is zero; on a codimension-one
simplex it is the number of common zero coordinates, reduced modulo two. -/
theorem sum_freudenthalCoordinateFaceChains_apply
    (N n : ℕ) (rho : Finset (Point N (n + 1))) :
    (∑ k : Fin (n + 2), freudenthalCoordinateFaceChain N n k) rho =
      if rho ∈ freudenthalComplex N (n + 1) ∧ rho.card = n + 1 then
        ((commonZeroCoordinates rho).card : ZMod 2)
      else 0 := by
  by_cases hmain : rho ∈ freudenthalComplex N (n + 1) ∧
      rho.card = n + 1
  · rw [if_pos hmain, Finsupp.finsetSum_apply]
    simp only [freudenthalCoordinateFaceChain_apply,
      hmain.1, hmain.2, true_and]
    rw [Finset.sum_boole]
    simp
  · rw [if_neg hmain, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [freudenthalCoordinateFaceChain_apply, if_neg]
    exact fun h ↦ hmain ⟨h.1, h.2.1⟩

/-- Pointwise coefficient of the boundary of the Freudenthal top chain. -/
theorem boundary_freudenthalTopChain_apply
    (N n : ℕ) (rho : Finset (Point N (n + 1))) :
    SimplexFamily.boundary (freudenthalTopChain N (n + 1)) rho =
      if rho.card = n + 1 then
        (((freudenthalFacets N (n + 1)).filter
          fun sigma ↦ rho ⊆ sigma).card : ZMod 2)
      else 0 := by
  by_cases hcard : rho.card = n + 1
  · rw [if_pos hcard, freudenthalTopChain,
      FacetChain.boundary_sum_apply_of_card
        freudenthalFacets_isPure hcard]
  · rw [if_neg hcard, freudenthalTopChain,
      FacetChain.boundary_sum_apply_of_card_ne
        freudenthalFacets_isPure hcard]

/-- A simplex outside the Freudenthal complex has no containing
Freudenthal facet. -/
theorem freudenthalCofaces_eq_empty_of_not_mem
    {N d : ℕ} {rho : Finset (Point N d)}
    (hrho : rho ∉ freudenthalComplex N d) :
    (freudenthalFacets N d).filter (fun sigma ↦ rho ⊆ sigma) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro sigma hsigma
  have hsigmaData := Finset.mem_filter.mp hsigma
  apply hrho
  exact (freudenthalComplex N d).downward_closed
    ((mem_freudenthalFacets_iff sigma).1 hsigmaData.1).mem_complex
    hsigmaData.2

/-- The exact remaining local statement behind formula (19): for every
actual codimension-one simplex, coface parity equals ambient coordinate-face
parity.  This is a predicate, not an assumed theorem. -/
def FreudenthalBoundaryIncidenceParity (N n : ℕ) : Prop :=
  ∀ rho : Finset (Point N (n + 1)),
    rho ∈ freudenthalComplex N (n + 1) →
    rho.card = n + 1 →
    (((freudenthalFacets N (n + 1)).filter
      fun sigma ↦ rho ⊆ sigma).card : ZMod 2) =
      ((commonZeroCoordinates rho).card : ZMod 2)

/-- At positive scale, a genuine top-dimensional Freudenthal simplex cannot
be contained in a coordinate face.  In positive dimension this follows from
the exact coordinate-face identification and the strict lower-dimensional
cardinality bound; dimension zero is checked directly from the positive
coordinate sum. -/
theorem IsFreudenthalTopSimplex.not_all_coord_zero
    {N d : ℕ} (hN : 0 < N) {rho : Finset (Point N d)}
    (hrho : IsFreudenthalTopSimplex rho) (k : Fin (d + 1)) :
    ¬∀ a ∈ rho, (a.1 k).val = 0 := by
  cases d with
  | zero =>
      intro hzero
      have hrhoNonempty : rho.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have hcard := hrho.card
        rw [hempty] at hcard
        simp at hcard
      obtain ⟨a, ha⟩ := hrhoNonempty
      have haSum := a.2
      have hak := hzero a ha
      have hk : k = (0 : Fin 1) := Fin.eq_zero k
      subst k
      have ha0 : (a.1 (0 : Fin 1)).val = N := by
        simpa using haSum
      omega
  | succ n =>
      intro hzero
      let sigma : Finset (ZeroFacePoint (N := N) k) :=
        bundleZeroFaceSimplex k rho
      have himage : sigma.image Subtype.val = rho :=
        image_bundleZeroFaceSimplex k rho hzero
      have hsigmaFace : sigma ∈
          freudenthalCoordinateFaceComplex N n k :=
        (mem_freudenthalCoordinateFaceComplex_iff k sigma).2 (by
          rw [himage]
          exact hrho.mem_complex)
      have hsigmaLower : sigma ∈
          lowerFreudenthalRelabeledToFace N n k := by
        rw [lowerFreudenthalRelabeledToFace_eq_coordinateFace hN]
        exact hsigmaFace
      obtain ⟨tau, htau, htauImage⟩ :=
        (FiniteSimplicialComplex.mem_relabel_iff
          (freudenthalComplex N n) (zeroFaceEquiv k) sigma).1
          hsigmaLower
      have hsigmaCard : sigma.card = n + 2 := by
        rw [← Finset.card_image_of_injective sigma Subtype.val_injective,
          himage, hrho.card]
      have htauCard : tau.card = sigma.card := by
        rw [← Finset.card_image_of_injective tau
          (zeroFaceEquiv k).injective, htauImage]
      have htauLe := freudenthalComplex_card_le htau
      omega

/-- An actual codimension-one Freudenthal simplex at positive scale lies in
at most one ambient coordinate face.  The proof lowers through one alleged
coordinate face; a second common zero coordinate would make the resulting
lower top simplex lie entirely in a lower coordinate face, contradicting the
previous theorem. -/
theorem commonZeroCoordinates_card_le_one
    {N n : ℕ} (hN : 0 < N)
    {rho : Finset (Point N (n + 1))}
    (hrho : rho ∈ freudenthalComplex N (n + 1))
    (hcard : rho.card = n + 1) :
    (commonZeroCoordinates rho).card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro k l hk hl
  by_contra hkl
  have hkzero : ∀ a ∈ rho, (a.1 k).val = 0 :=
    (mem_commonZeroCoordinates_iff rho k).1 hk
  have hlzero : ∀ a ∈ rho, (a.1 l).val = 0 :=
    (mem_commonZeroCoordinates_iff rho l).1 hl
  let sigma : Finset (ZeroFacePoint (N := N) k) :=
    bundleZeroFaceSimplex k rho
  have himage : sigma.image Subtype.val = rho :=
    image_bundleZeroFaceSimplex k rho hkzero
  have hsigmaFace : sigma ∈ freudenthalCoordinateFaceComplex N n k :=
    (mem_freudenthalCoordinateFaceComplex_iff k sigma).2 (by
      rw [himage]
      exact hrho)
  have hsigmaLower : sigma ∈ lowerFreudenthalRelabeledToFace N n k := by
    rw [lowerFreudenthalRelabeledToFace_eq_coordinateFace hN]
    exact hsigmaFace
  obtain ⟨tau, htau, htauImage⟩ :=
    (FiniteSimplicialComplex.mem_relabel_iff
      (freudenthalComplex N n) (zeroFaceEquiv k) sigma).1
      hsigmaLower
  have hsigmaCard : sigma.card = rho.card := by
    rw [← Finset.card_image_of_injective sigma Subtype.val_injective,
      himage]
  have htauCard : tau.card = n + 1 := by
    rw [← Finset.card_image_of_injective tau
      (zeroFaceEquiv k).injective, htauImage, hsigmaCard, hcard]
  have htauTop : IsFreudenthalTopSimplex tau := by
    apply (mem_freudenthalFacets_iff tau).1
    rw [freudenthalFacets_eq_topSimplices]
    exact Finset.mem_filter.mpr ⟨htau, htauCard⟩
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hkl)
  apply htauTop.not_all_coord_zero hN j
  intro a ha
  have haImage : zeroFaceEquiv k a ∈ sigma := by
    rw [← htauImage]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have haAmbient : (zeroFaceEquiv k a).1 ∈ rho := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨zeroFaceEquiv k a, haImage, rfl⟩
  have hz := hlzero (zeroFaceEquiv k a).1 haAmbient
  rw [zeroFaceEquiv_apply_val, ← hj,
    insertZeroPoint_apply_succAbove] at hz
  exact hz

/-! ## Exact incidence on the first coordinate face -/

/-- Inserting a zero as the first original coordinate makes the first
cumulative coordinate zero. -/
@[simp]
theorem pointPrefix_insertZeroPoint_zero_zero {N n : ℕ}
    (a : Point N n) :
    pointPrefix (insertZeroPoint (0 : Fin (n + 2)) a)
        (0 : Fin (n + 1)) = 0 := by
  rw [pointPrefix, prefixMap_zero, pointCoords_insertZeroPoint,
    insertZeroCoords_apply_self]

/-- Every other cumulative coordinate on the first coordinate face is the
corresponding lower-dimensional cumulative coordinate. -/
@[simp]
theorem pointPrefix_insertZeroPoint_zero_succ {N n : ℕ}
    (a : Point N n) (q : Fin n) :
    pointPrefix (insertZeroPoint (0 : Fin (n + 2)) a) q.succ =
      pointPrefix a q := by
  cases n with
  | zero => exact Fin.elim0 q
  | succ n =>
      induction q using Fin.induction with
      | zero =>
          rw [pointPrefix, prefixMap_succ, pointPrefix, prefixMap_zero,
            pointCoords_insertZeroPoint]
          rw [prefixMap_eq_of_val_zero _ _ rfl]
          rw [insertZeroCoords_apply_self]
          rw [show (Fin.succ (0 : Fin (n + 1))).castSucc =
            (0 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) by rfl,
            insertZeroCoords_apply_succAbove]
          simp
      | succ q ih =>
          change prefixMap
              (pointCoords (insertZeroPoint (0 : Fin (n + 3)) a))
                q.succ.succ =
            prefixMap (pointCoords a) q.succ
          rw [prefixMap_succ, prefixMap_succ]
          change pointPrefix
                (insertZeroPoint (0 : Fin (n + 3)) a) q.castSucc.succ + _ = _
          rw [ih, pointCoords_insertZeroPoint]
          rw [show q.succ.succ.castSucc =
            (0 : Fin (n + 3)).succAbove q.succ.castSucc by rfl,
            insertZeroCoords_apply_succAbove]
          simp [pointPrefix]

/-- First-face insertion preserves intrinsic cumulative weight. -/
@[simp]
theorem cumulativeWeight_pointPrefix_insertZeroPoint_zero {N n : ℕ}
    (a : Point N n) :
    cumulativeWeight
        (pointPrefix (insertZeroPoint (0 : Fin (n + 2)) a)) =
      cumulativeWeight (pointPrefix a) := by
  rw [cumulativeWeight, Fin.sum_univ_succ]
  simp [cumulativeWeight]

/-- The cumulative ranks of a lifted first-coordinate facet are obtained by
deleting the last rank of the unique ambient consecutive block. -/
theorem image_cumulativeWeight_zeroFace_eq_erase_last
    {N n : ℕ} {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho) :
    ∃ z : ℤ,
      (rho.image (insertZeroPoint (0 : Fin (n + 2)))).image
          (fun a ↦ cumulativeWeight (pointPrefix a)) =
        (consecutiveRanks z (n + 1)).erase (z + n + 1) := by
  obtain ⟨u, hu⟩ := hrho.image_cumulativeWeight_pointPrefix
  let z := cumulativeWeight u
  refine ⟨z, ?_⟩
  calc
    (rho.image (insertZeroPoint (0 : Fin (n + 2)))).image
        (fun a ↦ cumulativeWeight (pointPrefix a)) =
      rho.image (fun a ↦ cumulativeWeight (pointPrefix a)) := by
        ext x
        simp
    _ = consecutiveRanks z n := hu
    _ = (consecutiveRanks z (n + 1)).erase (z + n + 1) := by
      ext x
      simp only [Finset.mem_erase]
      rw [mem_consecutiveRanks_iff_bounds,
        mem_consecutiveRanks_iff_bounds]
      constructor
      · intro hx
        exact ⟨by omega, by omega⟩
      · rintro ⟨hne, hx⟩
        constructor
        · exact hx.1
        · by_contra hnot
          have : x = z + n + 1 := by omega
          exact hne this

/-- A lifted first-coordinate facet belongs to exactly one ambient top
simplex.  The formal obstruction to a second (lower-rank) completion is the
impossible cumulative coordinate `-1` at index zero. -/
theorem zeroFace_cofacets_card_eq_one
    {N n : ℕ} (hN : 0 < N)
    {rho : Finset (Point N n)} (hrho : IsFreudenthalTopSimplex rho) :
    ((freudenthalFacets N (n + 1)).filter fun tau ↦
      rho.image (insertZeroPoint (0 : Fin (n + 2))) ⊆ tau).card = 1 := by
  let face : Finset (Point N (n + 1)) :=
    rho.image (insertZeroPoint (0 : Fin (n + 2)))
  let weight : Point N (n + 1) → ℤ :=
    fun a ↦ cumulativeWeight (pointPrefix a)
  let C := (freudenthalFacets N (n + 1)).filter fun tau ↦ face ⊆ tau
  have hfaceCard : face.card = n + 1 := by
    change (rho.image (insertZeroPoint (0 : Fin (n + 2)))).card = n + 1
    rw [Finset.card_image_of_injective]
    · exact hrho.card
    · exact insertZeroPoint_injective _
  have hfaceMem : face ∈ freudenthalComplex N (n + 1) :=
    image_insertZeroPoint_zero_mem_freudenthalComplex hN hrho
  have hfaceSimplex := (mem_freudenthalComplex_iff face).1 hfaceMem
  obtain ⟨sigma₀, hsigma₀, hfaceSigma₀⟩ :
      ∃ sigma₀, IsFreudenthalTopSimplex sigma₀ ∧ face ⊆ sigma₀ := by
    rcases hfaceSimplex with hzero | htop
    · exfalso
      have : face.card = 0 := by rw [hzero]; simp
      omega
    · exact htop
  have hsigma₀C : sigma₀ ∈ C := by
    exact Finset.mem_filter.mpr
      ⟨(mem_freudenthalFacets_iff sigma₀).2 hsigma₀,
        hfaceSigma₀⟩
  obtain ⟨z, hRerase⟩ := image_cumulativeWeight_zeroFace_eq_erase_last hrho
  change face.image weight =
    (consecutiveRanks z (n + 1)).erase (z + n + 1) at hRerase
  have hcardR : (face.image weight).card = n + 1 := by
    rw [Finset.card_image_of_injOn]
    · exact hfaceCard
    · intro a ha b hb hab
      exact hsigma₀.cumulativeWeight_pointPrefix_injective
        (hfaceSigma₀ ha) (hfaceSigma₀ hb) hab
  have hxRank : z ∈ face.image weight := by
    rw [hRerase]
    exact Finset.mem_erase.mpr ⟨by omega,
      mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)⟩
  have hyRank : z + n ∈ face.image weight := by
    rw [hRerase]
    exact Finset.mem_erase.mpr ⟨by omega,
      mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)⟩
  obtain ⟨x, hxFace, hxWeight⟩ := Finset.mem_image.mp hxRank
  obtain ⟨y, hyFace, hyWeight⟩ := Finset.mem_image.mp hyRank
  have hxy : pointPrefix x ≤ pointPrefix y :=
    hsigma₀.pointPrefix_le_of_weight_le
      (hfaceSigma₀ hxFace) (hfaceSigma₀ hyFace)
      (by change weight x ≤ weight y; omega)
  have hxyWeight : cumulativeWeight (pointPrefix y) =
      cumulativeWeight (pointPrefix x) + n := by
    change weight y = weight x + n
    omega
  have husedCard :
      (positiveCoords (pointPrefix x) (pointPrefix y)).card = n :=
    hsigma₀.card_positiveCoords_eq
      (hfaceSigma₀ hxFace) (hfaceSigma₀ hyFace)
      hxy hxyWeight
  have hunusedCard :
      ((Finset.univ : Finset (Fin (n + 1))) \
        positiveCoords (pointPrefix x) (pointPrefix y)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, husedCard]
    omega
  have hxZero : pointPrefix x (0 : Fin (n + 1)) = 0 := by
    obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.mp hxFace
    exact pointPrefix_insertZeroPoint_zero_zero x₀
  have hyZero : pointPrefix y (0 : Fin (n + 1)) = 0 := by
    obtain ⟨y₀, _, rfl⟩ := Finset.mem_image.mp hyFace
    exact pointPrefix_insertZeroPoint_zero_zero y₀
  have hzeroUnused : (0 : Fin (n + 1)) ∈
      (Finset.univ : Finset (Fin (n + 1))) \
        positiveCoords (pointPrefix x) (pointPrefix y) := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      simp [positiveCoords, hxZero, hyZero]⟩
  have hunusedEq :
      (Finset.univ : Finset (Fin (n + 1))) \
          positiveCoords (pointPrefix x) (pointPrefix y) = {0} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hzeroUnused, ?_⟩
    intro i hi
    exact Finset.card_le_one_iff.mp (by omega) hi hzeroUnused
  have offVertexUpper : ∀ tau, tau ∈ C →
      ∃ a : Point N (n + 1),
        tau \ face = {a} ∧ a ∈ tau ∧ weight a = z + n + 1 := by
    intro tau htauC
    have htauData := Finset.mem_filter.mp htauC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hdiffCard := card_sdiff_codimFace_of_topSimplex
      hfaceCard htauTop htauData.2
    obtain ⟨a, haDiff⟩ := Finset.card_eq_one.mp hdiffCard
    have haDiffMem : a ∈ tau \ face := by rw [haDiff]; simp
    have haTau := (Finset.mem_sdiff.mp haDiffMem).1
    have haNotFace := (Finset.mem_sdiff.mp haDiffMem).2
    obtain ⟨w, hwRanks⟩ := htauTop.image_cumulativeWeight_pointPrefix
    have hRw : face.image weight ⊆
        consecutiveRanks (cumulativeWeight w) (n + 1) := by
      rw [← hwRanks]
      exact Finset.image_mono _ htauData.2
    have haW : weight a ∈
        consecutiveRanks (cumulativeWeight w) (n + 1) := by
      rw [← hwRanks]
      exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
    have haNotImage : weight a ∉ face.image weight := by
      intro haImage
      obtain ⟨b, hbFace, hbWeight⟩ := Finset.mem_image.mp haImage
      have hab : a = b := htauTop.cumulativeWeight_pointPrefix_injective
        haTau (htauData.2 hbFace) hbWeight.symm
      exact haNotFace (hab ▸ hbFace)
    have hmBlock : z + n + 1 ∈ consecutiveRanks z (n + 1) :=
      mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)
    have haCases := completion_rank_cases (Nat.succ_pos n) hcardR
      hmBlock hRerase hRw haW haNotImage
    have haWeight : weight a = z + n + 1 := by
      rcases haCases with haUpper | haImpossible | haLower
      · exact haUpper
      · omega
      · have haWeightLower : weight a = z - 1 := haLower.2
        have hax : pointPrefix a ≤ pointPrefix x :=
          htauTop.pointPrefix_le_of_weight_le haTau
            (htauData.2 hxFace) (by
              change weight a ≤ weight x
              omega)
        have hstepWeight : cumulativeWeight (pointPrefix x) =
            cumulativeWeight (pointPrefix a) + 1 := by
          change weight x = weight a + 1
          omega
        have hpos := positiveCoords_nonempty_of_le_of_weight_add_one
          hax hstepWeight
        obtain ⟨i, hiPos⟩ := hpos
        have hxEq := eq_add_single_of_le_of_weight_add_one
          hax hstepWeight (Finset.mem_filter.mp hiPos).2
        have hiUnused : i ∈
            (Finset.univ : Finset (Fin (n + 1))) \
              positiveCoords (pointPrefix x) (pointPrefix y) := by
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hiUsed
          have hiLt := (Finset.mem_filter.mp hiUsed).2
          have haY : pointPrefix a ≤ pointPrefix y := hax.trans hxy
          have hiStep := htauTop.coordinate_sub_eq_zero_or_one
            haTau (htauData.2 hyFace) haY i
          have hxi : pointPrefix x i = pointPrefix a i + 1 := by
            rw [hxEq]
            simp
          rcases hiStep with hiStep | hiStep <;> omega
        have hiZero : i = (0 : Fin (n + 1)) := by
          rw [hunusedEq] at hiUnused
          simpa using hiUnused
        have haZero : pointPrefix a (0 : Fin (n + 1)) = -1 := by
          subst i
          have hxZeroStep : pointPrefix x (0 : Fin (n + 1)) =
              pointPrefix a 0 + 1 := by
            rw [hxEq]
            simp
          omega
        have haNonneg := (pointPrefix_isGammaPoint a).1
          (0 : Fin (n + 1))
        omega
    exact ⟨a, haDiff, haTau, haWeight⟩
  have hCsubsingleton : C.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro tau sigma htauC hsigmaC
    obtain ⟨a, hdiffTau, haTau, haWeight⟩ :=
      offVertexUpper tau htauC
    obtain ⟨b, hdiffSigma, hbSigma, hbWeight⟩ :=
      offVertexUpper sigma hsigmaC
    have htauData := Finset.mem_filter.mp htauC
    have hsigmaData := Finset.mem_filter.mp hsigmaC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hsigmaTop := (mem_freudenthalFacets_iff sigma).1 hsigmaData.1
    have hab : a = b := upper_completion_point_unique
      htauTop hsigmaTop htauData.2 hsigmaData.2 hxFace hyFace
      haTau hbSigma hxy
      (by change weight a = weight y + 1; omega)
      (by change weight b = weight y + 1; omega)
      hunusedCard
    exact sdiff_injective_on_cofacets htauC hsigmaC (by
      change tau \ face = sigma \ face
      rw [hdiffTau, hdiffSigma, hab])
  have hCnonempty : C.Nonempty := ⟨sigma₀, hsigma₀C⟩
  change C.card = 1
  exact Nat.le_antisymm hCsubsingleton (Finset.one_le_card.mpr hCnonempty)

/-! ## Exact incidence on an interior coordinate face -/

/-- Successive cumulative coordinates differ by the intervening original
simplex coordinate. -/
theorem pointPrefix_succ_eq_prev_add_coord
    {N n : ℕ} (a : Point N (n + 1)) (q : Fin n) :
    pointPrefix a q.succ = pointPrefix a q.castSucc +
      (a.1 q.succ.castSucc).val := by
  exact prefixMap_succ (pointCoords a) q

/-- On the coordinate face indexed by `q.succ`, the two adjacent
cumulative coordinates coincide. -/
theorem pointPrefix_insertZeroPoint_interior_eq
    {N n : ℕ} (q : Fin n) (a : Point N n) :
    pointPrefix (insertZeroPoint q.castSucc.succ a) q.succ =
      pointPrefix (insertZeroPoint q.castSucc.succ a) q.castSucc := by
  rw [pointPrefix_succ_eq_prev_add_coord]
  have hindex : q.succ.castSucc = q.castSucc.succ := by
    apply Fin.ext
    rfl
  rw [hindex, insertZeroPoint_apply_self]
  simp

/-- Extreme vertices of a Freudenthal top simplex differ by the all-ones
vector whenever their intrinsic ranks differ by the full dimension. -/
theorem IsFreudenthalTopSimplex.pointPrefix_eq_add_one_of_weight_distance
    {N d : ℕ} {sigma : Finset (Point N d)}
    (hsigma : IsFreudenthalTopSimplex sigma)
    {x y : Point N d} (hx : x ∈ sigma) (hy : y ∈ sigma)
    (hweight : cumulativeWeight (pointPrefix y) =
      cumulativeWeight (pointPrefix x) + d) :
    pointPrefix y = pointPrefix x + 1 := by
  have hxy : pointPrefix x ≤ pointPrefix y :=
    hsigma.pointPrefix_le_of_weight_le hx hy (by omega)
  have hcard :
      (positiveCoords (pointPrefix x) (pointPrefix y)).card = d :=
    hsigma.card_positiveCoords_eq hx hy hxy hweight
  have huniv : positiveCoords (pointPrefix x) (pointPrefix y) =
      (Finset.univ : Finset (Fin d)) :=
    Finset.eq_univ_of_card _ (by simpa using hcard)
  funext i
  have hiLt : pointPrefix x i < pointPrefix y i := by
    have : i ∈ positiveCoords (pointPrefix x) (pointPrefix y) := by
      rw [huniv]
      exact Finset.mem_univ i
    exact (Finset.mem_filter.mp this).2
  have hiStep := hsigma.coordinate_sub_eq_zero_or_one hx hy hxy i
  simp only [Pi.add_apply, Pi.one_apply]
  rcases hiStep with hiStep | hiStep <;> omega

/-- A lifted interior-coordinate facet belongs to exactly one ambient top
simplex.  Its unique off-face vertex is the bridge point obtained by first
incrementing the right cumulative coordinate.  The opposite ordering would
violate monotonicity across the two equal face coordinates. -/
theorem interiorFace_cofacets_card_eq_one
    {N n : ℕ} (hN : 0 < N) (q : Fin n)
    {rho : Finset (Point N n)} (hrho : IsFreudenthalTopSimplex rho) :
    ((freudenthalFacets N (n + 1)).filter fun tau ↦
      rho.image (insertZeroPoint q.castSucc.succ) ⊆ tau).card = 1 := by
  let k : Fin (n + 2) := q.castSucc.succ
  let left : Fin (n + 1) := q.castSucc
  let right : Fin (n + 1) := q.succ
  let face : Finset (Point N (n + 1)) :=
    rho.image (insertZeroPoint k)
  let weight : Point N (n + 1) → ℤ :=
    fun a ↦ cumulativeWeight (pointPrefix a)
  let C := (freudenthalFacets N (n + 1)).filter fun tau ↦ face ⊆ tau
  have hk : k = q.castSucc.succ := rfl
  have hleft : left = q.castSucc := rfl
  have hright : right = q.succ := rfl
  have hfaceCard : face.card = n + 1 := by
    change (rho.image (insertZeroPoint k)).card = n + 1
    rw [Finset.card_image_of_injective]
    · exact hrho.card
    · exact insertZeroPoint_injective _
  have hfaceMem : face ∈ freudenthalComplex N (n + 1) := by
    have hd : q.castSucc ≠ Fin.last n := Fin.castSucc_ne_last q
    simpa [face, k] using
      (image_insertZeroPoint_interior_mem_freudenthalComplex
        q.castSucc hd hrho)
  have hfaceSimplex := (mem_freudenthalComplex_iff face).1 hfaceMem
  obtain ⟨sigma₀, hsigma₀, hfaceSigma₀⟩ :
      ∃ sigma₀, IsFreudenthalTopSimplex sigma₀ ∧ face ⊆ sigma₀ := by
    rcases hfaceSimplex with hzero | htop
    · exfalso
      have : face.card = 0 := by rw [hzero]; simp
      omega
    · exact htop
  have hsigma₀C : sigma₀ ∈ C := by
    exact Finset.mem_filter.mpr
      ⟨(mem_freudenthalFacets_iff sigma₀).2 hsigma₀,
        hfaceSigma₀⟩
  have hdiffCard₀ := card_sdiff_codimFace_of_topSimplex
    hfaceCard hsigma₀ hfaceSigma₀
  obtain ⟨a₀, hdiff₀⟩ := Finset.card_eq_one.mp hdiffCard₀
  have ha₀Diff : a₀ ∈ sigma₀ \ face := by rw [hdiff₀]; simp
  have ha₀Sigma := (Finset.mem_sdiff.mp ha₀Diff).1
  have ha₀NotFace := (Finset.mem_sdiff.mp ha₀Diff).2
  have hfaceErase₀ : face = sigma₀.erase a₀ := by
    apply Finset.Subset.antisymm
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun h ↦ ha₀NotFace (h ▸ hv),
        hfaceSigma₀ hv⟩
    · intro v hv
      have hvData := Finset.mem_erase.mp hv
      by_contra hvFace
      have hvDiff : v ∈ sigma₀ \ face :=
        Finset.mem_sdiff.mpr ⟨hvData.2, hvFace⟩
      rw [hdiff₀] at hvDiff
      exact hvData.1 (by simpa using hvDiff)
  have hfaceCoord : ∀ v ∈ face, (v.1 k).val = 0 := by
    intro v hv
    change v ∈ rho.image (insertZeroPoint k) at hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact congrArg Fin.val (insertZeroPoint_apply_self k w)
  have hfacePrefix : ∀ v ∈ face,
      pointPrefix v right = pointPrefix v left := by
    intro v hv
    change v ∈ rho.image (insertZeroPoint k) at hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    simpa [k, left, right] using
      pointPrefix_insertZeroPoint_interior_eq q w
  have ha₀CoordNe : (a₀.1 k).val ≠ 0 := by
    intro haZero
    apply hsigma₀.not_all_coord_zero hN k
    intro v hv
    by_cases hva : v = a₀
    · simpa [hva] using haZero
    · apply hfaceCoord v
      rw [hfaceErase₀]
      exact Finset.mem_erase.mpr ⟨hva, hv⟩
  have ha₀Strict : pointPrefix a₀ left < pointPrefix a₀ right := by
    have hcoord := pointPrefix_succ_eq_prev_add_coord a₀ q
    have hpos : 0 < (a₀.1 k).val := by omega
    have hindex : q.succ.castSucc = k := by
      apply Fin.ext
      rfl
    rw [hindex] at hcoord
    change pointPrefix a₀ q.castSucc < pointPrefix a₀ q.succ
    omega
  obtain ⟨u, huRanks⟩ := hsigma₀.image_cumulativeWeight_pointPrefix
  let z : ℤ := cumulativeWeight u
  let m : ℤ := weight a₀
  have hmBlock : m ∈ consecutiveRanks z (n + 1) := by
    rw [← huRanks]
    exact Finset.mem_image.mpr ⟨a₀, ha₀Sigma, rfl⟩
  have hRerase : face.image weight =
      (consecutiveRanks z (n + 1)).erase m := by
    have himageErase : face.image weight =
        (sigma₀.image weight).erase (weight a₀) := by
      ext w
      constructor
      · intro hw
        obtain ⟨v, hvFace, rfl⟩ := Finset.mem_image.mp hw
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_image.mpr
          ⟨v, hfaceSigma₀ hvFace, rfl⟩⟩
        intro hvWeight
        have hva : v = a₀ :=
          hsigma₀.cumulativeWeight_pointPrefix_injective
            (hfaceSigma₀ hvFace) ha₀Sigma hvWeight
        exact ha₀NotFace (hva ▸ hvFace)
      · intro hw
        have hwData := Finset.mem_erase.mp hw
        obtain ⟨v, hvSigma, hvWeight⟩ := Finset.mem_image.mp hwData.2
        apply Finset.mem_image.mpr
        refine ⟨v, ?_, hvWeight⟩
        rw [hfaceErase₀]
        apply Finset.mem_erase.mpr
        refine ⟨?_, hvSigma⟩
        intro hva
        subst v
        exact hwData.1 hvWeight.symm
    rw [himageErase, huRanks]
  have hcardR : (face.image weight).card = n + 1 := by
    rw [Finset.card_image_of_injOn]
    · exact hfaceCard
    · intro a ha b hb hab
      exact hsigma₀.cumulativeWeight_pointPrefix_injective
        (hfaceSigma₀ ha) (hfaceSigma₀ hb) hab
  have hmLower : z < m := by
    have hmBounds := bounds_of_mem_consecutiveRanks hmBlock
    by_contra hnot
    have hmEq : m = z := by omega
    have hyRank : z + n + 1 ∈ face.image weight := by
      rw [hRerase]
      exact Finset.mem_erase.mpr ⟨by omega,
        mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)⟩
    obtain ⟨y, hyFace, hyWeight⟩ := Finset.mem_image.mp hyRank
    have hExtreme :=
      hsigma₀.pointPrefix_eq_add_one_of_weight_distance
        ha₀Sigma (hfaceSigma₀ hyFace) (by
          change weight y = weight a₀ + (n + 1)
          omega)
    have hyEq := hfacePrefix y hyFace
    have hleftEq := congrFun hExtreme left
    have hrightEq := congrFun hExtreme right
    simp only [Pi.add_apply, Pi.one_apply] at hleftEq hrightEq
    omega
  have hmUpper : m < z + n + 1 := by
    have hmBounds := bounds_of_mem_consecutiveRanks hmBlock
    by_contra hnot
    have hmEq : m = z + n + 1 := by omega
    have hxRank : z ∈ face.image weight := by
      rw [hRerase]
      exact Finset.mem_erase.mpr ⟨by omega,
        mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)⟩
    obtain ⟨x, hxFace, hxWeight⟩ := Finset.mem_image.mp hxRank
    have hExtreme :=
      hsigma₀.pointPrefix_eq_add_one_of_weight_distance
        (hfaceSigma₀ hxFace) ha₀Sigma (by
          change weight a₀ = weight x + (n + 1)
          omega)
    have hxEq := hfacePrefix x hxFace
    have hleftEq := congrFun hExtreme left
    have hrightEq := congrFun hExtreme right
    simp only [Pi.add_apply, Pi.one_apply] at hleftEq hrightEq
    omega
  have hxRank : m - 1 ∈ face.image weight := by
    rw [hRerase]
    exact Finset.mem_erase.mpr ⟨by omega,
      mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)⟩
  have hyRank : m + 1 ∈ face.image weight := by
    rw [hRerase]
    exact Finset.mem_erase.mpr ⟨by omega,
      mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)⟩
  obtain ⟨x, hxFace, hxWeight⟩ := Finset.mem_image.mp hxRank
  obtain ⟨y, hyFace, hyWeight⟩ := Finset.mem_image.mp hyRank
  have hxPrefixEq := hfacePrefix x hxFace
  have offVertexData : ∀ tau, tau ∈ C →
      ∃ b : Point N (n + 1),
        tau \ face = {b} ∧ b ∈ tau ∧ weight b = m ∧
          pointPrefix b = pointPrefix x + Pi.single right 1 := by
    intro tau htauC
    have htauData := Finset.mem_filter.mp htauC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hdiffCard := card_sdiff_codimFace_of_topSimplex
      hfaceCard htauTop htauData.2
    obtain ⟨b, hdiff⟩ := Finset.card_eq_one.mp hdiffCard
    have hbDiff : b ∈ tau \ face := by rw [hdiff]; simp
    have hbTau := (Finset.mem_sdiff.mp hbDiff).1
    have hbNotFace := (Finset.mem_sdiff.mp hbDiff).2
    obtain ⟨w, hwRanks⟩ := htauTop.image_cumulativeWeight_pointPrefix
    have hRw : face.image weight ⊆
        consecutiveRanks (cumulativeWeight w) (n + 1) := by
      rw [← hwRanks]
      exact Finset.image_mono _ htauData.2
    have hbW : weight b ∈
        consecutiveRanks (cumulativeWeight w) (n + 1) := by
      rw [← hwRanks]
      exact Finset.mem_image.mpr ⟨b, hbTau, rfl⟩
    have hbNotImage : weight b ∉ face.image weight := by
      intro hbImage
      obtain ⟨v, hvFace, hvWeight⟩ := Finset.mem_image.mp hbImage
      have hbv : b = v := htauTop.cumulativeWeight_pointPrefix_injective
        hbTau (htauData.2 hvFace) hvWeight.symm
      exact hbNotFace (hbv ▸ hvFace)
    have hbCases := completion_rank_cases (Nat.succ_pos n) hcardR
      hmBlock hRerase hRw hbW hbNotImage
    have hbWeight : weight b = m := by
      rcases hbCases with hsame | hfirst | hlast
      · exact hsame
      · omega
      · omega
    have hfaceErase : face = tau.erase b := by
      apply Finset.Subset.antisymm
      · intro v hv
        exact Finset.mem_erase.mpr ⟨fun h ↦ hbNotFace (h ▸ hv),
          htauData.2 hv⟩
      · intro v hv
        have hvData := Finset.mem_erase.mp hv
        by_contra hvFace
        have hvDiff : v ∈ tau \ face :=
          Finset.mem_sdiff.mpr ⟨hvData.2, hvFace⟩
        rw [hdiff] at hvDiff
        exact hvData.1 (by simpa using hvDiff)
    have hbCoordNe : (b.1 k).val ≠ 0 := by
      intro hbZero
      apply htauTop.not_all_coord_zero hN k
      intro v hv
      by_cases hvb : v = b
      · simpa [hvb] using hbZero
      · apply hfaceCoord v
        rw [hfaceErase]
        exact Finset.mem_erase.mpr ⟨hvb, hv⟩
    have hbStrict : pointPrefix b left < pointPrefix b right := by
      have hcoord := pointPrefix_succ_eq_prev_add_coord b q
      have hpos : 0 < (b.1 k).val := by omega
      have hindex : q.succ.castSucc = k := by
        apply Fin.ext
        rfl
      rw [hindex] at hcoord
      change pointPrefix b q.castSucc < pointPrefix b q.succ
      omega
    have hxb : pointPrefix x ≤ pointPrefix b :=
      htauTop.pointPrefix_le_of_weight_le (htauData.2 hxFace) hbTau
        (by change weight x ≤ weight b; omega)
    have hstepWeight : cumulativeWeight (pointPrefix b) =
        cumulativeWeight (pointPrefix x) + 1 := by
      change weight b = weight x + 1
      omega
    have hpos := positiveCoords_nonempty_of_le_of_weight_add_one
      hxb hstepWeight
    obtain ⟨i, hiPos⟩ := hpos
    have hbAdd := eq_add_single_of_le_of_weight_add_one
      hxb hstepWeight (Finset.mem_filter.mp hiPos).2
    have hiRight : i = right := by
      by_contra hir
      have hbRight : pointPrefix b right = pointPrefix x right := by
        rw [hbAdd]
        simp [hir]
      have hbLeftGe : pointPrefix x left ≤ pointPrefix b left := hxb left
      omega
    refine ⟨b, hdiff, hbTau, hbWeight, ?_⟩
    simpa [hiRight] using hbAdd
  have hCsubsingleton : C.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro tau sigma htauC hsigmaC
    obtain ⟨a, hdiffTau, _, _, haPrefix⟩ := offVertexData tau htauC
    obtain ⟨b, hdiffSigma, _, _, hbPrefix⟩ :=
      offVertexData sigma hsigmaC
    have hab : a = b := pointPrefix_injective (haPrefix.trans hbPrefix.symm)
    exact sdiff_injective_on_cofacets htauC hsigmaC (by
      change tau \ face = sigma \ face
      rw [hdiffTau, hdiffSigma, hab])
  have hCnonempty : C.Nonempty := ⟨sigma₀, hsigma₀C⟩
  change C.card = 1
  exact Nat.le_antisymm hCsubsingleton (Finset.one_le_card.mpr hCnonempty)

/-- Every actual codimension-one simplex contained in a coordinate face has
exactly one ambient Freudenthal cofacet.  The proof first lowers the face to
a genuine lower-dimensional top simplex and then dispatches to the first,
interior, or last coordinate calculation above. -/
theorem coordinateFace_cofacets_card_eq_one
    {N n : ℕ} (hN : 0 < N)
    {rho : Finset (Point N (n + 1))}
    (hrho : rho ∈ freudenthalComplex N (n + 1))
    (hcard : rho.card = n + 1)
    {k : Fin (n + 2)} (hk : k ∈ commonZeroCoordinates rho) :
    ((freudenthalFacets N (n + 1)).filter fun tau ↦ rho ⊆ tau).card = 1 := by
  have hkzero : ∀ a ∈ rho, (a.1 k).val = 0 :=
    (mem_commonZeroCoordinates_iff rho k).1 hk
  let sigma : Finset (ZeroFacePoint (N := N) k) :=
    bundleZeroFaceSimplex k rho
  have himage : sigma.image Subtype.val = rho :=
    image_bundleZeroFaceSimplex k rho hkzero
  have hsigmaFace : sigma ∈ freudenthalCoordinateFaceComplex N n k :=
    (mem_freudenthalCoordinateFaceComplex_iff k sigma).2 (by
      rw [himage]
      exact hrho)
  have hsigmaLower : sigma ∈ lowerFreudenthalRelabeledToFace N n k := by
    rw [lowerFreudenthalRelabeledToFace_eq_coordinateFace hN]
    exact hsigmaFace
  obtain ⟨tau, htau, htauImage⟩ :=
    (FiniteSimplicialComplex.mem_relabel_iff
      (freudenthalComplex N n) (zeroFaceEquiv k) sigma).1
      hsigmaLower
  have hsigmaCard : sigma.card = rho.card := by
    rw [← Finset.card_image_of_injective sigma Subtype.val_injective,
      himage]
  have htauCard : tau.card = n + 1 := by
    rw [← Finset.card_image_of_injective tau
      (zeroFaceEquiv k).injective, htauImage, hsigmaCard, hcard]
  have htauTop : IsFreudenthalTopSimplex tau := by
    apply (mem_freudenthalFacets_iff tau).1
    rw [freudenthalFacets_eq_topSimplices]
    exact Finset.mem_filter.mpr ⟨htau, htauCard⟩
  have htauAmbient : tau.image (insertZeroPoint k) = rho := by
    calc
      tau.image (insertZeroPoint k) =
          (tau.image (zeroFaceEquiv k)).image Subtype.val := by
        rw [Finset.image_image]
        rfl
      _ = sigma.image Subtype.val := by rw [htauImage]
      _ = rho := himage
  rw [← htauAmbient]
  refine Fin.cases ?_ ?_ k
  · exact zeroFace_cofacets_card_eq_one hN htauTop
  · intro d
    rcases Fin.eq_castSucc_or_eq_last d with ⟨q, rfl⟩ | rfl
    · exact interiorFace_cofacets_card_eq_one hN q htauTop
    · simpa using lastFace_cofacets_card_eq_one hN htauTop

/-! ## Local alternate completions away from the coordinate boundary -/

/-- Recovering original coordinates from the cumulative coordinates of an
actual point gives its literal coordinate vector. -/
theorem pointCoords_eq_gammaCoords_pointPrefix {N d : ℕ}
    (a : Point N d) :
    pointCoords a = gammaCoords (N : ℤ) (pointPrefix a) := by
  apply prefixMap_injective_on_sum
    (pointCoords_isPoint a).2 (sum_gammaCoords (pointPrefix a))
  rw [pointPrefix, prefixMap_gammaCoords]

/-- Equality of two successive cumulative coordinates is exactly vanishing
of the intervening original coordinate. -/
theorem point_coord_succ_eq_zero_of_prefix_eq
    {N n : ℕ} (a : Point N (n + 1)) (q : Fin n)
    (h : pointPrefix a q.succ = pointPrefix a q.castSucc) :
    (a.1 q.succ.castSucc).val = 0 := by
  have hcoord := pointPrefix_succ_eq_prev_add_coord a q
  omega

/-- Vanishing of the first cumulative coordinate is vanishing of the first
original coordinate. -/
theorem point_coord_zero_eq_zero_of_prefix_zero
    {N d : ℕ} (a : Point N (d + 1))
    (h : pointPrefix a (0 : Fin (d + 1)) = 0) :
    (a.1 (0 : Fin (d + 2))).val = 0 := by
  have hz : pointCoords a (0 : Fin (d + 2)) = 0 := by
    simpa [pointPrefix] using h
  have hz' : ((a.1 (0 : Fin (d + 2))).val : ℤ) = 0 := by
    simpa [pointCoords] using hz
  omega

/-- If the last cumulative coordinate has reached the total mass, the last
original coordinate vanishes. -/
theorem point_coord_last_eq_zero_of_prefix_last
    {N d : ℕ} (a : Point N (d + 1))
    (h : pointPrefix a (Fin.last d) = N) :
    (a.1 (Fin.last (d + 1))).val = 0 := by
  have hcoords := pointCoords_eq_gammaCoords_pointPrefix a
  have hlast := congrFun hcoords (Fin.last (d + 1))
  rw [gammaCoords_apply_last] at hlast
  have hz : pointCoords a (Fin.last (d + 1)) = 0 := by omega
  have hz' : ((a.1 (Fin.last (d + 1))).val : ℤ) = 0 := by
    simpa [pointCoords] using hz
  omega

/-- Every endpoint of an initial list segment occurs in the full
Freudenthal sequence. -/
theorem freudenthalEndpoint_take_mem_sequence {d : ℕ}
    (u : Fin d → ℤ) (l : List (Fin d)) (r : ℕ) :
    freudenthalEndpoint u (l.take r) ∈ freudenthalSequence u l := by
  have hmem : freudenthalEndpoint u (l.take r) ∈
      freudenthalSequence u (l.take r ++ l.drop r) := by
    rw [freudenthalSequence_append]
    exact List.mem_append_left _
      (freudenthalEndpoint_mem_sequence u (l.take r))
  simpa only [List.take_append_drop] using hmem

/-- A vertex of rank `r` in a duplicate-free cumulative path is the endpoint
after the first `r` transfers. -/
theorem eq_freudenthalEndpoint_take_of_rank
    {d : ℕ} {u : Fin d → ℤ} {l : List (Fin d)}
    {y : Fin d → ℤ} (hy : y ∈ freudenthalSequence u l)
    {r : ℕ} (hr : r ≤ l.length)
    (hweight : cumulativeWeight y = cumulativeWeight u + r) :
    y = freudenthalEndpoint u (l.take r) := by
  apply cumulativeWeight_injective_on_freudenthalSequence u l hy
    (freudenthalEndpoint_take_mem_sequence u l r)
  rw [cumulativeWeight_freudenthalEndpoint, List.length_take, min_eq_left hr]
  exact hweight

/-- Rotating the first transfer to the end gives the facet across the first
rank face, provided its one new endpoint remains in `Gamma`. -/
theorem facetAdjacent_realize_rotate_first
    {N d : ℕ} (u : Fin d → ℤ) (i : Fin d) (s : List (Fin d))
    (hl : (i :: s).Nodup) (hlen : (i :: s).length = d)
    (hGamma : ∀ z ∈ freudenthalSimplex u (i :: s),
      IsGammaPoint (N : ℤ) z)
    (hnew : IsGammaPoint (N : ℤ)
      (freudenthalEndpoint (u + Pi.single i 1) s + Pi.single i 1)) :
    FacetChain.Adjacent (freudenthalFacets N d) d
      (realizeGammaSet N d (freudenthalSimplex u (i :: s)))
      (realizeGammaSet N d
        (freudenthalSimplex (u + Pi.single i 1) (s ++ [i]))) := by
  let v := u + Pi.single i 1
  let A := freudenthalSimplex v s
  let x := u
  let y := freudenthalEndpoint v s + Pi.single i 1
  let R := freudenthalSimplex u (i :: s)
  let S := freudenthalSimplex v (s ++ [i])
  have hR : R = insert x A := by
    exact freudenthalSimplex_cons u i s
  have hS : S = insert y A := by
    exact freudenthalSimplex_append_single v s i
  have hsNodup : s.Nodup := (List.nodup_cons.mp hl).2
  have hsLen : s.length + 1 = d := by simpa using hlen
  have hAcard : A.card = d := by
    rw [card_freudenthalSimplex_of_nodup v hsNodup]
    omega
  have hxA : x ∉ A := by
    intro hxA
    have hvLe := freudenthalSequence_base_le_of_mem v s
      (by simpa [A, freudenthalSimplex] using hxA)
    have hi := hvLe i
    simp [v, x] at hi
  have hyA : y ∉ A := by
    intro hyA
    obtain ⟨r, hr, hrWeight⟩ := exists_rank_of_mem_freudenthalSequence
      v s (by simpa [A, freudenthalSimplex] using hyA)
    have hyWeight : cumulativeWeight y =
        cumulativeWeight v + s.length + 1 := by
      change cumulativeWeight
        (freudenthalEndpoint v s + Pi.single i 1) = _
      rw [cumulativeWeight_add_single,
        cumulativeWeight_freudenthalEndpoint]
    omega
  have hxy : x ≠ y := by
    intro hxy
    have hyWeight : cumulativeWeight y =
        cumulativeWeight v + s.length + 1 := by
      change cumulativeWeight
        (freudenthalEndpoint v s + Pi.single i 1) = _
      rw [cumulativeWeight_add_single,
        cumulativeWeight_freudenthalEndpoint]
    have hvWeight : cumulativeWeight v = cumulativeWeight x + 1 := by
      change cumulativeWeight (u + Pi.single i 1) =
        cumulativeWeight u + 1
      rw [cumulativeWeight_add_single]
    rw [← hxy] at hyWeight
    omega
  have hGammaA : ∀ z ∈ A, IsGammaPoint (N : ℤ) z := by
    intro z hz
    apply hGamma z
    rw [freudenthalSimplex_cons]
    exact Finset.mem_insert_of_mem hz
  have hGammaS : ∀ z ∈ S, IsGammaPoint (N : ℤ) z := by
    intro z hz
    rw [hS] at hz
    rcases Finset.mem_insert.mp hz with rfl | hzA
    · exact hnew
    · exact hGammaA z hzA
  have htopR : IsFreudenthalTopSimplex (realizeGammaSet N d R) := by
    exact isFreudenthalTopSimplex_realizeGammaList u (i :: s)
      hl hlen (by simpa [R] using hGamma)
  have hperm : (i :: s).Perm (s ++ [i]) := by
    simpa using (List.perm_append_comm (l₁ := [i]) (l₂ := s))
  have htopS : IsFreudenthalTopSimplex (realizeGammaSet N d S) := by
    apply isFreudenthalTopSimplex_realizeGammaList v (s ++ [i])
      (hperm.nodup_iff.mp hl) (hperm.length_eq.symm.trans hlen)
    simpa [S] using hGammaS
  have hInter : (R ∩ S).card = d := by
    have hRS : R ∩ S = A := by
      rw [hR, hS]
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨(rfl | hzA), (hEq | hxMem)⟩
        · exact (hxy hEq).elim
        · exact (hxA hxMem).elim
        · exact hzA
        · exact hzA
      · intro hzA
        exact ⟨Or.inr hzA, Or.inr hzA⟩
    rw [hRS, hAcard]
  apply facetAdjacent_of_cumulative_images htopR htopS
    (image_pointPrefix_realizeGammaSet R (by
      intro z hz
      apply hGamma z
      simpa [R] using hz))
    (image_pointPrefix_realizeGammaSet S hGammaS)
  · rw [hR, hS]
    intro hrs
    have hxRight : x ∈ insert y A := by rw [← hrs]; simp
    simp [hxy, hxA] at hxRight
  · exact hInter

/-- Moving the last transfer to the front of the decreased base gives the
facet across the last-rank face, provided the decreased base lies in
`Gamma`. -/
theorem facetAdjacent_realize_decrease_last
    {N d : ℕ} (u : Fin d → ℤ) (p : List (Fin d)) (i : Fin d)
    (hl : (p ++ [i]).Nodup) (hlen : (p ++ [i]).length = d)
    (hGamma : ∀ z ∈ freudenthalSimplex u (p ++ [i]),
      IsGammaPoint (N : ℤ) z)
    (hbase : IsGammaPoint (N : ℤ) (u - Pi.single i 1)) :
    FacetChain.Adjacent (freudenthalFacets N d) d
      (realizeGammaSet N d (freudenthalSimplex u (p ++ [i])))
      (realizeGammaSet N d
        (freudenthalSimplex (u - Pi.single i 1) (i :: p))) := by
  let u' := u - Pi.single i 1
  let A := freudenthalSimplex u p
  let x := freudenthalEndpoint u p + Pi.single i 1
  let R := freudenthalSimplex u (p ++ [i])
  let S := freudenthalSimplex u' (i :: p)
  have huRestore : u' + Pi.single i 1 = u := sub_single_add_single u i
  have hR : R = insert x A := freudenthalSimplex_append_single u p i
  have hS : S = insert u' A := by
    rw [show S = freudenthalSimplex u' (i :: p) by rfl,
      freudenthalSimplex_cons, huRestore]
  have hpNodup : p.Nodup := (List.nodup_append.mp hl).1
  have hpLen : p.length + 1 = d := by simpa using hlen
  have hAcard : A.card = d := by
    rw [card_freudenthalSimplex_of_nodup u hpNodup]
    omega
  have hxA : x ∉ A := by
    intro hxA
    obtain ⟨r, hr, hrWeight⟩ := exists_rank_of_mem_freudenthalSequence
      u p (by simpa [A, freudenthalSimplex] using hxA)
    have hxWeight : cumulativeWeight x =
        cumulativeWeight u + p.length + 1 := by
      change cumulativeWeight
        (freudenthalEndpoint u p + Pi.single i 1) = _
      rw [cumulativeWeight_add_single,
        cumulativeWeight_freudenthalEndpoint]
    omega
  have hu'NotA : u' ∉ A := by
    intro hu'A
    have hbaseLe := freudenthalSequence_base_le_of_mem u p
      (by simpa [A, freudenthalSimplex] using hu'A)
    have hi := hbaseLe i
    simp [u'] at hi
  have hxu' : x ≠ u' := by
    intro h
    have hxWeight : cumulativeWeight x =
        cumulativeWeight u + p.length + 1 := by
      change cumulativeWeight
        (freudenthalEndpoint u p + Pi.single i 1) = _
      rw [cumulativeWeight_add_single,
        cumulativeWeight_freudenthalEndpoint]
    have hu'Weight := cumulativeWeight_sub_single u i
    rw [h] at hxWeight
    change cumulativeWeight u' = cumulativeWeight u - 1 at hu'Weight
    omega
  have hGammaA : ∀ z ∈ A, IsGammaPoint (N : ℤ) z := by
    intro z hz
    apply hGamma z
    rw [freudenthalSimplex_append_single]
    exact Finset.mem_insert_of_mem hz
  have hGammaS : ∀ z ∈ S, IsGammaPoint (N : ℤ) z := by
    intro z hz
    rw [hS] at hz
    rcases Finset.mem_insert.mp hz with rfl | hzA
    · exact hbase
    · exact hGammaA z hzA
  have htopR : IsFreudenthalTopSimplex (realizeGammaSet N d R) :=
    isFreudenthalTopSimplex_realizeGammaList u (p ++ [i])
      hl hlen (by simpa [R] using hGamma)
  have hperm : (p ++ [i]).Perm (i :: p) := by
    simp
  have htopS : IsFreudenthalTopSimplex (realizeGammaSet N d S) := by
    apply isFreudenthalTopSimplex_realizeGammaList u' (i :: p)
      (hperm.nodup_iff.mp hl) (hperm.length_eq.symm.trans hlen)
    simpa [S] using hGammaS
  have hInter : (R ∩ S).card = d := by
    have hRS : R ∩ S = A := by
      rw [hR, hS]
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨(rfl | hzA), (hEq | hxMem)⟩
        · exact (hxu' hEq).elim
        · exact (hxA hxMem).elim
        · exact hzA
        · exact hzA
      · intro hzA
        exact ⟨Or.inr hzA, Or.inr hzA⟩
    rw [hRS, hAcard]
  apply facetAdjacent_of_cumulative_images htopR htopS
    (image_pointPrefix_realizeGammaSet R (by
      intro z hz
      apply hGamma z
      simpa [R] using hz))
    (image_pointPrefix_realizeGammaSet S hGammaS)
  · rw [hR, hS]
    intro hrs
    have hxRight : x ∈ insert u' A := by rw [← hrs]; simp
    simp [hxu', hxA] at hxRight
  · exact hInter

/-- A duplicate-free list of all `d` directions contains every direction. -/
theorem mem_of_nodup_length_eq_fin {d : ℕ} {l : List (Fin d)}
    (hl : l.Nodup) (hlen : l.length = d) (i : Fin d) : i ∈ l := by
  have hcard : l.toFinset.card = Fintype.card (Fin d) := by
    rw [List.toFinset_card_of_nodup hl, hlen]
    simp
  have huniv : l.toFinset = Finset.univ :=
    Finset.eq_univ_of_card l.toFinset hcard
  simp [← List.mem_toFinset, huniv]

/-- Exact criterion for decreasing one cumulative coordinate while staying
inside `Gamma`. -/
theorem isGammaPoint_sub_single_iff {N : ℤ} {d : ℕ}
    {u : Fin d → ℤ} (hu : IsGammaPoint N u) (i : Fin d) :
    IsGammaPoint N (u - Pi.single i 1) ↔
      0 < u i ∧ ∀ j, j < i → u j < u i := by
  constructor
  · intro h
    constructor
    · have hi := h.1 i
      simp at hi
      omega
    · intro j hji
      have hjiNe : j ≠ i := hji.ne
      have hmono := h.2.1 j i hji.le
      simp [hjiNe] at hmono
      omega
  · rintro ⟨hiPos, hiLeft⟩
    constructor
    · intro j
      simp only [Pi.sub_apply, Pi.single_apply]
      by_cases hji : j = i
      · subst j
        simp
        omega
      · simp [hji, hu.1 j]
    constructor
    · intro a b hab
      simp only [Pi.sub_apply, Pi.single_apply]
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · simp [hbi]
        · have hmono := hu.2.1 i b hab
          simp [hbi]
          omega
      · by_cases hbi : b = i
        · subst b
          simp [hai]
          by_cases haiLt : a < i
          · have := hiLeft a haiLt
            omega
          · have haiEq : a = i := le_antisymm hab (Fin.not_lt.mp haiLt)
            exact (hai haiEq).elim
        · simp [hai, hbi]
          exact hu.2.1 a b hab
    · intro j
      simp only [Pi.sub_apply, Pi.single_apply]
      by_cases hji : j = i
      · subst j
        simp
        have := hu.2.2 i
        omega
      · simpa [hji] using hu.2.2 j

/-- A codimension-one Freudenthal simplex with no common zero coordinate is
an interior face and therefore has exactly two cofacets.  The three cases
are the erased base vertex, erased final vertex, and erased intermediate
vertex of a concrete permutation path. -/
theorem cofacets_card_eq_two_of_commonZeroCoordinates_eq_empty
    {N n : ℕ} {rho : Finset (Point N (n + 1))}
    (hrho : rho ∈ freudenthalComplex N (n + 1))
    (hcard : rho.card = n + 1)
    (hzero : commonZeroCoordinates rho = ∅) :
    ((freudenthalFacets N (n + 1)).filter fun tau ↦ rho ⊆ tau).card = 2 := by
  let d := n + 1
  let C := (freudenthalFacets N d).filter fun tau ↦ rho ⊆ tau
  have hNoZero : ∀ k : Fin (d + 1),
      ¬∀ a ∈ rho, (a.1 k).val = 0 := by
    intro k hk
    have : k ∈ commonZeroCoordinates rho :=
      (mem_commonZeroCoordinates_iff rho k).2 hk
    rw [hzero] at this
    simp at this
  have hrhoNonempty : rho.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨sigma, hsigmaTop, hrhoSigma⟩ :
      ∃ sigma, IsFreudenthalTopSimplex sigma ∧ rho ⊆ sigma := by
    rcases (mem_freudenthalComplex_iff rho).1 hrho with hEmpty | htop
    · exact (hrhoNonempty.ne_empty hEmpty).elim
    · exact htop
  have hsigmaFacet : sigma ∈ freudenthalFacets N d :=
    (mem_freudenthalFacets_iff sigma).2 hsigmaTop
  have hsigmaC : sigma ∈ C := Finset.mem_filter.mpr
    ⟨hsigmaFacet, hrhoSigma⟩
  have hdiffCard := card_sdiff_codimFace_of_topSimplex
    hcard hsigmaTop hrhoSigma
  obtain ⟨a, hdiff⟩ := Finset.card_eq_one.mp hdiffCard
  have haDiff : a ∈ sigma \ rho := by rw [hdiff]; simp
  have haSigma := (Finset.mem_sdiff.mp haDiff).1
  have haNotRho := (Finset.mem_sdiff.mp haDiff).2
  have hrhoErase : rho = sigma.erase a := by
    apply Finset.Subset.antisymm
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun h ↦ haNotRho (h ▸ hv),
        hrhoSigma hv⟩
    · intro v hv
      have hvData := Finset.mem_erase.mp hv
      by_contra hvRho
      have hvDiff : v ∈ sigma \ rho :=
        Finset.mem_sdiff.mpr ⟨hvData.2, hvRho⟩
      rw [hdiff] at hvDiff
      exact hvData.1 (by simpa using hvDiff)
  obtain ⟨u, l, hl, hlen, hGamma, hsigmaEq⟩ :=
    exists_valid_realization_of_topSimplex hsigmaTop
  have hlenD : l.length = d := by simpa [d] using hlen
  let S := freudenthalSimplex u l
  have haReal : a ∈ realizeGammaSet N d S := by
    simpa [d, S, hsigmaEq] using haSigma
  have haPrefixS : pointPrefix a ∈ S :=
    (Finset.mem_filter.mp haReal).2
  have haSeq : pointPrefix a ∈ freudenthalSequence u l := by
    simpa [S, freudenthalSimplex] using haPrefixS
  obtain ⟨r, hr, hrWeight⟩ :=
    exists_rank_of_mem_freudenthalSequence u l haSeq
  have hrD : r ≤ d := by omega
  have haRankEq : pointPrefix a = freudenthalEndpoint u (l.take r) :=
    eq_freudenthalEndpoint_take_of_rank haSeq hr hrWeight
  have hpointPrefixOfRho : ∀ v ∈ rho,
      pointPrefix v ∈ S ∧ pointPrefix v ≠ pointPrefix a := by
    intro v hv
    have hvSigma := hrhoSigma hv
    have hvReal : v ∈ realizeGammaSet N d S := by
      simpa [d, S, hsigmaEq] using hvSigma
    refine ⟨(Finset.mem_filter.mp hvReal).2, ?_⟩
    intro h
    exact haNotRho ((pointPrefix_injective h.symm) ▸ hv)
  have finish (alt : Finset (Point N d))
      (hadj : FacetChain.Adjacent (freudenthalFacets N d) d sigma alt)
      (hrhoAlt : rho ⊆ alt) : C.card = 2 := by
    have haltC : alt ∈ C := Finset.mem_filter.mpr ⟨hadj.2.1, hrhoAlt⟩
    have hpair : ({sigma, alt} : Finset (Finset (Point N d))) ⊆ C := by
      intro tau htau
      simp only [Finset.mem_insert, Finset.mem_singleton] at htau
      rcases htau with rfl | rfl
      · exact hsigmaC
      · exact haltC
    have hlower := Finset.card_le_card hpair
    have hne : sigma ≠ alt := hadj.2.2.1
    have hlower' : 2 ≤ C.card := by simpa [hne] using hlower
    have hupper : C.card ≤ 2 := by
      exact freudenthalFacets_nonbranching (N := N) (n := d)
        (by simp [d]) rho (by simpa [d] using hcard)
    exact Nat.le_antisymm hupper hlower'
  by_cases hrZero : r = 0
  · subst r
    have haBase : pointPrefix a = u := by simpa using haRankEq
    have hlNe : l ≠ [] := by
      intro hlNil
      rw [hlNil] at hlenD
      simp [d] at hlenD
    obtain ⟨i, s, rfl⟩ := List.exists_cons_of_ne_nil hlNe
    have hsNodup : s.Nodup := (List.nodup_cons.mp hl).2
    have hiNotS : i ∉ s := (List.nodup_cons.mp hl).1
    let v := u + Pi.single i 1
    let t := freudenthalEndpoint v s
    let A := freudenthalSimplex v s
    have hvGamma : IsGammaPoint (N : ℤ) v := by
      apply hGamma v
      rw [freudenthalSimplex_cons]
      exact Finset.mem_insert_of_mem (freudenthalBase_mem_simplex v s)
    have htGamma : IsGammaPoint (N : ℤ) t := by
      apply hGamma t
      rw [freudenthalSimplex_cons]
      exact Finset.mem_insert_of_mem (freudenthalEndpoint_mem_simplex v s)
    have hall : ∀ j : Fin d, j ∈ i :: s :=
      mem_of_nodup_length_eq_fin hl hlenD
    have hnew : IsGammaPoint (N : ℤ) (t + Pi.single i 1) := by
      rw [isGammaPoint_add_single_iff htGamma i]
      constructor
      · by_contra hiUpper
        have hti : t i = N := by
          have := htGamma.2.2 i
          omega
        have hiLast : i = Fin.last n := by
          by_contra hiNeLast
          have hiLt : i < Fin.last n :=
            lt_of_le_of_ne (Fin.le_last i) hiNeLast
          let j : Fin d := ⟨i.val + 1, by
            change i.val + 1 < n + 1
            have hiVal : i.val < n := by
              change i.val < n at hiLt
              exact hiLt
            omega⟩
          have hij : i < j := by
            change i.val < i.val + 1
            omega
          have hjMem : j ∈ s := by
            have hjAll := hall j
            simp only [List.mem_cons] at hjAll
            rcases hjAll with hji | hjs
            · have := congrArg Fin.val hji
              simp [j] at this
            · exact hjs
          have htiEndpoint := freudenthalEndpoint_apply_of_nodup
            v hsNodup i
          have htjEndpoint := freudenthalEndpoint_apply_of_nodup
            v hsNodup j
          have hvMono := hvGamma.2.1 i j hij.le
          have htiEq : t i = v i := by
            change freudenthalEndpoint v s i = v i
            simpa [hiNotS] using htiEndpoint
          have htjEq : t j = v j + 1 := by
            change freudenthalEndpoint v s j = v j + 1
            simpa [hjMem] using htjEndpoint
          have htjUpper := htGamma.2.2 j
          omega
        apply hNoZero (Fin.last d)
        intro b hb
        have hbData := hpointPrefixOfRho b hb
        have hbA : pointPrefix b ∈ A := by
          rw [show S = insert u A by
            simpa [S, A, v] using freudenthalSimplex_cons u i s] at hbData
          rcases Finset.mem_insert.mp hbData.1 with hbu | hbA
          · exact (hbData.2 (hbu.trans haBase.symm)).elim
          · exact hbA
        have hbSeq : pointPrefix b ∈ freudenthalSequence v s := by
          simpa [A, freudenthalSimplex] using hbA
        have hbi := freudenthalSequence_coordinate_eq_of_not_mem
          v s hiNotS hbSeq
        have htiEndpoint := freudenthalEndpoint_apply_of_nodup
          v hsNodup i
        have htiEq : t i = v i := by
          change freudenthalEndpoint v s i = v i
          simpa [hiNotS] using htiEndpoint
        have hvi : v i = N := by omega
        have hbLastPrefix : pointPrefix b (Fin.last n) = N := by
          rw [hiLast] at hbi hvi
          omega
        exact point_coord_last_eq_zero_of_prefix_last b hbLastPrefix
      · intro j hij
        have hjMem : j ∈ s := by
          have hjAll := hall j
          simpa [hij.ne'] using hjAll
        have htiEndpoint := freudenthalEndpoint_apply_of_nodup
          v hsNodup i
        have htjEndpoint := freudenthalEndpoint_apply_of_nodup
          v hsNodup j
        have hvMono := hvGamma.2.1 i j hij.le
        have htiEq : t i = v i := by
          change freudenthalEndpoint v s i = v i
          simpa [hiNotS] using htiEndpoint
        have htjEq : t j = v j + 1 := by
          change freudenthalEndpoint v s j = v j + 1
          simpa [hjMem] using htjEndpoint
        omega
    let alt : Finset (Point N d) :=
      realizeGammaSet N d (freudenthalSimplex v (s ++ [i]))
    have hadj : FacetChain.Adjacent (freudenthalFacets N d) d sigma alt := by
      have h := facetAdjacent_realize_rotate_first u i s hl hlenD
        hGamma hnew
      simpa [alt, v, S, hsigmaEq] using h
    have hrhoAlt : rho ⊆ alt := by
      intro b hb
      have hbData := hpointPrefixOfRho b hb
      have hbA : pointPrefix b ∈ A := by
        rw [show S = insert u A by
          simpa [S, A, v] using freudenthalSimplex_cons u i s] at hbData
        rcases Finset.mem_insert.mp hbData.1 with hbu | hbA
        · exact (hbData.2 (hbu.trans haBase.symm)).elim
        · exact hbA
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [freudenthalSimplex_append_single]
      exact Finset.mem_insert_of_mem hbA
    exact finish alt hadj hrhoAlt
  · by_cases hrLast : r = d
    · have hlNe : l ≠ [] := by
        intro hlNil
        rw [hlNil] at hlenD
        simp [d] at hlenD
      rcases List.eq_nil_or_concat l with hlNil | ⟨p, i, hlEq⟩
      · exact (hlNe hlNil).elim
      · subst l
        have haLast : pointPrefix a =
            freudenthalEndpoint u (p ++ [i]) := by
          rw [hrLast, ← hlenD, List.take_length] at haRankEq
          simpa only [List.concat_eq_append] using haRankEq
        rw [List.concat_eq_append] at hl hlenD hGamma
        have hpNodup : p.Nodup := (List.nodup_append.mp hl).1
        have hiNotP : i ∉ p := by
          have hdata := List.nodup_append.mp hl
          intro hi
          exact hdata.2.2 i hi i (by simp) rfl
        let x := freudenthalEndpoint u p + Pi.single i 1
        let A := freudenthalSimplex u p
        have hxEq : x = freudenthalEndpoint u (p ++ [i]) := by
          rw [freudenthalEndpoint, List.foldl_append]
          rfl
        have haX : pointPrefix a = x := haLast.trans hxEq.symm
        have huGamma : IsGammaPoint (N : ℤ) u := by
          apply hGamma u
          exact freudenthalBase_mem_simplex u (p ++ [i])
        have hxGamma : IsGammaPoint (N : ℤ) x := by
          apply hGamma x
          rw [show x = freudenthalEndpoint u (p ++ [i]) by exact hxEq]
          exact freudenthalEndpoint_mem_simplex u (p ++ [i])
        have hall : ∀ j : Fin d, j ∈ p ++ [i] :=
          mem_of_nodup_length_eq_fin hl hlenD
        have hiLeft : ∀ j, j < i → u j < u i := by
          intro j hji
          have hjMem : j ∈ p := by
            have hjAll := hall j
            simp only [List.mem_append, List.mem_singleton] at hjAll
            rcases hjAll with hjp | hjiEq
            · exact hjp
            · exact (hji.ne hjiEq).elim
          have hxj := freudenthalEndpoint_apply_of_nodup
            u hpNodup j
          have hxi := freudenthalEndpoint_apply_of_nodup
            u hpNodup i
          have heGamma : IsGammaPoint (N : ℤ)
              (freudenthalEndpoint u p) := by
            apply hGamma (freudenthalEndpoint u p)
            rw [freudenthalSimplex_append_single]
            exact Finset.mem_insert_of_mem
              (freudenthalEndpoint_mem_simplex u p)
          have heMono := heGamma.2.1 j i hji.le
          simp [hjMem, hiNotP] at hxj hxi
          omega
        have hiPos : 0 < u i := by
          by_cases hiZero : i = 0
          · subst i
            by_contra hnot
            have hui : u (0 : Fin d) = 0 := by
              have := huGamma.1 (0 : Fin d)
              omega
            apply hNoZero (0 : Fin (d + 1))
            intro b hb
            have hbData := hpointPrefixOfRho b hb
            have hbA : pointPrefix b ∈ A := by
              rw [show S = insert x A by
                simpa [S, A, x] using
                  freudenthalSimplex_append_single u p (0 : Fin d)]
                at hbData
              rcases Finset.mem_insert.mp hbData.1 with hbx | hbA
              · exact (hbData.2 (hbx.trans haX.symm)).elim
              · exact hbA
            have hbSeq : pointPrefix b ∈ freudenthalSequence u p := by
              simpa [A, freudenthalSimplex] using hbA
            have hb0 := freudenthalSequence_coordinate_eq_of_not_mem
              u p hiNotP hbSeq
            have hbPrefixZero : pointPrefix b (0 : Fin d) = 0 := by
              simpa [hui] using hb0
            exact point_coord_zero_eq_zero_of_prefix_zero b hbPrefixZero
          · have hiVal : 0 < i.val := Fin.pos_iff_ne_zero.mpr hiZero
            let j : Fin d := ⟨i.val - 1, by omega⟩
            have hji : j < i := by
              change i.val - 1 < i.val
              omega
            have := hiLeft j hji
            have := huGamma.1 j
            omega
        have hbase : IsGammaPoint (N : ℤ) (u - Pi.single i 1) :=
          (isGammaPoint_sub_single_iff huGamma i).2 ⟨hiPos, hiLeft⟩
        let alt : Finset (Point N d) :=
          realizeGammaSet N d
            (freudenthalSimplex (u - Pi.single i 1) (i :: p))
        have hadj : FacetChain.Adjacent
            (freudenthalFacets N d) d sigma alt := by
          have h := facetAdjacent_realize_decrease_last u p i hl hlenD
            hGamma hbase
          simpa [alt, S, hsigmaEq] using h
        have hrhoAlt : rho ⊆ alt := by
          intro b hb
          have hbData := hpointPrefixOfRho b hb
          have hbA : pointPrefix b ∈ A := by
            rw [show S = insert x A by
              simpa [S, A, x] using
                freudenthalSimplex_append_single u p i] at hbData
            rcases Finset.mem_insert.mp hbData.1 with hbx | hbA
            · exact (hbData.2 (hbx.trans haX.symm)).elim
            · exact hbA
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [freudenthalSimplex_cons, sub_single_add_single]
          exact Finset.mem_insert_of_mem hbA
        exact finish alt hadj hrhoAlt
    · have hrPos : 0 < r := Nat.pos_of_ne_zero hrZero
      have hrLt : r < l.length := by omega
      have hrPredLt : r - 1 < l.length := by omega
      let p := l.take (r - 1)
      let i : Fin d := l[r - 1]
      let j : Fin d := l[r]
      let s := l.drop (r + 1)
      have hlEq : l = p ++ i :: j :: s := by
        rw [← List.take_append_drop (r - 1) l]
        rw [List.drop_eq_getElem_cons hrPredLt]
        have hrEq : r - 1 + 1 = r := by omega
        rw [hrEq, List.drop_eq_getElem_cons hrLt]
      have hlPath : (p ++ i :: j :: s).Nodup := by
        simpa [hlEq] using hl
      have hlenPath : (p ++ i :: j :: s).length = d := by
        simpa [hlEq] using hlenD
      have hGammaPath : ∀ z ∈ freudenthalSimplex u (p ++ i :: j :: s),
          IsGammaPoint (N : ℤ) z := by
        simpa [hlEq] using hGamma
      have haSeqPath : pointPrefix a ∈
          freudenthalSequence u (p ++ i :: j :: s) := by
        simpa [hlEq] using haSeq
      have hij : i ≠ j := by
        intro hij
        have htail := (List.nodup_append.mp hlPath).2.1
        apply (List.nodup_cons.mp htail).1
        rw [hij]
        exact List.mem_cons_self
      let e := freudenthalEndpoint u p
      let x := e + Pi.single i 1
      let w := e + Pi.single i 1 + Pi.single j 1
      let A := freudenthalSimplex u p
      let B := freudenthalSimplex w s
      have hxMem : x ∈ freudenthalSimplex u (p ++ i :: j :: s) := by
        rw [freudenthalSimplex_pair_decomposition]
        exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      have hxSeq : x ∈ freudenthalSequence u (p ++ i :: j :: s) := by
        simpa [freudenthalSimplex] using hxMem
      have hxWeight : cumulativeWeight x = cumulativeWeight u + r := by
        change cumulativeWeight
          (freudenthalEndpoint u p + Pi.single i 1) = _
        rw [cumulativeWeight_add_single,
          cumulativeWeight_freudenthalEndpoint]
        have hpLen : p.length = r - 1 := by
          simp [p, List.length_take, hrPredLt.le]
        omega
      have haX : pointPrefix a = x :=
        cumulativeWeight_injective_on_freudenthalSequence u
          (p ++ i :: j :: s) haSeqPath hxSeq (hrWeight.trans hxWeight.symm)
      have heGamma : IsGammaPoint (N : ℤ) e := by
        apply hGammaPath e
        rw [freudenthalSimplex_pair_decomposition]
        exact Finset.mem_union_left _
          (freudenthalEndpoint_mem_simplex u p)
      have hwGamma : IsGammaPoint (N : ℤ) w := by
        apply hGammaPath w
        rw [freudenthalSimplex_pair_decomposition]
        exact Finset.mem_union_right _
          (Finset.mem_insert_of_mem (freudenthalBase_mem_simplex w s))
      have hnew : IsGammaPoint (N : ℤ) (e + Pi.single j 1) := by
        apply isGammaPoint_add_single_swap heGamma hij hwGamma
        intro hji
        by_contra hstrict
        have hej : e j = e i := by
          have hle := heGamma.2.1 j i hji.le
          omega
        have hAdjVal : i.val = j.val + 1 := by
          by_contra hgap
          have hgap' : j.val + 1 < i.val := by omega
          let qmid : Fin d := ⟨j.val + 1, by omega⟩
          have hjq : j < qmid := by
            change j.val < j.val + 1
            omega
          have hqi : qmid < i := hgap'
          have hejq := heGamma.2.1 j qmid hjq.le
          have heqi := heGamma.2.1 qmid i hqi.le
          have hqNeI : qmid ≠ i := hqi.ne
          have hqNeJ : qmid ≠ j := hjq.ne'
          have hwMono := hwGamma.2.1 j qmid hjq.le
          change w j ≤ w qmid at hwMono
          simp [w, hij.symm, hqNeI, hqNeJ] at hwMono
          omega
        have hjNeLast : j ≠ Fin.last n := by
          intro hjLast
          have hjVal := congrArg Fin.val hjLast
          have hiLt := i.isLt
          simp [d, Fin.val_last] at hjVal hiLt
          omega
        obtain ⟨q, hqCast⟩ := Fin.eq_castSucc_of_ne_last hjNeLast
        have hiSucc : i = q.succ := by
          apply Fin.ext
          have hqVal := congrArg Fin.val hqCast
          simp at hqVal ⊢
          omega
        apply hNoZero q.succ.castSucc
        intro b hb
        have hbData := hpointPrefixOfRho b hb
        have hbShared : pointPrefix b ∈ A ∨ pointPrefix b ∈ B := by
          rw [show S = A ∪ insert x B by
            simpa [S, hlEq, A, B, x, w, e] using
              freudenthalSimplex_pair_decomposition u p s i j]
            at hbData
          rcases Finset.mem_union.mp hbData.1 with hbA | hbRest
          · exact Or.inl hbA
          · rcases Finset.mem_insert.mp hbRest with hbx | hbB
            · exact (hbData.2 (hbx.trans haX.symm)).elim
            · exact Or.inr hbB
        have hiNotP : i ∉ p := by
          have hdata := List.nodup_append.mp hlPath
          exact fun hiP ↦ hdata.2.2 i hiP i (by simp) rfl
        have hjNotP : j ∉ p := by
          have hdata := List.nodup_append.mp hlPath
          exact fun hjP ↦ hdata.2.2 j hjP j (by simp) rfl
        have hiNotS : i ∉ s := by
          have htail := (List.nodup_append.mp hlPath).2.1
          intro hiS
          exact (List.nodup_cons.mp htail).1 (by simp [hiS])
        have hjNotS : j ∉ s := by
          have htail := (List.nodup_append.mp hlPath).2.1
          exact (List.nodup_cons.mp (List.nodup_cons.mp htail).2).1
        have hbEq : pointPrefix b i = pointPrefix b j := by
          rcases hbShared with hbA | hbB
          · have hbSeq : pointPrefix b ∈ freudenthalSequence u p := by
              simpa [A, freudenthalSimplex] using hbA
            have hbi := freudenthalSequence_coordinate_eq_of_not_mem
              u p hiNotP hbSeq
            have hbj := freudenthalSequence_coordinate_eq_of_not_mem
              u p hjNotP hbSeq
            have hei := freudenthalEndpoint_coordinate_eq_of_not_mem
              u p hiNotP
            have hej' := freudenthalEndpoint_coordinate_eq_of_not_mem
              u p hjNotP
            change freudenthalEndpoint u p j =
              freudenthalEndpoint u p i at hej
            omega
          · have hbSeq : pointPrefix b ∈ freudenthalSequence w s := by
              simpa [B, freudenthalSimplex] using hbB
            have hbi := freudenthalSequence_coordinate_eq_of_not_mem
              w s hiNotS hbSeq
            have hbj := freudenthalSequence_coordinate_eq_of_not_mem
              w s hjNotS hbSeq
            have hwEq : w j = w i := by
              simp [w, hij, hej]
            omega
        rw [← hqCast, hiSucc] at hbEq
        exact point_coord_succ_eq_zero_of_prefix_eq b q hbEq
      let alt : Finset (Point N d) :=
        realizeGammaSet N d
          (freudenthalSimplex u (p ++ j :: i :: s))
      have hadj : FacetChain.Adjacent
          (freudenthalFacets N d) d sigma alt := by
        have h := facetAdjacent_realize_adjacent_swap u p s i j
          hlPath hlenPath hGammaPath hij hnew
        simpa [alt, S, hlEq, hsigmaEq] using h
      have hrhoAlt : rho ⊆ alt := by
        intro b hb
        have hbData := hpointPrefixOfRho b hb
        have hbShared : pointPrefix b ∈ A ∨ pointPrefix b ∈ B := by
          rw [show S = A ∪ insert x B by
            simpa [S, hlEq, A, B, x, w, e] using
              freudenthalSimplex_pair_decomposition u p s i j]
            at hbData
          rcases Finset.mem_union.mp hbData.1 with hbA | hbRest
          · exact Or.inl hbA
          · rcases Finset.mem_insert.mp hbRest with hbx | hbB
            · exact (hbData.2 (hbx.trans haX.symm)).elim
            · exact Or.inr hbB
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [freudenthalSimplex_pair_decomposition,
          ← add_single_add_single_comm e i j]
        rcases hbShared with hbA | hbB
        · exact Finset.mem_union_left _ hbA
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hbB)
      exact finish alt hadj hrhoAlt

/-- Exact local incidence parity at positive scale: a coordinate-boundary
face has one cofacet and one common zero coordinate, while every other face
has two cofacets and no common zero coordinate. -/
theorem freudenthalBoundaryIncidenceParity_of_pos
    {N n : ℕ} (hN : 0 < N) :
    FreudenthalBoundaryIncidenceParity N n := by
  intro rho hrho hcard
  by_cases hzero : commonZeroCoordinates rho = ∅
  · have hcofaces :=
      cofacets_card_eq_two_of_commonZeroCoordinates_eq_empty
        hrho hcard hzero
    rw [hcofaces, hzero]
    change (2 : ZMod 2) = 0
    exact ZMod.natCast_self 2
  · have hzeroNonempty : (commonZeroCoordinates rho).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hzero
    obtain ⟨k, hk⟩ := hzeroNonempty
    have hcofaces := coordinateFace_cofacets_card_eq_one
      hN hrho hcard hk
    have hzeroLe := commonZeroCoordinates_card_le_one hN hrho hcard
    have hzeroCard : (commonZeroCoordinates rho).card = 1 :=
      Nat.le_antisymm hzeroLe (Finset.one_le_card.mpr ⟨k, hk⟩)
    rw [hcofaces, hzeroCard]

/-- Formula (19) is equivalent to the explicit local incidence-parity
classification above.  In particular, no geometric content is hidden in the
definition of the coordinate-face chains. -/
theorem boundary_freudenthalTopChain_eq_sum_coordinateFaces_iff
    (N n : ℕ) :
    SimplexFamily.boundary (freudenthalTopChain N (n + 1)) =
        ∑ k : Fin (n + 2), freudenthalCoordinateFaceChain N n k ↔
      FreudenthalBoundaryIncidenceParity N n := by
  constructor
  · intro h rho hrho hcard
    have hcoeff := congrArg (fun c ↦ c rho) h
    rw [boundary_freudenthalTopChain_apply,
      sum_freudenthalCoordinateFaceChains_apply,
      if_pos hcard, if_pos ⟨hrho, hcard⟩] at hcoeff
    exact hcoeff
  · intro hparity
    ext rho
    rw [boundary_freudenthalTopChain_apply,
      sum_freudenthalCoordinateFaceChains_apply]
    by_cases hcard : rho.card = n + 1
    · rw [if_pos hcard]
      by_cases hrho : rho ∈ freudenthalComplex N (n + 1)
      · rw [if_pos ⟨hrho, hcard⟩]
        exact hparity rho hrho hcard
      · rw [if_neg (by exact fun h ↦ hrho h.1),
          freudenthalCofaces_eq_empty_of_not_mem hrho]
        simp
    · rw [if_neg hcard, if_neg (by exact fun h ↦ hcard h.2)]

/-- Equation (19), now proved from the exact codimension-one incidence
classification rather than postulated as a boundary interface. -/
theorem boundary_freudenthalTopChain_eq_sum_coordinateFaces_of_pos
    {N n : ℕ} (hN : 0 < N) :
    SimplexFamily.boundary (freudenthalTopChain N (n + 1)) =
      ∑ k : Fin (n + 2), freudenthalCoordinateFaceChain N n k := by
  exact (boundary_freudenthalTopChain_eq_sum_coordinateFaces_iff N n).2
    (freudenthalBoundaryIncidenceParity_of_pos hN)

/-- The induced Scarf coordinate-face chain is exactly the corresponding
high-dimensional family face chain.  This is an equality of ambient chains,
not just an equality of abstract face complexes. -/
theorem scarfCoordinateFaceChain_eq_associatedFaceTopChain
    (N n : ℕ) (k : Fin (n + 2)) :
    scarfCoordinateFaceChain N n k =
      (pointOrders N (n + 1)).associatedFamily.topChain
        (Finset.univ.erase k) := by
  let K := (pointOrders N (n + 1)).associatedComplex
    (Finset.univ.erase k)
  have hface : ∀ sigma : Finset (Point N (n + 1)), sigma ∈ K →
      ∀ v ∈ sigma, (v.1 k).val = 0 := by
    intro sigma hsigma v hv
    have hcoord := associatedFace_simplex_vertex_coord_zero k hsigma hv
    change (((v.1 k).val : ℕ) : ℤ) = 0 at hcoord
    omega
  calc
    scarfCoordinateFaceChain N n k =
        SimplexFamily.mapChainHom (zeroFaceInclusion k)
          (SimplexFamily.complexCardChain
            (K.inducedOn (fun v ↦ (v.1 k).val = 0)) (n + 1)) := by
      rfl
    _ = SimplexFamily.complexCardChain K (n + 1) :=
      SimplexFamily.mapChainHom_complexCardChain_inducedOn
        K (fun v ↦ (v.1 k).val = 0) (n + 1) hface
    _ = (pointOrders N (n + 1)).associatedFamily.topChain
        (Finset.univ.erase k) := by
      rw [SimplexFamily.topChain_eq_complexCardChain]
      simp [K, IndexedLinearOrders.associatedFamily]

/-- Direct insertion transports the lower Scarf top chain to the ambient
Scarf coordinate-face chain. -/
theorem map_associatedTopChain_eq_scarfCoordinateFaceChain
    (N n : ℕ) (k : Fin (n + 2)) :
    SimplexFamily.mapChainHom (insertZeroPointEmbedding k)
        (associatedTopChain N n) =
      scarfCoordinateFaceChain N n k := by
  let e := zeroFaceEquiv (N := N) k
  let g := zeroFaceInclusion (N := N) k
  let c := SimplexFamily.complexCardChain
    ((pointOrders N n).associatedComplex Finset.univ) (n + 1)
  calc
    SimplexFamily.mapChainHom (insertZeroPointEmbedding k)
        (associatedTopChain N n) =
        SimplexFamily.mapChainHom (e.toEmbedding.trans g) c := by
      rw [associatedTopChain_eq_complexCardChain]
      congr 2
    _ = SimplexFamily.mapChainHom g
        (SimplexFamily.mapChainHom e.toEmbedding c) :=
      (SimplexFamily.mapChainHom_comp e.toEmbedding g c).symm
    _ = SimplexFamily.mapChainHom g
        (SimplexFamily.relabelChainHom e c) := by
      rw [SimplexFamily.mapChainHom_equiv_toEmbedding]
    _ = SimplexFamily.mapChainHom g
        (SimplexFamily.complexCardChain
          (lowerScarfRelabeledToFace N n k) (n + 1)) := by
      rw [SimplexFamily.relabelChainHom_complexCardChain]
      rfl
    _ = scarfCoordinateFaceChain N n k := by
      rw [lowerScarfRelabeledToFace_eq_coordinateFace]
      rfl

/-- At positive scale, direct insertion transports the lower Freudenthal top
chain to the ambient Freudenthal coordinate-face chain. -/
theorem map_freudenthalTopChain_eq_freudenthalCoordinateFaceChain
    {N n : ℕ} (hN : 0 < N) (k : Fin (n + 2)) :
    SimplexFamily.mapChainHom (insertZeroPointEmbedding k)
        (freudenthalTopChain N n) =
      freudenthalCoordinateFaceChain N n k := by
  let e := zeroFaceEquiv (N := N) k
  let g := zeroFaceInclusion (N := N) k
  let c := SimplexFamily.complexCardChain
    (freudenthalComplex N n) (n + 1)
  calc
    SimplexFamily.mapChainHom (insertZeroPointEmbedding k)
        (freudenthalTopChain N n) =
        SimplexFamily.mapChainHom (e.toEmbedding.trans g) c := by
      rw [freudenthalTopChain_eq_complexCardChain]
      congr 2
    _ = SimplexFamily.mapChainHom g
        (SimplexFamily.mapChainHom e.toEmbedding c) :=
      (SimplexFamily.mapChainHom_comp e.toEmbedding g c).symm
    _ = SimplexFamily.mapChainHom g
        (SimplexFamily.relabelChainHom e c) := by
      rw [SimplexFamily.mapChainHom_equiv_toEmbedding]
    _ = SimplexFamily.mapChainHom g
        (SimplexFamily.complexCardChain
          (lowerFreudenthalRelabeledToFace N n k) (n + 1)) := by
      rw [SimplexFamily.relabelChainHom_complexCardChain]
      rfl
    _ = freudenthalCoordinateFaceChain N n k := by
      rw [lowerFreudenthalRelabeledToFace_eq_coordinateFace hN]
      rfl

/-- Chain-level form of equation (21): the induction hypothesis on the lower
full-index chains identifies the high Scarf face chain with the corresponding
Freudenthal coordinate-face chain. -/
theorem associatedFaceTopChain_eq_freudenthalCoordinateFaceChain_of_lower_eq
    {N n : ℕ} (hN : 0 < N) (k : Fin (n + 2))
    (hLower : associatedTopChain N n = freudenthalTopChain N n) :
    (pointOrders N (n + 1)).associatedFamily.topChain
        (Finset.univ.erase k) =
      freudenthalCoordinateFaceChain N n k := by
  rw [← scarfCoordinateFaceChain_eq_associatedFaceTopChain,
    ← map_associatedTopChain_eq_scarfCoordinateFaceChain,
    hLower,
    map_freudenthalTopChain_eq_freudenthalCoordinateFaceChain hN]

/-- Equation (18) specialized to the full index set and with its
codimension-one indices explicitly enumerated by the deleted coordinate. -/
theorem boundary_associatedTopChain_eq_sum_associatedFaces
    (N n : ℕ) :
    SimplexFamily.boundary (associatedTopChain N (n + 1)) =
      ∑ k : Fin (n + 2),
        (pointOrders N (n + 1)).associatedFamily.topChain
          (Finset.univ.erase k) := by
  have hchain :=
    (pointOrders N (n + 1)).associatedFamily_isChainSimplex
      (Finset.univ : Finset (Fin (n + 2)))
  rw [associatedTopChain, hchain, SimplexFamily.boundaryIndexChain,
    boundaryIndices_univ_fin]
  rw [Finset.sum_image
    (univ_erase_injective_fin (m := n + 2)).injOn]

/-- Summed form of equation (21), with every summand living in the same
ambient chain group. -/
theorem sum_associatedFaces_eq_sum_freudenthalCoordinateFaces_of_lower_eq
    {N n : ℕ} (hN : 0 < N)
    (hLower : associatedTopChain N n = freudenthalTopChain N n) :
    (∑ k : Fin (n + 2),
        (pointOrders N (n + 1)).associatedFamily.topChain
          (Finset.univ.erase k)) =
      ∑ k : Fin (n + 2), freudenthalCoordinateFaceChain N n k := by
  apply Finset.sum_congr rfl
  intro k _
  exact associatedFaceTopChain_eq_freudenthalCoordinateFaceChain_of_lower_eq
    hN k hLower

/-- The Scarf side of the inductive boundary comparison, obtained from
equation (18) and the already proved chain-level equation (21).  This theorem
does not itself claim equation (19); the separate Freudenthal boundary
computation is supplied above. -/
theorem boundary_associatedTopChain_eq_sum_freudenthalCoordinateFaces_of_lower_eq
    {N n : ℕ} (hN : 0 < N)
    (hLower : associatedTopChain N n = freudenthalTopChain N n) :
    SimplexFamily.boundary (associatedTopChain N (n + 1)) =
      ∑ k : Fin (n + 2), freudenthalCoordinateFaceChain N n k := by
  rw [boundary_associatedTopChain_eq_sum_associatedFaces,
    sum_associatedFaces_eq_sum_freudenthalCoordinateFaces_of_lower_eq
      hN hLower]

/-! ## Closing the induction in Theorem 4.8 -/

/-- Full chain form of Theorem 4.8 at positive scale.  The successor step
uses equations (18), (21), and the now-proved equation (19), then invokes the
concrete chain-uniqueness theorem with nonbranching, connectivity, and
nonempty boundary already discharged. -/
theorem associatedTopChain_eq_freudenthalTopChain_of_pos
    {N : ℕ} (hN : 0 < N) :
    ∀ n : ℕ, associatedTopChain N n = freudenthalTopChain N n
  | 0 => associatedTopChain_eq_freudenthalTopChain_zero_dim (N := N)
  | n + 1 => by
      have hLower := associatedTopChain_eq_freudenthalTopChain_of_pos hN n
      have hAssociated :=
        boundary_associatedTopChain_eq_sum_freudenthalCoordinateFaces_of_lower_eq
          hN hLower
      have hFreudenthal :=
        boundary_freudenthalTopChain_eq_sum_coordinateFaces_of_pos
          (N := N) (n := n) hN
      have hBoundary :
          SimplexFamily.boundary (associatedTopChain N (n + 1)) =
            SimplexFamily.boundary (freudenthalTopChain N (n + 1)) :=
        hAssociated.trans hFreudenthal.symm
      exact associatedTopChain_eq_freudenthalTopChain_of_boundary_eq_of_pos
        hN (Nat.succ_pos n) hBoundary

/-- Theorem 4.8: at every positive scale the Scarf associated complex for
the full cyclic-order system is exactly the finite Freudenthal complex. -/
theorem associatedComplex_eq_freudenthalComplex_of_pos
    {N n : ℕ} (hN : 0 < N) :
    (pointOrders N n).associatedComplex Finset.univ =
      freudenthalComplex N n := by
  apply associatedComplex_eq_freudenthalComplex_of_topChain_eq
  exact associatedTopChain_eq_freudenthalTopChain_of_pos hN n

/-- The full associated Scarf complex is pure at every positive scale.  This
is the concrete Freudenthal discharge of the purity hypothesis used when the
lower-dimensional solution face in Theorem 10.10 is extended to a top
simplex. -/
theorem associatedComplex_isPureOfCardinality_of_pos
    {N n : ℕ} (hN : 0 < N) :
    ((pointOrders N n).associatedComplex Finset.univ).IsPureOfCardinality
      (n + 1) := by
  rw [associatedComplex_eq_freudenthalComplex_of_pos hN]
  exact freudenthalComplex_isPureOfCardinality_of_pos hN

/-- Every face-family complex `D(C)` embeds in the full associated complex
`D(I)` for the positive-scale cyclic orders.  This is the arbitrary-face
ambient-inclusion obligation used in Theorem 10.10; it is proved by the
iterated coordinate-face theorem and Theorem 4.8, not inferred from the
abstract `SimplexFamily` interface. -/
theorem associatedComplex_subset_full_of_pos
    {N n : ℕ} (hN : 0 < N) (C : Finset (Fin (n + 1)))
    {tau : Finset (Point N n)}
    (htau : tau ∈ (pointOrders N n).associatedComplex C) :
    tau ∈ (pointOrders N n).associatedComplex Finset.univ := by
  rw [associatedComplex_eq_freudenthalComplex_of_pos hN]
  exact associatedComplex_subset_freudenthalComplex_of_pos hN n C htau

/-- Top-dimensional simplices in the associated complex are literally the
full cells.  Combined with Theorem 4.8 this identifies full cells with
Freudenthal facets. -/
theorem isCell_univ_iff_isFreudenthalTopSimplex_of_pos
    {N n : ℕ} (hN : 0 < N) {sigma : Finset (Point N n)} :
    (pointOrders N n).IsCell sigma Finset.univ ↔
      IsFreudenthalTopSimplex sigma := by
  constructor
  · exact isFreudenthalTopSimplex_of_isCell
  · intro hsigmaTop
    have hsigmaMem : sigma ∈
        (pointOrders N n).associatedComplex Finset.univ := by
      rw [associatedComplex_eq_freudenthalComplex_of_pos hN]
      exact hsigmaTop.mem_complex
    have hsigmaAssociated := (Finset.mem_filter.mp hsigmaMem).2
    have huniv : (Finset.univ : Finset (Fin (n + 1))) ≠ ∅ := by
      intro h
      have : (0 : Fin (n + 1)) ∈
          (Finset.univ : Finset (Fin (n + 1))) := Finset.mem_univ _
      rw [h] at this
      simp at this
    rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg huniv]
      at hsigmaAssociated
    rcases hsigmaAssociated with hsigmaEmpty | ⟨tau, htauCell, hsub⟩
    · have hcard := hsigmaTop.card
      rw [hsigmaEmpty] at hcard
      simp at hcard
    · have hsigmaCard := hsigmaTop.card
      have htauCard : tau.card = n + 1 := by
        simpa using htauCell.2
      have heq : sigma = tau :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      simpa [heq] using htauCell

/-- Combinatorial form of Corollary 4.9: the finite set of full `I`-cells is
exactly the facet set of the Freudenthal complex.  The paper's additional
geometric wording about a triangulation of the real simplex is not smuggled
into this finite-complex statement. -/
theorem fullCells_eq_freudenthalFacets_of_pos
    {N n : ℕ} (hN : 0 < N) :
    (Finset.univ.filter fun sigma : Finset (Point N n) ↦
      (pointOrders N n).IsCell sigma Finset.univ) =
        freudenthalFacets N n := by
  ext sigma
  simp [freudenthalFacets,
    isCell_univ_iff_isFreudenthalTopSimplex_of_pos hN]

/-- Corollary 4.10 at positive scale: a subset is a full `I`-cell exactly
when its coordinate image is a permutation step simplex. -/
theorem isCell_univ_iff_exists_stepSimplex_of_pos
    {N n : ℕ} (hN : 0 < N) {sigma : Finset (Point N n)} :
    (pointOrders N n).IsCell sigma Finset.univ ↔
      ∃ a : Point N n, ∃ omega : Equiv.Perm (Fin n),
        sigma.image pointCoords =
          stepSimplex (pointCoords a) (permutationList omega) := by
  rw [isCell_univ_iff_isFreudenthalTopSimplex_of_pos hN]
  rfl

end IntegerSimplex

end BeyondSperner
