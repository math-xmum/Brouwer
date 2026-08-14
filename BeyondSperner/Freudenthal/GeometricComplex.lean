import BeyondSperner.Freudenthal.Realization
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Geometric Freudenthal simplices

This file proves the genuinely geometric obligations behind Corollary 4.9.
The first stage identifies the difference vectors of a Freudenthal path
with a triangular change of the standard basis.  This gives affine
independence rather than merely the correct number of abstract vertices.
-/

namespace BeyondSperner

open Classical
open Set

namespace IntegerSimplex

/-- The `r`-th prefix vector along the coordinate order `omega`.  It has
value one in the first `r + 1` permuted coordinates and zero elsewhere. -/
def realFreudenthalPrefixVector {n : ℕ}
    (omega : Equiv.Perm (Fin n)) (r : Fin n) : Fin n → ℝ :=
  fun i ↦ if omega.symm i ≤ r then 1 else 0

/-- Adjacent differences in the coordinate order `omega`, with the final
coordinate left unchanged.  On prefix vectors this is the inverse
unitriangular operation. -/
def permutedAdjacentDifferenceLinearMap {n : ℕ}
    (omega : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun z q :=
    if hq : Nat.succ q.val < n then
      z (omega q) - z (omega ⟨Nat.succ q.val, hq⟩)
    else z (omega q)
  map_add' y z := by
    funext q
    by_cases hq : Nat.succ q.val < n
    · simp [hq]
      ring
    · simp [hq]
  map_smul' c z := by
    funext q
    by_cases hq : Nat.succ q.val < n
    · simp [hq]
      ring
    · simp [hq]

/-- Adjacent differences send a cumulative prefix vector to the
corresponding standard basis vector. -/
theorem permutedAdjacentDifferenceLinearMap_prefixVector {n : ℕ}
    (omega : Equiv.Perm (Fin n)) (r : Fin n) :
    permutedAdjacentDifferenceLinearMap omega
        (realFreudenthalPrefixVector omega r) =
      Pi.single r 1 := by
  funext q
  simp only [permutedAdjacentDifferenceLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hnext : Nat.succ q.val < n
  · rw [dif_pos hnext]
    simp only [realFreudenthalPrefixVector,
      Equiv.symm_apply_apply, Pi.single_apply]
    by_cases hne : q = r
    · subst r
      have hnot : ¬(⟨Nat.succ q.val, hnext⟩ : Fin n) ≤ q := by
        simp [Fin.le_iff_val_le_val]
      rw [if_pos le_rfl, if_neg hnot, if_pos rfl]
      norm_num
    · rcases lt_or_gt_of_ne hne with hqr | hrq
      · have hsuccle : (⟨Nat.succ q.val, hnext⟩ : Fin n) ≤ r := by
          exact Fin.le_iff_val_le_val.mpr hqr
        rw [if_pos hqr.le, if_pos hsuccle,
          if_neg hne]
        norm_num
      · have hnq : ¬q ≤ r := not_le_of_gt hrq
        have hnsucc : ¬(⟨Nat.succ q.val, hnext⟩ : Fin n) ≤ r := by
          intro h
          exact hnq (Fin.le_iff_val_le_val.mpr
            ((Nat.le_succ q.val).trans
              (Fin.le_iff_val_le_val.mp h)))
        rw [if_neg hnq, if_neg hnsucc,
          if_neg hne]
        norm_num
  · rw [dif_neg hnext]
    simp only [realFreudenthalPrefixVector,
      Equiv.symm_apply_apply, Pi.single_apply]
    by_cases hne : q = r
    · subst r
      rw [if_pos le_rfl, if_pos rfl]
    · have hrq : r < q := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exfalso
          have : Nat.succ q.val < n :=
            lt_of_le_of_lt hlt (r.isLt)
          exact hnext this
        · exact hgt
      rw [if_neg (not_le_of_gt hrq), if_neg hne]

/-- The cumulative prefix vectors are linearly independent.  This is the
nondegeneracy calculation for a Freudenthal top simplex. -/
theorem linearIndependent_realFreudenthalPrefixVector {n : ℕ}
    (omega : Equiv.Perm (Fin n)) :
    LinearIndependent ℝ (realFreudenthalPrefixVector omega) := by
  apply LinearIndependent.of_comp
    (permutedAdjacentDifferenceLinearMap omega)
  have hbasis : LinearIndependent ℝ
      (fun r : Fin n ↦ Pi.single r (1 : ℝ)) := by
    have heq : (fun r : Fin n ↦ Pi.single r (1 : ℝ)) =
        (Pi.basisFun ℝ (Fin n) : Fin n → (Fin n → ℝ)) := by
      funext r i
      simp [Pi.basisFun_apply]
    rw [heq]
    exact (Pi.basisFun ℝ (Fin n)).linearIndependent
  rw [show
    (permutedAdjacentDifferenceLinearMap omega :
        (Fin n → ℝ) → (Fin n → ℝ)) ∘
          realFreudenthalPrefixVector omega =
        (fun r : Fin n ↦ Pi.single r (1 : ℝ)) by
      funext r
      exact permutedAdjacentDifferenceLinearMap_prefixVector omega r]
  exact hbasis

/-- The `k`-th real vertex of a translated Freudenthal path.  Vertex zero
is the base point; vertex `k` has incremented exactly the first `k`
coordinates in the order `omega`. -/
def realFreudenthalPathVertex {n : ℕ} (u : Fin n → ℤ)
    (omega : Equiv.Perm (Fin n)) (k : Fin (n + 1)) : Fin n → ℝ :=
  fun i ↦ (u i : ℝ) +
    if (omega.symm i).val < k.val then 1 else 0

@[simp]
theorem realFreudenthalPathVertex_zero {n : ℕ} (u : Fin n → ℤ)
    (omega : Equiv.Perm (Fin n)) :
    realFreudenthalPathVertex u omega 0 = fun i ↦ (u i : ℝ) := by
  funext i
  simp [realFreudenthalPathVertex]

/-- Differences from the base vertex are precisely the cumulative prefix
vectors proved linearly independent above. -/
theorem realFreudenthalPathVertex_succ_sub_zero {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n)) (r : Fin n) :
    realFreudenthalPathVertex u omega r.succ -
        realFreudenthalPathVertex u omega 0 =
      realFreudenthalPrefixVector omega r := by
  rw [realFreudenthalPathVertex_zero]
  funext i
  simp only [realFreudenthalPathVertex, realFreudenthalPrefixVector,
    Pi.sub_apply, Fin.val_succ]
  have hiff : (omega.symm i).val < r.val + 1 ↔
      omega.symm i ≤ r := by
    rw [Fin.le_iff_val_le_val]
    omega
  by_cases hle : omega.symm i ≤ r
  · rw [if_pos (hiff.mpr hle), if_pos hle]
    ring
  · rw [if_neg (not_congr hiff |>.mpr hle), if_neg hle]
    ring

/-- Nonzero indices of `Fin (n+1)` are canonically equivalent to `Fin n`
by subtracting one. -/
def nonzeroFinSuccEquiv (n : ℕ) :
    {k : Fin (n + 1) // k ≠ 0} ≃ Fin n where
  toFun k := ⟨k.1.val - 1, by
    have hkpos : 0 < k.1.val := Fin.pos_iff_ne_zero.mpr k.2
    omega⟩
  invFun r := ⟨r.succ, by simp⟩
  left_inv k := by
    apply Subtype.ext
    apply Fin.ext
    simp only [Fin.val_succ]
    have hkpos : 0 < k.1.val := Fin.pos_iff_ne_zero.mpr k.2
    omega
  right_inv r := by
    apply Fin.ext
    simp

@[simp]
theorem nonzeroFinSuccEquiv_symm_apply {n : ℕ} (r : Fin n) :
    (nonzeroFinSuccEquiv n).symm r = ⟨r.succ, by simp⟩ := rfl

/-- Every translated-permuted Freudenthal path consists of `n+1`
affinely independent real points. -/
theorem affineIndependent_realFreudenthalPathVertex {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n)) :
    AffineIndependent ℝ (realFreudenthalPathVertex u omega) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ
    (realFreudenthalPathVertex u omega) 0]
  let f : {k : Fin (n + 1) // k ≠ 0} → (Fin n → ℝ) :=
    fun k ↦ realFreudenthalPathVertex u omega k.1 -
      realFreudenthalPathVertex u omega 0
  change LinearIndependent ℝ f
  have hreindex : f ∘ (nonzeroFinSuccEquiv n).symm =
      realFreudenthalPrefixVector omega := by
    funext r
    exact realFreudenthalPathVertex_succ_sub_zero u omega r
  exact (linearIndependent_equiv (nonzeroFinSuccEquiv n).symm).mp
    (hreindex ▸ linearIndependent_realFreudenthalPrefixVector omega)

/-- Integer version of the explicit path vertex. -/
def integerFreudenthalPathVertex {n : ℕ} (u : Fin n → ℤ)
    (omega : Equiv.Perm (Fin n)) (k : Fin (n + 1)) : Fin n → ℤ :=
  fun i ↦ u i + if (omega.symm i).val < k.val then 1 else 0

/-- Membership in an initial segment of `permutationList omega` is exactly
the corresponding rank inequality. -/
theorem mem_take_permutationList_iff {n : ℕ}
    (omega : Equiv.Perm (Fin n)) (q : Fin n) (k : ℕ) :
    q ∈ (permutationList omega).take k ↔
      (omega.symm q).val < k := by
  simp only [permutationList, List.mem_iff_getElem, List.length_take,
    List.length_ofFn, Nat.lt_min, List.getElem_take, List.getElem_ofFn]
  constructor
  · rintro ⟨i, hi, heq⟩
    have heqi : (⟨i, hi.2⟩ : Fin n) = omega.symm q := by
      apply omega.injective
      simpa using heq
    have hval := congrArg Fin.val heqi
    change i = (omega.symm q).val at hval
    omega
  · intro h
    refine ⟨(omega.symm q).val,
      ⟨h, (omega.symm q).isLt⟩, ?_⟩
    simp

/-- The explicit integer formula agrees with the recursively defined
endpoint after the first `k` transfers. -/
theorem integerFreudenthalPathVertex_eq_endpoint_take {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) :
    integerFreudenthalPathVertex u omega k =
      freudenthalEndpoint u ((permutationList omega).take k.val) := by
  funext q
  rw [freudenthalEndpoint_apply_of_nodup u
    ((nodup_permutationList omega).take) q]
  simp only [integerFreudenthalPathVertex]
  by_cases hmem : q ∈ (permutationList omega).take k.val
  · have hlt := (mem_take_permutationList_iff omega q k.val).mp hmem
    rw [if_pos hlt, if_pos hmem]
  · have hnlt := (not_congr
      (mem_take_permutationList_iff omega q k.val)).mp hmem
    rw [if_neg hnlt, if_neg hmem]

/-- The original recursive Freudenthal vertex set is exactly the range of
the explicit rank-indexed path. -/
theorem freudenthalSimplex_eq_image_integerPath {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n)) :
    freudenthalSimplex u (permutationList omega) =
      Finset.univ.image (integerFreudenthalPathVertex u omega) := by
  ext y
  simp only [freudenthalSimplex, List.mem_toFinset,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hy
    obtain ⟨r, hr, hweight⟩ :=
      exists_rank_of_mem_freudenthalSequence
        u (permutationList omega) hy
    have heq := eq_freudenthalEndpoint_take_of_rank
      hy hr hweight
    have hrn : r < n + 1 := by
      rw [length_permutationList] at hr
      omega
    let k : Fin (n + 1) := ⟨r, hrn⟩
    refine ⟨k, ?_⟩
    rw [integerFreudenthalPathVertex_eq_endpoint_take]
    exact heq.symm
  · rintro ⟨k, rfl⟩
    rw [integerFreudenthalPathVertex_eq_endpoint_take]
    exact freudenthalEndpoint_take_mem_sequence
      u (permutationList omega) k.val

/-- Coordinatewise casting of an explicit integer path gives the real path
used in the affine-independence proof. -/
theorem cast_integerFreudenthalPathVertex {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) :
    (fun i ↦ (integerFreudenthalPathVertex u omega k i : ℝ)) =
      realFreudenthalPathVertex u omega k := by
  funext i
  simp only [integerFreudenthalPathVertex,
    realFreudenthalPathVertex]
  split <;> norm_num

/-- Real casting of an integer vector. -/
def integerVectorRealization {n : ℕ} (y : Fin n → ℤ) : Fin n → ℝ :=
  fun i ↦ (y i : ℝ)

/-- A standard Freudenthal top vertex set has an affinely independent real
realization. -/
theorem affineIndependent_image_integerVector_freudenthalSimplex
    {n : ℕ} (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n)) :
    AffineIndependent ℝ
      ((↑) :
        ((freudenthalSimplex u (permutationList omega)).image
          integerVectorRealization : Set (Fin n → ℝ)) →
            (Fin n → ℝ)) := by
  have hfinset :
      (freudenthalSimplex u (permutationList omega)).image
          integerVectorRealization =
        Finset.univ.image (realFreudenthalPathVertex u omega) := by
    rw [freudenthalSimplex_eq_image_integerPath]
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_univ _, ?_⟩
      change realFreudenthalPathVertex u omega k =
        (fun i ↦ (integerFreudenthalPathVertex u omega k i : ℝ))
      exact (cast_integerFreudenthalPathVertex u omega k).symm
    · intro hy
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
      apply Finset.mem_image.mpr
      refine ⟨integerFreudenthalPathVertex u omega k, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
      · change
          (fun i ↦ (integerFreudenthalPathVertex u omega k i : ℝ)) =
            realFreudenthalPathVertex u omega k
        exact cast_integerFreudenthalPathVertex u omega k
  rw [hfinset]
  have hrange :
      ((Finset.univ.image (realFreudenthalPathVertex u omega) :
          Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) =
        Set.range (realFreudenthalPathVertex u omega) := by
    ext y
    simp
  rw [hrange]
  exact (affineIndependent_realFreudenthalPathVertex u omega).range

/-- Realizing a finite set of certified `Gamma` vertices is the same as
first forgetting the certificate and then casting its integer vectors. -/
theorem gammaFaceRealization_eq_image_val_cast {N n : ℕ}
    (rho : Finset (GammaPoint N n)) :
    gammaFaceRealization rho =
      (rho.image Subtype.val).image integerVectorRealization := by
  ext y
  constructor
  · intro hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_image.mpr
    refine ⟨v.1, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
    rfl
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- The real vertex set of a literal `Gamma` top simplex is exactly the
range of its explicit Freudenthal path presentation. -/
theorem IsGammaFreudenthalTopSimplex.realization_eq_image_path
    {N n : ℕ} {rho : Finset (GammaPoint N n)}
    (hrho : IsGammaFreudenthalTopSimplex rho) :
    ∃ u : Fin n → ℤ, ∃ omega : Equiv.Perm (Fin n),
      gammaFaceRealization rho =
        Finset.univ.image (realFreudenthalPathVertex u omega) := by
  obtain ⟨u, omega, heq⟩ := hrho
  refine ⟨u, omega, ?_⟩
  rw [gammaFaceRealization_eq_image_val_cast, heq,
    freudenthalSimplex_eq_image_integerPath]
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    exact (cast_integerFreudenthalPathVertex u omega k).symm
  · intro hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_image.mpr
    refine ⟨integerFreudenthalPathVertex u omega k, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    · exact cast_integerFreudenthalPathVertex u omega k

/-- Every literal `Gamma` Freudenthal top simplex is genuinely affinely
independent in `R^n`. -/
theorem IsGammaFreudenthalTopSimplex.affineIndependent_realization
    {N n : ℕ} {rho : Finset (GammaPoint N n)}
    (hrho : IsGammaFreudenthalTopSimplex rho) :
    AffineIndependent ℝ
      (fun x : (↑(gammaFaceRealization rho) : Set (Fin n → ℝ)) ↦
        (x : Fin n → ℝ)) := by
  obtain ⟨u, omega, heq⟩ := hrho
  rw [gammaFaceRealization_eq_image_val_cast, heq]
  exact affineIndependent_image_integerVector_freudenthalSimplex
    u omega

/-- Every nonempty face of the abstract Freudenthal complex has a genuine
affinely independent realization. -/
theorem IsGammaFreudenthalSimplex.affineIndependent_realization
    {N n : ℕ} {tau : Finset (GammaPoint N n)}
    (htau : IsGammaFreudenthalSimplex tau) (hne : tau.Nonempty) :
    AffineIndependent ℝ
      (fun x : (↑(gammaFaceRealization tau) : Set (Fin n → ℝ)) ↦
        (x : Fin n → ℝ)) := by
  rcases htau with hzero | ⟨rho, hrho, hsub⟩
  · subst tau
    exact (Finset.not_nonempty_empty hne).elim
  · apply hrho.affineIndependent_realization.mono
    exact_mod_cast gammaFaceRealization_mono hsub

/-- Predicate saying that a real finite vertex set is the realization of a
nonempty face of the literal `Gamma` Freudenthal complex. -/
def IsRealizedGammaFreudenthalFace (N n : ℕ)
    (s : Finset (Fin n → ℝ)) : Prop :=
  ∃ tau : Finset (GammaPoint N n),
    IsGammaFreudenthalSimplex tau ∧ tau.Nonempty ∧
      gammaFaceRealization tau = s

/-- The downward-closed realization family before the empty face is
erased.  This is the input expected by `Geometry.SimplicialComplex.ofErase`.
-/
def IsRealizedGammaFreudenthalFaceOrEmpty (N n : ℕ)
    (s : Finset (Fin n → ℝ)) : Prop :=
  ∃ tau : Finset (GammaPoint N n),
    IsGammaFreudenthalSimplex tau ∧ gammaFaceRealization tau = s

theorem IsRealizedGammaFreudenthalFace.nonempty {N n : ℕ}
    {s : Finset (Fin n → ℝ)}
    (hs : IsRealizedGammaFreudenthalFace N n s) : s.Nonempty := by
  obtain ⟨tau, _, htau, rfl⟩ := hs
  exact htau.image gammaVertexRealization

/-- The first defining field of a geometric simplicial complex is now
fully discharged for the realized Freudenthal face family. -/
theorem IsRealizedGammaFreudenthalFace.affineIndependent {N n : ℕ}
    {s : Finset (Fin n → ℝ)}
    (hs : IsRealizedGammaFreudenthalFace N n s) :
    AffineIndependent ℝ
      (fun x : (↑s : Set (Fin n → ℝ)) ↦ (x : Fin n → ℝ)) := by
  obtain ⟨tau, htau, hne, rfl⟩ := hs
  exact htau.affineIndependent_realization hne

/-- Abstract vertices whose real realizations belong to a prescribed
finite real vertex set. -/
noncomputable def gammaFacePreimage (N n : ℕ)
    (s : Finset (Fin n → ℝ)) : Finset (GammaPoint N n) :=
  Finset.univ.filter fun y ↦ gammaVertexRealization y ∈ s

/-- For a set contained in an already realized face, taking the certified
vertex preimage and realizing again recovers the set exactly. -/
theorem gammaFaceRealization_preimage_eq_of_subset {N n : ℕ}
    {s : Finset (Fin n → ℝ)} {tau : Finset (GammaPoint N n)}
    (hsub : s ⊆ gammaFaceRealization tau) :
    gammaFaceRealization (gammaFacePreimage N n s) = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hy).2
  · intro hx
    have hx' := hsub hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx'
    apply Finset.mem_image.mpr
    refine ⟨y, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩, hxy⟩
    simpa [hxy] using hx

/-- Under the same containment hypothesis, no new abstract vertex is
introduced by the preimage construction. -/
theorem gammaFacePreimage_subset_of_subset {N n : ℕ}
    {s : Finset (Fin n → ℝ)} {tau : Finset (GammaPoint N n)}
    (hsub : s ⊆ gammaFaceRealization tau) :
    gammaFacePreimage N n s ⊆ tau := by
  intro y hy
  have hyReal : gammaVertexRealization y ∈ s :=
    (Finset.mem_filter.mp hy).2
  have hyImage := hsub hyReal
  obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hyImage
  have hzy' : z = y := gammaVertexRealization_injective hzy
  simpa [hzy'] using hz

/-- The realized face predicate is genuinely downward closed, not merely
declared to be so. -/
theorem isLowerSet_isRealizedGammaFreudenthalFaceOrEmpty (N n : ℕ) :
    IsLowerSet {s : Finset (Fin n → ℝ) |
      IsRealizedGammaFreudenthalFaceOrEmpty N n s} := by
  intro s t hts hs
  obtain ⟨tau, htau, hsEq⟩ := hs
  let eta := gammaFacePreimage N n t
  have htSub : t ⊆ gammaFaceRealization tau := by
    simpa [hsEq] using hts
  have hetaSub : eta ⊆ tau :=
    gammaFacePreimage_subset_of_subset htSub
  have hetaFace : IsGammaFreudenthalSimplex eta :=
    htau.of_subset hetaSub
  have hetaEq : gammaFaceRealization eta = t :=
    gammaFaceRealization_preimage_eq_of_subset htSub
  exact ⟨eta, hetaFace, hetaEq⟩

/-! ## Convex-hull coordinates of a top simplex -/

/-- Complemented coordinates in the permutation order.  A point lies in
the path simplex exactly when these coordinates lie in the unit monotone
simplex. -/
def orderedComplementCoordinates {n : ℕ} (u : Fin n → ℤ)
    (omega : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun q ↦ 1 - (x (omega q) - (u (omega q) : ℝ))

/-- Closed ordered region associated with a translated-permuted
Freudenthal top simplex. -/
def InRealFreudenthalOrderedRegion {n : ℕ} (u : Fin n → ℤ)
    (omega : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Prop :=
  IsRealGammaPoint 1 (orderedComplementCoordinates u omega x)

/-- Every explicit path vertex lies in its ordered region. -/
theorem realFreudenthalPathVertex_mem_orderedRegion {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) :
    InRealFreudenthalOrderedRegion u omega
      (realFreudenthalPathVertex u omega k) := by
  constructor
  · intro q
    simp only [orderedComplementCoordinates,
      realFreudenthalPathVertex, Equiv.symm_apply_apply]
    split <;> norm_num
  constructor
  · intro q r hqr
    simp only [orderedComplementCoordinates,
      realFreudenthalPathVertex, Equiv.symm_apply_apply]
    by_cases hr : r.val < k.val
    · have hq : q.val < k.val :=
        lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hqr) hr
      rw [if_pos hq, if_pos hr]
      norm_num
    · rw [if_neg hr]
      by_cases hq : q.val < k.val
      · rw [if_pos hq]
        norm_num
      · rw [if_neg hq]
        norm_num
  · intro q
    simp only [orderedComplementCoordinates,
      realFreudenthalPathVertex, Equiv.symm_apply_apply]
    split <;> norm_num

/-- The ordered region is convex. -/
theorem convex_inRealFreudenthalOrderedRegion {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n)) :
    Convex ℝ {x : Fin n → ℝ |
      InRealFreudenthalOrderedRegion u omega x} := by
  intro x hx z hz a b ha hb hab
  have hcoords :
      orderedComplementCoordinates u omega (a • x + b • z) =
        a • orderedComplementCoordinates u omega x +
          b • orderedComplementCoordinates u omega z := by
    funext q
    simp only [orderedComplementCoordinates, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    conv_lhs => rw [← hab]
    have hu : (u (omega q) : ℝ) =
        (a + b) * (u (omega q) : ℝ) := by
      rw [hab, one_mul]
    conv_lhs => rw [hu]
    ring
  change IsRealGammaPoint 1
    (orderedComplementCoordinates u omega (a • x + b • z))
  rw [hcoords]
  exact convex_realGamma 1 n hx hz ha hb hab

/-- The convex hull of the explicit path vertices is contained in the
ordered region. -/
theorem convexHull_realFreudenthalPath_subset_orderedRegion {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n)) :
    convexHull ℝ
        (Set.range (realFreudenthalPathVertex u omega)) ⊆
      {x | InRealFreudenthalOrderedRegion u omega x} := by
  apply convexHull_min
  · rintro x ⟨k, rfl⟩
    exact realFreudenthalPathVertex_mem_orderedRegion u omega k
  · exact convex_inRealFreudenthalOrderedRegion u omega

/-- Tail weights after rank `q` are one minus the corresponding prefix
sum. -/
theorem sum_filter_rank_lt_eq_one_sub_prefix {n : ℕ}
    (w : Fin (n + 1) → ℝ) (hw : ∑ k, w k = 1) (q : Fin n) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) ↦
        q.val < k.val), w k) = 1 - realPrefixMap w q := by
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (n + 1)))
    (fun k : Fin (n + 1) ↦ k.val ≤ q.val) w
  have htail :
      (∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) ↦
          ¬k.val ≤ q.val), w k) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) ↦
          q.val < k.val), w k := by
    apply Finset.sum_congr
    · ext k
      simp
    · intro k _
      rfl
  rw [htail] at hpartition
  unfold realPrefixMap
  linarith

/-- The barycentric weights obtained from the inverse cumulative formula
reconstruct the original point in the ordered region. -/
theorem sum_gammaCoords_smul_realFreudenthalPathVertex {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) :
    let y := orderedComplementCoordinates u omega x
    let w := realGammaCoords 1 y
    (∑ k, w k • realFreudenthalPathVertex u omega k) = x := by
  dsimp only
  funext i
  let q : Fin n := omega.symm i
  have hq : omega q = i := omega.apply_symm_apply i
  have hsum : ∑ k, realGammaCoords 1
      (orderedComplementCoordinates u omega x) k = 1 :=
    sum_realGammaCoords _
  have htail := sum_filter_rank_lt_eq_one_sub_prefix
    (realGammaCoords 1 (orderedComplementCoordinates u omega x))
    hsum q
  rw [realPrefixMap_realGammaCoords] at htail
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    realFreudenthalPathVertex]
  calc
    (∑ k, realGammaCoords 1
          (orderedComplementCoordinates u omega x) k *
        ((u i : ℝ) +
          if (omega.symm i).val < k.val then 1 else 0)) =
      (u i : ℝ) *
          (∑ k, realGammaCoords 1
            (orderedComplementCoordinates u omega x) k) +
        ∑ k ∈ Finset.univ.filter
          (fun k : Fin (n + 1) ↦ q.val < k.val),
          realGammaCoords 1
            (orderedComplementCoordinates u omega x) k := by
      rw [Finset.mul_sum]
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro k _
        ring
      · subst q
        simp [Finset.sum_filter]
    _ = (u i : ℝ) + 1 -
        orderedComplementCoordinates u omega x q := by
      rw [hsum, mul_one, htail]
      ring
    _ = x i := by
      simp only [orderedComplementCoordinates, hq]
      ring

/-- The ordered-region inequalities are also sufficient for convex-hull
membership, using the explicit nonnegative barycentric weights. -/
theorem orderedRegion_subset_convexHull_realFreudenthalPath {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n)) :
    {x | InRealFreudenthalOrderedRegion u omega x} ⊆
      convexHull ℝ (Set.range (realFreudenthalPathVertex u omega)) := by
  intro x hx
  let y := orderedComplementCoordinates u omega x
  let w := realGammaCoords 1 y
  have hwDelta : IsRealDeltaPoint 1 w :=
    realGammaCoords_isRealDeltaPoint zero_le_one hx
  apply mem_convexHull_of_exists_fintype w
    (realFreudenthalPathVertex u omega)
  · exact hwDelta.1
  · exact hwDelta.2
  · intro k
    exact Set.mem_range_self k
  · exact sum_gammaCoords_smul_realFreudenthalPathVertex
      u omega x

/-- Exact half-space description of a Freudenthal top simplex. -/
theorem convexHull_realFreudenthalPath_eq_orderedRegion {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n)) :
    convexHull ℝ (Set.range (realFreudenthalPathVertex u omega)) =
      {x | InRealFreudenthalOrderedRegion u omega x} :=
  Set.Subset.antisymm
    (convexHull_realFreudenthalPath_subset_orderedRegion u omega)
    (orderedRegion_subset_convexHull_realFreudenthalPath u omega)

/-- Canonical barycentric coordinates of a point relative to an explicit
Freudenthal path. -/
def freudenthalPathBarycentricWeight {n : ℕ} (u : Fin n → ℤ)
    (omega : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    Fin (n + 1) → ℝ :=
  realGammaCoords 1 (orderedComplementCoordinates u omega x)

theorem sum_freudenthalPathBarycentricWeight {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) :
    ∑ k, freudenthalPathBarycentricWeight u omega x k = 1 :=
  sum_realGammaCoords _

theorem freudenthalPathBarycentricWeight_nonneg_of_mem {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : InRealFreudenthalOrderedRegion u omega x) :
    ∀ k, 0 ≤ freudenthalPathBarycentricWeight u omega x k := by
  exact (realGammaCoords_isRealDeltaPoint zero_le_one hx).1

theorem sum_barycentricWeight_smul_pathVertex {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) :
    (∑ k, freudenthalPathBarycentricWeight u omega x k •
      realFreudenthalPathVertex u omega k) = x :=
  sum_gammaCoords_smul_realFreudenthalPathVertex u omega x

/-- Affine independence makes the displayed barycentric coordinates the
only coefficients of total mass one that reconstruct the point. -/
theorem freudenthalPathBarycentricWeight_unique {n : ℕ}
    (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (w : Fin (n + 1) → ℝ)
    (hw : ∑ k, w k = 1)
    (hreconstruct :
      (∑ k, w k • realFreudenthalPathVertex u omega k) = x) :
    w = freudenthalPathBarycentricWeight u omega x := by
  funext k
  apply (affineIndependent_realFreudenthalPathVertex u omega).eq_of_sum_eq_sum
    (s := Finset.univ)
  · simpa [sum_freudenthalPathBarycentricWeight] using hw
  · simp [hreconstruct,
      sum_barycentricWeight_smul_pathVertex]
  · exact Finset.mem_univ k

/-- The canonical barycentric coefficient is strictly positive exactly at
the relative interior vertices of the smallest face containing the point.
This elementary support predicate is kept explicit for the intersection
proof. -/
noncomputable def PositiveFreudenthalSupport {n : ℕ} (u : Fin n → ℤ)
    (omega : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter fun k ↦
    0 < freudenthalPathBarycentricWeight u omega x k

theorem positiveSupport_nonempty_of_mem {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : InRealFreudenthalOrderedRegion u omega x) :
    (PositiveFreudenthalSupport u omega x).Nonempty := by
  by_contra hnone
  have hall : ∀ k, freudenthalPathBarycentricWeight u omega x k = 0 := by
    intro k
    have hnpos : ¬0 < freudenthalPathBarycentricWeight u omega x k := by
      intro hk
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hnone
      have hknot : k ∉ PositiveFreudenthalSupport u omega x := by
        rw [hempty]
        simp
      exact hknot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    exact le_antisymm (le_of_not_gt hnpos)
      (freudenthalPathBarycentricWeight_nonneg_of_mem hx k)
  have hsum := sum_freudenthalPathBarycentricWeight u omega x
  simp [hall] at hsum

/-- A point is reconstructed already from its positive-support vertices;
zero coefficients are discarded literally. -/
theorem mem_convexHull_image_positiveSupport {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : InRealFreudenthalOrderedRegion u omega x) :
    x ∈ convexHull ℝ
      (↑((PositiveFreudenthalSupport u omega x).image
        (realFreudenthalPathVertex u omega)) : Set (Fin n → ℝ)) := by
  let support := PositiveFreudenthalSupport u omega x
  let w := freudenthalPathBarycentricWeight u omega x
  apply mem_convexHull_of_exists_fintype
    (ι := support) (fun k : support ↦ w k.1)
    (fun k : support ↦ realFreudenthalPathVertex u omega k.1)
  · intro k
    exact (freudenthalPathBarycentricWeight_nonneg_of_mem hx k.1)
  · calc
      (∑ k : support, w k.1) = ∑ k ∈ support, w k := by
        exact Finset.sum_attach support w
      _ = ∑ k, w k := by
        apply Finset.sum_subset (Finset.subset_univ support)
        intro k _ hk
        have hnpos : ¬0 < w k := by
          exact fun hpos ↦ hk (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hpos⟩)
        exact le_antisymm (le_of_not_gt hnpos)
          (freudenthalPathBarycentricWeight_nonneg_of_mem hx k)
      _ = 1 := sum_freudenthalPathBarycentricWeight u omega x
  · intro k
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨k.1, k.2, rfl⟩)
  · calc
      (∑ k : support, w k.1 •
          realFreudenthalPathVertex u omega k.1) =
        ∑ k ∈ support, w k •
          realFreudenthalPathVertex u omega k := by
            exact Finset.sum_attach support
              (fun k ↦ w k • realFreudenthalPathVertex u omega k)
      _ = ∑ k, w k • realFreudenthalPathVertex u omega k := by
        apply Finset.sum_subset (Finset.subset_univ support)
        intro k _ hk
        have hnpos : ¬0 < w k := by
          exact fun hpos ↦ hk (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hpos⟩)
        have hzero : w k = 0 := le_antisymm (le_of_not_gt hnpos)
          (freudenthalPathBarycentricWeight_nonneg_of_mem hx k)
        simp [hzero]
      _ = x := sum_barycentricWeight_smul_pathVertex u omega x

/-! ## Cell-independent rounded vertices -/

/-- Every coordinate of a point in an ordered Freudenthal region lies
between its integer base coordinate and that coordinate plus one. -/
theorem coordinate_sub_base_mem_Icc_of_orderedRegion {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : InRealFreudenthalOrderedRegion u omega x)
    (i : Fin n) : x i - (u i : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  let q := omega.symm i
  have hq : omega q = i := omega.apply_symm_apply i
  have hyNonneg := hx.1 q
  have hyTop := hx.2.2 q
  simp only [orderedComplementCoordinates, hq] at hyNonneg hyTop
  constructor <;> linarith

/-- Rounding a point at a strict interior threshold, relative to an
integer unit-cube base. -/
noncomputable def interiorRoundedVertex {n : ℕ} (u : Fin n → ℤ)
    (x : Fin n → ℝ) (theta : ℝ) : Fin n → ℤ :=
  fun i ↦ u i + if theta < x i - (u i : ℝ) then 1 else 0

/-- The rounded integer vertex at a threshold in `[0,1)` is independent of
which unit cube containing the point was used.  The endpoint `0` is
included because the comparison itself is strict. -/
theorem interiorRoundedVertex_eq_of_two_bases {n : ℕ}
    {u v : Fin n → ℤ} {x : Fin n → ℝ} {theta : ℝ}
    (htheta : theta ∈ Set.Ico (0 : ℝ) 1)
    (hu : ∀ i, x i - (u i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, x i - (v i : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    interiorRoundedVertex u x theta =
      interiorRoundedVertex v x theta := by
  funext i
  change
    u i + (if theta < x i - (u i : ℝ) then 1 else 0) =
      v i + (if theta < x i - (v i : ℝ) then 1 else 0)
  have hdiffLowerR : (-1 : ℝ) ≤ ((v i - u i : ℤ) : ℝ) := by
    push_cast
    linarith [(hu i).1, (hu i).2, (hv i).1, (hv i).2]
  have hdiffUpperR : ((v i - u i : ℤ) : ℝ) ≤ 1 := by
    push_cast
    linarith [(hu i).1, (hu i).2, (hv i).1, (hv i).2]
  have hdiffLower : (-1 : ℤ) ≤ v i - u i := by
    exact_mod_cast hdiffLowerR
  have hdiffUpper : v i - u i ≤ (1 : ℤ) := by
    exact_mod_cast hdiffUpperR
  have hcases : v i = u i - 1 ∨ v i = u i ∨ v i = u i + 1 := by
    omega
  rcases hcases with hminus | heq | hplus
  · have hxu : x i - (u i : ℝ) = 0 := by
      have := (hv i).2
      rw [hminus] at this
      push_cast at this
      linarith [(hu i).1]
    have hxv : x i - (v i : ℝ) = 1 := by
      rw [hminus]
      push_cast
      linarith
    have hnegU : ¬theta < x i - (u i : ℝ) := by
      linarith [htheta.1, hxu]
    have hposV : theta < x i - (v i : ℝ) := by
      linarith [htheta.2, hxv]
    rw [if_neg hnegU, if_pos hposV, hminus]
    omega
  · simp [heq]
  · have hxu : x i - (u i : ℝ) = 1 := by
      have := (hv i).1
      rw [hplus] at this
      push_cast at this
      linarith [(hu i).2]
    have hxv : x i - (v i : ℝ) = 0 := by
      rw [hplus]
      push_cast
      linarith
    have hposU : theta < x i - (u i : ℝ) := by
      linarith [htheta.2, hxu]
    have hnegV : ¬theta < x i - (v i : ℝ) := by
      linarith [htheta.1, hxv]
    rw [if_pos hposU, if_neg hnegV, hplus]
    omega

/-- Lower-endpoint rounding uses the strict test `0 < x-u`. -/
noncomputable def lowerRoundedVertex {n : ℕ} (u : Fin n → ℤ)
    (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i ↦ u i + if 0 < x i - (u i : ℝ) then 1 else 0

/-- Lower-endpoint rounding is independent of the containing unit cube. -/
theorem lowerRoundedVertex_eq_of_two_bases {n : ℕ}
    {u v : Fin n → ℤ} {x : Fin n → ℝ}
    (hu : ∀ i, x i - (u i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, x i - (v i : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    lowerRoundedVertex u x = lowerRoundedVertex v x := by
  exact interiorRoundedVertex_eq_of_two_bases
    (u := u) (v := v) (x := x) (theta := 0)
      ⟨le_rfl, zero_lt_one⟩ hu hv

/-- Upper-endpoint rounding uses the non-strict test `1 ≤ x-u`. -/
noncomputable def upperRoundedVertex {n : ℕ} (u : Fin n → ℤ)
    (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i ↦ u i + if 1 ≤ x i - (u i : ℝ) then 1 else 0

/-- Rounding with a non-strict threshold in `(0,1]`. -/
noncomputable def closedRoundedVertex {n : ℕ} (u : Fin n → ℤ)
    (x : Fin n → ℝ) (theta : ℝ) : Fin n → ℤ :=
  fun i ↦ u i + if theta ≤ x i - (u i : ℝ) then 1 else 0

/-- Non-strict-threshold rounding is also independent of the containing
unit cube, including the upper endpoint `theta = 1`. -/
theorem closedRoundedVertex_eq_of_two_bases {n : ℕ}
    {u v : Fin n → ℤ} {x : Fin n → ℝ} {theta : ℝ}
    (htheta : theta ∈ Set.Ioc (0 : ℝ) 1)
    (hu : ∀ i, x i - (u i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, x i - (v i : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    closedRoundedVertex u x theta =
      closedRoundedVertex v x theta := by
  funext i
  change
    u i + (if theta ≤ x i - (u i : ℝ) then 1 else 0) =
      v i + (if theta ≤ x i - (v i : ℝ) then 1 else 0)
  have hdiffLowerR : (-1 : ℝ) ≤ ((v i - u i : ℤ) : ℝ) := by
    push_cast
    linarith [(hu i).1, (hu i).2, (hv i).1, (hv i).2]
  have hdiffUpperR : ((v i - u i : ℤ) : ℝ) ≤ 1 := by
    push_cast
    linarith [(hu i).1, (hu i).2, (hv i).1, (hv i).2]
  have hdiffLower : (-1 : ℤ) ≤ v i - u i := by
    exact_mod_cast hdiffLowerR
  have hdiffUpper : v i - u i ≤ (1 : ℤ) := by
    exact_mod_cast hdiffUpperR
  have hcases : v i = u i - 1 ∨ v i = u i ∨ v i = u i + 1 := by
    omega
  rcases hcases with hminus | heq | hplus
  · have hxu : x i - (u i : ℝ) = 0 := by
      have := (hv i).2
      rw [hminus] at this
      push_cast at this
      linarith [(hu i).1]
    have hxv : x i - (v i : ℝ) = 1 := by
      rw [hminus]
      push_cast
      linarith
    have hnegU : ¬theta ≤ x i - (u i : ℝ) := by
      linarith [htheta.1, hxu]
    have hposV : theta ≤ x i - (v i : ℝ) := by
      linarith [htheta.2, hxv]
    rw [if_neg hnegU, if_pos hposV, hminus]
    omega
  · simp [heq]
  · have hxu : x i - (u i : ℝ) = 1 := by
      have := (hv i).1
      rw [hplus] at this
      push_cast at this
      linarith [(hu i).2]
    have hxv : x i - (v i : ℝ) = 0 := by
      rw [hplus]
      push_cast
      linarith
    have hposU : theta ≤ x i - (u i : ℝ) := by
      linarith [htheta.2, hxu]
    have hnegV : ¬theta ≤ x i - (v i : ℝ) := by
      linarith [htheta.1, hxv]
    rw [if_pos hposU, if_neg hnegV, hplus]
    omega

/-- Upper-endpoint rounding is independent of the containing unit cube. -/
theorem upperRoundedVertex_eq_of_two_bases {n : ℕ}
    {u v : Fin n → ℤ} {x : Fin n → ℝ}
    (hu : ∀ i, x i - (u i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, x i - (v i : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    upperRoundedVertex u x = upperRoundedVertex v x := by
  exact closedRoundedVertex_eq_of_two_bases
    (u := u) (v := v) (x := x) (theta := 1)
      ⟨zero_lt_one, le_rfl⟩ hu hv

/-- A lower subset of `Fin n` contains precisely the first `card` indices.
This finite-order lemma turns threshold cuts into a path rank. -/
theorem mem_lowerFinset_iff_val_lt_card {n : ℕ}
    (S : Finset (Fin n))
    (hLower : ∀ ⦃q r : Fin n⦄, q ≤ r → r ∈ S → q ∈ S)
    (q : Fin n) : q ∈ S ↔ q.val < S.card := by
  constructor
  · intro hq
    have hIic : Finset.Iic q ⊆ S := by
      intro r hr
      exact hLower (Finset.mem_Iic.mp hr) hq
    have hcard := Finset.card_le_card hIic
    have hIicCard : (Finset.Iic q).card = q.val + 1 := by simp
    rw [hIicCard] at hcard
    omega
  · intro hqcard
    by_contra hq
    have hsub : S ⊆ Finset.Iio q := by
      intro r hr
      have hrq : r < q := by
        rcases lt_or_ge r q with h | h
        · exact h
        · exact (hq (hLower h hr)).elim
      exact Finset.mem_Iio.mpr hrq
    have hcard := Finset.card_le_card hsub
    have hIioCard : (Finset.Iio q).card = q.val := by simp
    rw [hIioCard] at hcard
    omega

/-- A strict-threshold rounded vertex occurs on every Freudenthal path
whose ordered region contains the point. -/
theorem integerVector_interiorRoundedVertex_mem_path_range {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : InRealFreudenthalOrderedRegion u omega x)
    (theta : ℝ) :
    integerVectorRealization (interiorRoundedVertex u x theta) ∈
      Set.range (realFreudenthalPathVertex u omega) := by
  let S : Finset (Fin n) := Finset.univ.filter fun q ↦
    theta < x (omega q) - (u (omega q) : ℝ)
  have hLower : ∀ ⦃q r : Fin n⦄, q ≤ r → r ∈ S → q ∈ S := by
    intro q r hqr hr
    have hyr := hx.2.1 q r hqr
    simp only [orderedComplementCoordinates] at hyr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hr' := (Finset.mem_filter.mp hr).2
    linarith
  have hcard : S.card < n + 1 := by
    have := Finset.card_le_univ S
    simp only [Fintype.card_fin] at this
    omega
  let k : Fin (n + 1) := ⟨S.card, hcard⟩
  refine ⟨k, ?_⟩
  funext i
  simp only [integerVectorRealization, interiorRoundedVertex,
    realFreudenthalPathVertex]
  have hmem := mem_lowerFinset_iff_val_lt_card S hLower (omega.symm i)
  have hpred : omega.symm i ∈ S ↔
      theta < x i - (u i : ℝ) := by
    simp [S]
  have hiff : (omega.symm i).val < k.val ↔
      theta < x i - (u i : ℝ) := hmem.symm.trans hpred
  by_cases htheta : theta < x i - (u i : ℝ)
  · rw [if_pos htheta, if_pos (hiff.mpr htheta)]
    norm_num
  · rw [if_neg htheta, if_neg (not_congr hiff |>.mpr htheta)]
    norm_num

/-- Lower-endpoint rounding therefore occurs on every containing path. -/
theorem integerVector_lowerRoundedVertex_mem_path_range {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : InRealFreudenthalOrderedRegion u omega x) :
    integerVectorRealization (lowerRoundedVertex u x) ∈
      Set.range (realFreudenthalPathVertex u omega) := by
  exact integerVector_interiorRoundedVertex_mem_path_range hx 0

/-- A non-strict-threshold rounded vertex also occurs on every containing
Freudenthal path. -/
theorem integerVector_closedRoundedVertex_mem_path_range {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : InRealFreudenthalOrderedRegion u omega x)
    (theta : ℝ) :
    integerVectorRealization (closedRoundedVertex u x theta) ∈
      Set.range (realFreudenthalPathVertex u omega) := by
  let S : Finset (Fin n) := Finset.univ.filter fun q ↦
    theta ≤ x (omega q) - (u (omega q) : ℝ)
  have hLower : ∀ ⦃q r : Fin n⦄, q ≤ r → r ∈ S → q ∈ S := by
    intro q r hqr hr
    have hyr := hx.2.1 q r hqr
    simp only [orderedComplementCoordinates] at hyr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hr' := (Finset.mem_filter.mp hr).2
    linarith
  have hcard : S.card < n + 1 := by
    have := Finset.card_le_univ S
    simp only [Fintype.card_fin] at this
    omega
  let k : Fin (n + 1) := ⟨S.card, hcard⟩
  refine ⟨k, ?_⟩
  funext i
  simp only [integerVectorRealization, closedRoundedVertex,
    realFreudenthalPathVertex]
  have hmem := mem_lowerFinset_iff_val_lt_card S hLower (omega.symm i)
  have hpred : omega.symm i ∈ S ↔
      theta ≤ x i - (u i : ℝ) := by
    simp [S]
  have hiff : (omega.symm i).val < k.val ↔
      theta ≤ x i - (u i : ℝ) := hmem.symm.trans hpred
  by_cases htheta : theta ≤ x i - (u i : ℝ)
  · rw [if_pos htheta, if_pos (hiff.mpr htheta)]
    norm_num
  · rw [if_neg htheta, if_neg (not_congr hiff |>.mpr htheta)]
    norm_num

/-- Upper-endpoint rounding occurs on every containing path. -/
theorem integerVector_upperRoundedVertex_mem_path_range {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : InRealFreudenthalOrderedRegion u omega x) :
    integerVectorRealization (upperRoundedVertex u x) ∈
      Set.range (realFreudenthalPathVertex u omega) := by
  exact integerVector_closedRoundedVertex_mem_path_range hx 1

/-- A positive barycentric-support vertex for one Freudenthal cell belongs
to every other Freudenthal path whose closed simplex contains the same
point.  This is the key global compatibility statement behind the
convex-hull intersection axiom. -/
theorem positiveSupport_vertex_mem_other_path {n : ℕ}
    {u v : Fin n → ℤ}
    {omega pi : Equiv.Perm (Fin n)} {x : Fin n → ℝ}
    (hxU : InRealFreudenthalOrderedRegion u omega x)
    (hxV : InRealFreudenthalOrderedRegion v pi x)
    {k : Fin (n + 1)}
    (hk : k ∈ PositiveFreudenthalSupport u omega x) :
    realFreudenthalPathVertex u omega k ∈
      Set.range (realFreudenthalPathVertex v pi) := by
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      funext i
      exact Fin.elim0 i
  | succ m =>
      have hkPos : 0 < freudenthalPathBarycentricWeight u omega x k :=
        (Finset.mem_filter.mp hk).2
      have huBounds := coordinate_sub_base_mem_Icc_of_orderedRegion hxU
      have hvBounds := coordinate_sub_base_mem_Icc_of_orderedRegion hxV
      rcases Fin.eq_castSucc_or_eq_last k with ⟨q, rfl⟩ | rfl
      · by_cases hqZero : q = 0
        · subst q
          have htopEq :
              integerVectorRealization (upperRoundedVertex u x) =
                realFreudenthalPathVertex u omega 0 := by
            funext i
            let r := omega.symm i
            have hr : omega r = i := omega.apply_symm_apply i
            have hyMono := hxU.2.1 (0 : Fin (m + 1)) r
              (Fin.zero_le r)
            have hbase :
                1 - (x (omega 0) - (u (omega 0) : ℝ)) > 0 := by
              simpa [freudenthalPathBarycentricWeight,
                orderedComplementCoordinates] using hkPos
            have hlt : x i - (u i : ℝ) < 1 := by
              simp only [orderedComplementCoordinates] at hyMono
              rw [hr] at hyMono
              linarith
            simp only [integerVectorRealization, upperRoundedVertex,
              realFreudenthalPathVertex, Fin.val_zero]
            rw [if_neg (not_le_of_gt hlt)]
            norm_num
          have hroundEq : upperRoundedVertex u x =
              upperRoundedVertex v x :=
            upperRoundedVertex_eq_of_two_bases huBounds hvBounds
          change realFreudenthalPathVertex u omega 0 ∈
            Set.range (realFreudenthalPathVertex v pi)
          rw [← htopEq]
          rw [hroundEq]
          exact integerVector_upperRoundedVertex_mem_path_range hxV
        · have hqPos : 0 < q.val := Nat.pos_of_ne_zero
              (fun h ↦ hqZero (Fin.ext h))
          let p : Fin (m + 1) := ⟨q.val - 1, by omega⟩
          let theta : ℝ :=
            x (omega q) - (u (omega q) : ℝ)
          have hpq : p < q := by
            apply Fin.lt_def.mpr
            dsimp [p]
            omega
          have hweight :
              theta < x (omega p) - (u (omega p) : ℝ) := by
            have hw := hkPos
            rw [freudenthalPathBarycentricWeight,
              realGammaCoords_apply_castSucc_of_ne_zero
                (orderedComplementCoordinates u omega x) q hqZero] at hw
            simp only [orderedComplementCoordinates] at hw
            dsimp [p, theta]
            linarith
          have htheta : theta ∈ Set.Ico (0 : ℝ) 1 := by
            constructor
            · exact (coordinate_sub_base_mem_Icc_of_orderedRegion
                hxU (omega q)).1
            · have hpTop :=
                (coordinate_sub_base_mem_Icc_of_orderedRegion
                  hxU (omega p)).2
              linarith
          have hinteriorEq :
              integerVectorRealization
                  (interiorRoundedVertex u x theta) =
                realFreudenthalPathVertex u omega q.castSucc := by
            funext i
            let r := omega.symm i
            have hr : omega r = i := omega.apply_symm_apply i
            have hiff : theta < x i - (u i : ℝ) ↔
                r.val < q.val := by
              constructor
              · intro hthetaR
                by_contra hrq
                have hqr : q ≤ r := Fin.le_iff_val_le_val.mpr
                  (Nat.le_of_not_gt hrq)
                have hyMono := hxU.2.1 q r hqr
                simp only [orderedComplementCoordinates] at hyMono
                rw [hr] at hyMono
                dsimp [theta] at hthetaR
                linarith
              · intro hrq
                have hrp : r ≤ p := by
                  apply Fin.le_iff_val_le_val.mpr
                  dsimp [p]
                  omega
                have hyMono := hxU.2.1 r p hrp
                simp only [orderedComplementCoordinates] at hyMono
                rw [hr] at hyMono
                linarith
            simp only [integerVectorRealization, interiorRoundedVertex,
              realFreudenthalPathVertex, Fin.val_castSucc]
            by_cases h : theta < x i - (u i : ℝ)
            · rw [if_pos h, if_pos (hiff.mp h)]
              norm_num
            · rw [if_neg h, if_neg (not_congr hiff |>.mp h)]
              norm_num
          have hroundEq : interiorRoundedVertex u x theta =
              interiorRoundedVertex v x theta :=
            interiorRoundedVertex_eq_of_two_bases htheta
              huBounds hvBounds
          rw [← hinteriorEq, hroundEq]
          exact integerVector_interiorRoundedVertex_mem_path_range
            hxV theta
      · have hlowerEq :
            integerVectorRealization (lowerRoundedVertex u x) =
              realFreudenthalPathVertex u omega (Fin.last (m + 1)) := by
          funext i
          let r := omega.symm i
          have hr : omega r = i := omega.apply_symm_apply i
          have hyMono := hxU.2.1 r (Fin.last m) (Fin.le_last r)
          have hlastPos :
              0 < x (omega (Fin.last m)) -
                (u (omega (Fin.last m)) : ℝ) := by
            simpa [freudenthalPathBarycentricWeight,
              orderedComplementCoordinates] using hkPos
          have hpos : 0 < x i - (u i : ℝ) := by
            simp only [orderedComplementCoordinates] at hyMono
            rw [hr] at hyMono
            linarith
          simp only [integerVectorRealization, lowerRoundedVertex,
            realFreudenthalPathVertex, Fin.val_last]
          rw [if_pos hpos]
          have hrank : (omega.symm i).val < m + 1 :=
            (omega.symm i).isLt
          rw [if_pos hrank]
          norm_num
        have hroundEq : lowerRoundedVertex u x =
            lowerRoundedVertex v x :=
          lowerRoundedVertex_eq_of_two_bases huBounds hvBounds
        rw [← hlowerEq, hroundEq]
        exact integerVector_lowerRoundedVertex_mem_path_range hxV

/-- Within one affinely independent path simplex, every positive canonical
barycentric vertex belongs to any face whose convex hull contains the
point. -/
theorem positiveSupport_vertex_mem_face {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} {s : Set (Fin n → ℝ)}
    (_hx : InRealFreudenthalOrderedRegion u omega x)
    (hs : s ⊆ Set.range (realFreudenthalPathVertex u omega))
    (hxs : x ∈ convexHull ℝ s)
    {k : Fin (n + 1)}
    (hk : k ∈ PositiveFreudenthalSupport u omega x) :
    realFreudenthalPathVertex u omega k ∈ s := by
  by_contra hnot
  let A : Set (Fin (n + 1)) :=
    {j | realFreudenthalPathVertex u omega j ∈ s}
  have hsImage : s ⊆ realFreudenthalPathVertex u omega '' A := by
    intro y hy
    obtain ⟨j, rfl⟩ := hs hy
    exact ⟨j, hy, rfl⟩
  have hsum :
      ∑ j ∈ (Finset.univ : Finset (Fin (n + 1))),
          freudenthalPathBarycentricWeight u omega x j = 1 := by
    simpa using sum_freudenthalPathBarycentricWeight u omega x
  have hm :
      (Finset.univ : Finset (Fin (n + 1))).affineCombination ℝ
          (realFreudenthalPathVertex u omega)
          (freudenthalPathBarycentricWeight u omega x) ∈
        affineSpan ℝ
          (realFreudenthalPathVertex u omega '' A) := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
      sum_barycentricWeight_smul_pathVertex]
    exact affineSpan_mono ℝ hsImage
      (convexHull_subset_affineSpan s hxs)
  have hzero :=
    (affineIndependent_realFreudenthalPathVertex u omega).eq_zero_of_affineCombination_mem_affineSpan
      hsum hm (Finset.mem_univ k) (show k ∉ A from hnot)
  exact (ne_of_gt (Finset.mem_filter.mp hk).2) hzero

/-- The convex hulls of two explicit Freudenthal top simplices intersect
only in the convex hull of their common vertices. -/
theorem convexHull_inter_convexHull_path_subset_common {n : ℕ}
    (u v : Fin n → ℤ)
    (omega pi : Equiv.Perm (Fin n)) :
    convexHull ℝ (Set.range (realFreudenthalPathVertex u omega)) ∩
        convexHull ℝ (Set.range (realFreudenthalPathVertex v pi)) ⊆
      convexHull ℝ
        (Set.range (realFreudenthalPathVertex u omega) ∩
          Set.range (realFreudenthalPathVertex v pi)) := by
  intro x hx
  have hxU : InRealFreudenthalOrderedRegion u omega x := by
    change x ∈ {x | InRealFreudenthalOrderedRegion u omega x}
    rw [← convexHull_realFreudenthalPath_eq_orderedRegion]
    exact hx.1
  have hxV : InRealFreudenthalOrderedRegion v pi x := by
    change x ∈ {x | InRealFreudenthalOrderedRegion v pi x}
    rw [← convexHull_realFreudenthalPath_eq_orderedRegion]
    exact hx.2
  apply (convexHull_mono (𝕜 := ℝ) ?_)
    (mem_convexHull_image_positiveSupport hxU)
  intro y hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp
    (Finset.mem_coe.mp hy)
  exact ⟨Set.mem_range_self k,
    positiveSupport_vertex_mem_other_path hxU hxV hk⟩

/-! ## Cell-independent barycentric coefficients -/

/-- Maximum of finitely many real values together with zero.  Adding zero
makes the definition uniform in dimension zero. -/
noncomputable def finiteMaxWithZero {n : ℕ} (f : Fin n → ℝ) : ℝ :=
  let S : Finset ℝ := insert 0 (Finset.univ.image f)
  S.max' (by simp [S])

/-- A convenient exactness criterion for `finiteMaxWithZero`. -/
theorem finiteMaxWithZero_eq {n : ℕ} (f : Fin n → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hupper : ∀ i, f i ≤ c)
    (hattain : c = 0 ∨ ∃ i, f i = c) :
    finiteMaxWithZero f = c := by
  let S : Finset ℝ := insert 0 (Finset.univ.image f)
  have hS : S.Nonempty := by simp [S]
  apply le_antisymm
  · apply Finset.max'_le S hS c
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hc
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact hupper i
  · rcases hattain with rfl | ⟨i, hi⟩
    · exact Finset.le_max' S 0 (Finset.mem_insert_self _ _)
    · rw [← hi]
      exact Finset.le_max' S (f i)
        (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- Global nodal coefficient attached to an integer lattice vertex.  It is
the standard Freudenthal hat function and does not mention a cell or a
permutation. -/
noncomputable def freudenthalGlobalHat {n : ℕ}
    (p : Fin n → ℤ) (x : Fin n → ℝ) : ℝ :=
  1 - finiteMaxWithZero (fun i ↦ (p i : ℝ) - x i) -
    finiteMaxWithZero (fun i ↦ x i - (p i : ℝ))

/-- On any containing Freudenthal cell, its canonical barycentric
coefficient at a path vertex is exactly the cell-independent global hat
function at that integer vertex. -/
theorem freudenthalPathBarycentricWeight_eq_globalHat {n : ℕ}
    {u : Fin n → ℤ} {omega : Equiv.Perm (Fin n)}
    {x : Fin n → ℝ} (hx : InRealFreudenthalOrderedRegion u omega x)
    (k : Fin (n + 1)) :
    freudenthalPathBarycentricWeight u omega x k =
      freudenthalGlobalHat (integerFreudenthalPathVertex u omega k) x := by
  cases n with
  | zero =>
      have hk : k = 0 := Fin.eq_zero k
      subst k
      simp [freudenthalPathBarycentricWeight, freudenthalGlobalHat,
        finiteMaxWithZero, integerFreudenthalPathVertex,
        realGammaCoords_zero]
  | succ m =>
      have huBounds := coordinate_sub_base_mem_Icc_of_orderedRegion hx
      rcases Fin.eq_castSucc_or_eq_last k with ⟨q, rfl⟩ | rfl
      · by_cases hqZero : q = 0
        · subst q
          have hvertexZero :
              integerFreudenthalPathVertex u omega 0 = u := by
            funext i
            simp [integerFreudenthalPathVertex]
          have hmaxLeft :
              finiteMaxWithZero
                  (fun i ↦
                    (integerFreudenthalPathVertex u omega 0 i : ℝ) -
                      x i) = 0 := by
            rw [hvertexZero]
            apply finiteMaxWithZero_eq _ 0 le_rfl
            · intro i
              linarith [(huBounds i).1]
            · exact Or.inl rfl
          let z0 : ℝ :=
            x (omega 0) - (u (omega 0) : ℝ)
          have hz0 : 0 ≤ z0 := (huBounds (omega 0)).1
          have hmaxRight :
              finiteMaxWithZero
                  (fun i ↦ x i -
                    (integerFreudenthalPathVertex u omega 0 i : ℝ)) =
                z0 := by
            rw [hvertexZero]
            apply finiteMaxWithZero_eq _ z0 hz0
            · intro i
              let r := omega.symm i
              have hr : omega r = i := omega.apply_symm_apply i
              have hyMono := hx.2.1 (0 : Fin (m + 1)) r
                (Fin.zero_le r)
              simp only [orderedComplementCoordinates] at hyMono
              rw [hr] at hyMono
              dsimp [z0]
              linarith
            · right
              refine ⟨omega 0, ?_⟩
              simp [z0]
          change freudenthalPathBarycentricWeight u omega x 0 =
            freudenthalGlobalHat (integerFreudenthalPathVertex u omega 0) x
          rw [freudenthalPathBarycentricWeight,
            realGammaCoords_apply_zero]
          simp only [orderedComplementCoordinates,
            freudenthalGlobalHat, hmaxLeft, hmaxRight]
          dsimp [z0]
          ring
        · have hqPos : 0 < q.val := Nat.pos_of_ne_zero
              (fun h ↦ hqZero (Fin.ext h))
          let p : Fin (m + 1) := ⟨q.val - 1, by omega⟩
          let zp : ℝ := x (omega p) - (u (omega p) : ℝ)
          let zq : ℝ := x (omega q) - (u (omega q) : ℝ)
          have hpq : p < q := by
            apply Fin.lt_def.mpr
            dsimp [p]
            omega
          have hzpTop : zp ≤ 1 := (huBounds (omega p)).2
          have hzqZero : 0 ≤ zq := (huBounds (omega q)).1
          have hmaxLeft :
              finiteMaxWithZero
                  (fun i ↦
                    (integerFreudenthalPathVertex u omega q.castSucc i : ℝ) -
                      x i) = 1 - zp := by
            apply finiteMaxWithZero_eq _ (1 - zp)
              (sub_nonneg.mpr hzpTop)
            · intro i
              let r := omega.symm i
              have hr : omega r = i := omega.apply_symm_apply i
              simp only [integerFreudenthalPathVertex,
                Fin.val_castSucc, Int.cast_add, Int.cast_ite,
                Int.cast_one, Int.cast_zero]
              by_cases hrq : r.val < q.val
              · rw [if_pos (by simpa [r] using hrq)]
                have hrp : r ≤ p := by
                  apply Fin.le_iff_val_le_val.mpr
                  dsimp [p]
                  omega
                have hyMono := hx.2.1 r p hrp
                simp only [orderedComplementCoordinates] at hyMono
                rw [hr] at hyMono
                dsimp [zp]
                linarith
              · rw [if_neg (by simpa [r] using hrq)]
                have hzi := (huBounds i).1
                linarith [hzpTop]
            · right
              refine ⟨omega p, ?_⟩
              simp only [integerFreudenthalPathVertex,
                omega.symm_apply_apply, Fin.val_castSucc,
                Int.cast_add, Int.cast_ite, Int.cast_one,
                Int.cast_zero]
              rw [if_pos (Fin.lt_def.mp hpq)]
              dsimp [zp]
              ring
          have hmaxRight :
              finiteMaxWithZero
                  (fun i ↦ x i -
                    (integerFreudenthalPathVertex u omega q.castSucc i : ℝ)) =
                zq := by
            apply finiteMaxWithZero_eq _ zq hzqZero
            · intro i
              let r := omega.symm i
              have hr : omega r = i := omega.apply_symm_apply i
              simp only [integerFreudenthalPathVertex,
                Fin.val_castSucc, Int.cast_add, Int.cast_ite,
                Int.cast_one, Int.cast_zero]
              by_cases hrq : r.val < q.val
              · rw [if_pos (by simpa [r] using hrq)]
                have hzi := (huBounds i).2
                linarith [hzqZero]
              · rw [if_neg (by simpa [r] using hrq)]
                have hqr : q ≤ r := Fin.le_iff_val_le_val.mpr
                  (Nat.le_of_not_gt hrq)
                have hyMono := hx.2.1 q r hqr
                simp only [orderedComplementCoordinates] at hyMono
                rw [hr] at hyMono
                dsimp [zq]
                linarith
            · right
              refine ⟨omega q, ?_⟩
              simp [integerFreudenthalPathVertex, zq]
          rw [freudenthalPathBarycentricWeight,
            realGammaCoords_apply_castSucc_of_ne_zero
              (orderedComplementCoordinates u omega x) q hqZero]
          simp only [orderedComplementCoordinates,
            freudenthalGlobalHat, hmaxLeft, hmaxRight]
          dsimp [p, zp, zq]
          ring
      · let zlast : ℝ :=
          x (omega (Fin.last m)) -
            (u (omega (Fin.last m)) : ℝ)
        have hzlastTop : zlast ≤ 1 :=
          (huBounds (omega (Fin.last m))).2
        have hmaxLeft :
            finiteMaxWithZero
                (fun i ↦
                  (integerFreudenthalPathVertex u omega
                    (Fin.last (m + 1)) i : ℝ) - x i) =
              1 - zlast := by
          apply finiteMaxWithZero_eq _ (1 - zlast)
            (sub_nonneg.mpr hzlastTop)
          · intro i
            let r := omega.symm i
            have hr : omega r = i := omega.apply_symm_apply i
            have hyMono := hx.2.1 r (Fin.last m) (Fin.le_last r)
            simp only [orderedComplementCoordinates] at hyMono
            simp only [integerFreudenthalPathVertex, Fin.val_last,
              Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero]
            rw [if_pos (omega.symm i).isLt, hr] at *
            dsimp [zlast]
            linarith
          · right
            refine ⟨omega (Fin.last m), ?_⟩
            simp [integerFreudenthalPathVertex, zlast]
            ring
        have hmaxRight :
            finiteMaxWithZero
                (fun i ↦ x i -
                  (integerFreudenthalPathVertex u omega
                    (Fin.last (m + 1)) i : ℝ)) = 0 := by
          apply finiteMaxWithZero_eq _ 0 le_rfl
          · intro i
            simp only [integerFreudenthalPathVertex, Fin.val_last,
              Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero]
            rw [if_pos (omega.symm i).isLt]
            linarith [(huBounds i).2]
          · exact Or.inl rfl
        rw [freudenthalPathBarycentricWeight,
          realGammaCoords_apply_last]
        simp only [orderedComplementCoordinates,
          freudenthalGlobalHat, hmaxLeft, hmaxRight]
        dsimp [zlast]
        ring

/-- Casting integer vectors coordinatewise into `ℝ` loses no information. -/
theorem integerVectorRealization_injective {n : ℕ} :
    Function.Injective
      (integerVectorRealization : (Fin n → ℤ) → (Fin n → ℝ)) := by
  intro a b hab
  funext i
  have hi := congrFun hab i
  change (a i : ℝ) = (b i : ℝ) at hi
  exact_mod_cast hi

/-- Positivity of the canonical coefficient at a shared lattice vertex is
independent of the containing Freudenthal cell.  Unlike mere membership in
the second path, this records that the corresponding vertex lies in the
positive support there as well. -/
theorem positiveSupport_vertex_mem_other_positiveSupport {n : ℕ}
    {u v : Fin n → ℤ}
    {omega pi : Equiv.Perm (Fin n)} {x : Fin n → ℝ}
    (hxU : InRealFreudenthalOrderedRegion u omega x)
    (hxV : InRealFreudenthalOrderedRegion v pi x)
    {k : Fin (n + 1)}
    (hk : k ∈ PositiveFreudenthalSupport u omega x) :
    ∃ j ∈ PositiveFreudenthalSupport v pi x,
      realFreudenthalPathVertex u omega k =
        realFreudenthalPathVertex v pi j := by
  obtain ⟨j, hj⟩ :=
    positiveSupport_vertex_mem_other_path hxU hxV hk
  have hInteger :
      integerFreudenthalPathVertex u omega k =
        integerFreudenthalPathVertex v pi j := by
    apply integerVectorRealization_injective
    rw [show integerVectorRealization
        (integerFreudenthalPathVertex u omega k) =
          realFreudenthalPathVertex u omega k by
        exact cast_integerFreudenthalPathVertex u omega k]
    rw [show integerVectorRealization
        (integerFreudenthalPathVertex v pi j) =
          realFreudenthalPathVertex v pi j by
        exact cast_integerFreudenthalPathVertex v pi j]
    exact hj.symm
  refine ⟨j, ?_, hj.symm⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hkPos : 0 < freudenthalPathBarycentricWeight u omega x k :=
    (Finset.mem_filter.mp hk).2
  rw [freudenthalPathBarycentricWeight_eq_globalHat hxU k] at hkPos
  rw [freudenthalPathBarycentricWeight_eq_globalHat hxV j, ← hInteger]
  exact hkPos

/-- The convex hulls of arbitrary faces of two explicit Freudenthal top
simplices meet only in the convex hull of their common vertices.  This is
the face-level intersection theorem required by the geometric simplicial
complex constructor. -/
theorem convexHull_inter_convexHull_faces_subset_common {n : ℕ}
    {u v : Fin n → ℤ}
    {omega pi : Equiv.Perm (Fin n)}
    {s t : Set (Fin n → ℝ)}
    (hs : s ⊆ Set.range (realFreudenthalPathVertex u omega))
    (ht : t ⊆ Set.range (realFreudenthalPathVertex v pi)) :
    convexHull ℝ s ∩ convexHull ℝ t ⊆
      convexHull ℝ (s ∩ t) := by
  intro x hx
  have hxU : InRealFreudenthalOrderedRegion u omega x := by
    change x ∈ {y | InRealFreudenthalOrderedRegion u omega y}
    rw [← convexHull_realFreudenthalPath_eq_orderedRegion]
    exact convexHull_mono hs hx.1
  have hxV : InRealFreudenthalOrderedRegion v pi x := by
    change x ∈ {y | InRealFreudenthalOrderedRegion v pi y}
    rw [← convexHull_realFreudenthalPath_eq_orderedRegion]
    exact convexHull_mono ht hx.2
  apply (convexHull_mono (𝕜 := ℝ) ?_)
    (mem_convexHull_image_positiveSupport hxU)
  intro y hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp
    (Finset.mem_coe.mp hy)
  have hleft : realFreudenthalPathVertex u omega k ∈ s :=
    positiveSupport_vertex_mem_face hxU hs hx.1 hk
  obtain ⟨j, hj, hvertex⟩ :=
    positiveSupport_vertex_mem_other_positiveSupport hxU hxV hk
  have hright : realFreudenthalPathVertex u omega k ∈ t := by
    rw [hvertex]
    exact positiveSupport_vertex_mem_face hxV ht hx.2 hj
  exact ⟨hleft, hright⟩

/-- Realized literal `Gamma` faces, including the empty face, satisfy the
geometric convex-hull intersection axiom. -/
theorem inter_subset_convexHull_realizedGammaFreudenthalFaceOrEmpty
    (N n : ℕ) {s t : Finset (Fin n → ℝ)}
    (hs : IsRealizedGammaFreudenthalFaceOrEmpty N n s)
    (ht : IsRealizedGammaFreudenthalFaceOrEmpty N n t) :
    convexHull ℝ (s : Set (Fin n → ℝ)) ∩
        convexHull ℝ (t : Set (Fin n → ℝ)) ⊆
      convexHull ℝ (s ∩ t : Set (Fin n → ℝ)) := by
  obtain ⟨tau, htau, rfl⟩ := hs
  obtain ⟨eta, heta, rfl⟩ := ht
  rcases htau with rfl | ⟨rho, hrho, htauSub⟩
  · simp
  rcases heta with rfl | ⟨sigma, hsigma, hetaSub⟩
  · simp
  obtain ⟨u, omega, hrhoReal⟩ := hrho.realization_eq_image_path
  obtain ⟨v, pi, hsigmaReal⟩ := hsigma.realization_eq_image_path
  have hTauPath :
      (gammaFaceRealization tau : Set (Fin n → ℝ)) ⊆
        Set.range (realFreudenthalPathVertex u omega) := by
    intro y hy
    have hyTop := gammaFaceRealization_mono htauSub hy
    rw [hrhoReal] at hyTop
    simpa using hyTop
  have hEtaPath :
      (gammaFaceRealization eta : Set (Fin n → ℝ)) ⊆
        Set.range (realFreudenthalPathVertex v pi) := by
    intro y hy
    have hyTop := gammaFaceRealization_mono hetaSub hy
    rw [hsigmaReal] at hyTop
    simpa using hyTop
  simpa only [Finset.coe_inter] using
    (convexHull_inter_convexHull_faces_subset_common
      hTauPath hEtaPath)

/-- The empty-inclusive realized face family is affinely independent, as
required by `Geometry.SimplicialComplex.ofErase`. -/
theorem affineIndependent_realizedGammaFreudenthalFaceOrEmpty
    (N n : ℕ) (s : Finset (Fin n → ℝ))
    (hs : IsRealizedGammaFreudenthalFaceOrEmpty N n s) :
    AffineIndependent ℝ
      (fun x : (↑s : Set (Fin n → ℝ)) ↦ (x : Fin n → ℝ)) := by
  obtain ⟨tau, htau, rfl⟩ := hs
  by_cases hne : tau.Nonempty
  · exact htau.affineIndependent_realization hne
  · have heq : tau = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst tau
    rw [gammaFaceRealization_empty]
    let hinst : Subsingleton
        (↥((↑(∅ : Finset (Fin n → ℝ))) : Set (Fin n → ℝ))) :=
      Set.Subsingleton.coe_sort (by
        intro a ha b hb
        simp at ha)
    exact @affineIndependent_of_subsingleton
      ℝ _ _ _ _ _ _ _ hinst _

/-- The genuine geometric Freudenthal simplicial complex on the literal
realization of the integer `Gamma` vertices.  Its fields are supplied by
proved affine-independence, downward-closure, and intersection theorems. -/
noncomputable def gammaFreudenthalGeometricComplex (N n : ℕ) :
    Geometry.SimplicialComplex ℝ (Fin n → ℝ) :=
  Geometry.SimplicialComplex.ofErase
    {s : Finset (Fin n → ℝ) |
      IsRealizedGammaFreudenthalFaceOrEmpty N n s}
    (affineIndependent_realizedGammaFreudenthalFaceOrEmpty N n)
    (isLowerSet_isRealizedGammaFreudenthalFaceOrEmpty N n)
    (by
      intro s hs t ht
      exact inter_subset_convexHull_realizedGammaFreudenthalFaceOrEmpty
        N n hs ht)

/-- Removing the empty face from the constructor leaves exactly the
nonempty realized abstract Freudenthal faces. -/
theorem mem_gammaFreudenthalGeometricComplex_faces_iff
    (N n : ℕ) (s : Finset (Fin n → ℝ)) :
    s ∈ (gammaFreudenthalGeometricComplex N n).faces ↔
      IsRealizedGammaFreudenthalFace N n s := by
  constructor
  · intro hs
    have hsFamily : IsRealizedGammaFreudenthalFaceOrEmpty N n s := hs.1
    have hsNe : s ≠ ∅ := by simpa using hs.2
    obtain ⟨tau, htau, htauReal⟩ := hsFamily
    have htauNe : tau.Nonempty := by
      by_contra h
      have htauEmpty : tau = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp h
      subst tau
      simp at htauReal
      rw [← htauReal] at hsNe
      exact hsNe rfl
    exact ⟨tau, htau, htauNe, htauReal⟩
  · rintro ⟨tau, htau, htauNe, rfl⟩
    constructor
    · exact ⟨tau, htau, rfl⟩
    · have hrealNe : gammaFaceRealization tau ≠ ∅ := by
        intro h
        have hcard := card_gammaFaceRealization tau
        rw [h, Finset.card_empty] at hcard
        exact (Finset.card_pos.mpr htauNe).ne hcard
      simpa using hrealNe

/-! ## Coverage of the monotone simplex -/

/-- Base of the closed unit cube used to cover a real point.  At a
positive integer coordinate we choose the cube immediately below it; at
zero we choose base zero.  This convention is what keeps both boundary
facets inside `Gamma`. -/
noncomputable def freudenthalCoverBase {n : ℕ}
    (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i ↦ if x i = 0 then 0 else ⌈x i⌉ - 1

/-- Fractional height above the chosen closed-cube base.  Its values lie
in `[0,1]`, with positive integral coordinates represented by height one. -/
noncomputable def freudenthalCoverFraction {n : ℕ}
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i - (freudenthalCoverBase x i : ℝ)

/-- Lexicographic sorting key: decreasing fractional height, with larger
coordinate indices first in a tie.  The tie rule is forced by the
nondecreasing inequalities defining `Gamma`. -/
noncomputable def freudenthalCoverKey {n : ℕ}
    (x : Fin n → ℝ) : Fin n →
      (OrderDual ℝ ×ₗ OrderDual (Fin n)) :=
  fun i ↦ toLex
    (OrderDual.toDual (freudenthalCoverFraction x i),
      OrderDual.toDual i)

/-- Permutation selecting the Freudenthal cell containing a real point. -/
noncomputable def freudenthalCoverPermutation {n : ℕ}
    (x : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (freudenthalCoverKey x)

theorem freudenthalCoverFraction_mem_Icc {n : ℕ}
    (x : Fin n → ℝ) (i : Fin n) :
    freudenthalCoverFraction x i ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hi : x i = 0
  · simp [freudenthalCoverFraction, freudenthalCoverBase, hi]
  · have hceilUpper : x i ≤ (⌈x i⌉ : ℤ) := Int.le_ceil (x i)
    have hceilLower : ((⌈x i⌉ : ℤ) : ℝ) < x i + 1 :=
      Int.ceil_lt_add_one (x i)
    constructor
    · simp only [freudenthalCoverFraction, freudenthalCoverBase,
        hi, ↓reduceIte, Int.cast_sub, Int.cast_one]
      linarith
    · simp only [freudenthalCoverFraction, freudenthalCoverBase,
        hi, ↓reduceIte, Int.cast_sub, Int.cast_one]
      linarith

/-- The chosen permutation puts fractional heights in decreasing order. -/
theorem freudenthalCoverFraction_antitone_sort {n : ℕ}
    (x : Fin n → ℝ) :
    Antitone
      (freudenthalCoverFraction x ∘
        freudenthalCoverPermutation x) := by
  intro q r hqr
  have hkey := Tuple.monotone_sort (freudenthalCoverKey x) hqr
  have hfirst := Prod.Lex.monotone_fst _ _ hkey
  exact hfirst

/-- Every real point belongs to the ordered region of the cell chosen by
the closed-cube base and sorted fractional coordinates. -/
theorem mem_orderedRegion_coverCell {n : ℕ} (x : Fin n → ℝ) :
    InRealFreudenthalOrderedRegion
      (freudenthalCoverBase x)
      (freudenthalCoverPermutation x) x := by
  constructor
  · intro q
    have hz := freudenthalCoverFraction_mem_Icc x
      (freudenthalCoverPermutation x q)
    change 0 ≤ 1 - freudenthalCoverFraction x
      (freudenthalCoverPermutation x q)
    linarith [hz.2]
  constructor
  · intro q r hqr
    have hz := freudenthalCoverFraction_antitone_sort x hqr
    simp only [Function.comp_apply] at hz
    change 1 - freudenthalCoverFraction x
        (freudenthalCoverPermutation x q) ≤
      1 - freudenthalCoverFraction x
        (freudenthalCoverPermutation x r)
    linarith
  · intro q
    have hz := freudenthalCoverFraction_mem_Icc x
      (freudenthalCoverPermutation x q)
    change 1 - freudenthalCoverFraction x
      (freudenthalCoverPermutation x q) ≤ 1
    linarith [hz.1]

theorem freudenthalCoverBase_nonneg {N n : ℕ}
    {x : Fin n → ℝ} (hx : IsRealGammaPoint (N : ℝ) x)
    (i : Fin n) : 0 ≤ freudenthalCoverBase x i := by
  by_cases hi : x i = 0
  · simp [freudenthalCoverBase, hi]
  · have hxi : 0 < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hi)
    have hceil : 0 < ⌈x i⌉ := Int.ceil_pos.mpr hxi
    simp only [freudenthalCoverBase, hi, ↓reduceIte]
    omega

theorem freudenthalCoverBase_le_sub_one {N n : ℕ}
    {x : Fin n → ℝ} (hN : 0 < N)
    (hx : IsRealGammaPoint (N : ℝ) x) (i : Fin n) :
    freudenthalCoverBase x i ≤ (N : ℤ) - 1 := by
  by_cases hi : x i = 0
  · simp only [freudenthalCoverBase, hi, ↓reduceIte]
    omega
  · have hceil : ⌈x i⌉ ≤ (N : ℤ) := by
      apply Int.ceil_le.mpr
      exact hx.2.2 i
    simp only [freudenthalCoverBase, hi, ↓reduceIte]
    omega

/-- The special boundary-aware cube base remains coordinatewise
nondecreasing on the monotone simplex. -/
theorem monotone_freudenthalCoverBase {N n : ℕ}
    {x : Fin n → ℝ} (hx : IsRealGammaPoint (N : ℝ) x) :
    Monotone (freudenthalCoverBase x) := by
  intro i j hij
  have hxij := hx.2.1 i j hij
  by_cases hi : x i = 0
  · rw [freudenthalCoverBase, if_pos hi]
    exact freudenthalCoverBase_nonneg hx j
  · have hxi : 0 < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hi)
    have hj : x j ≠ 0 := ne_of_gt (hxi.trans_le hxij)
    simp only [freudenthalCoverBase, hi, hj, ↓reduceIte]
    exact sub_le_sub_right (Int.ceil_mono hxij) 1

/-- If two coordinates have the same cube base, the later coordinate is
visited no later by the sorted path.  This is the exact tie-sensitive
fact needed to keep every intermediate vertex monotone. -/
theorem coverPermutation_symm_anti_of_base_eq {N n : ℕ}
    {x : Fin n → ℝ} (hx : IsRealGammaPoint (N : ℝ) x)
    {i j : Fin n} (hij : i ≤ j)
    (hbase : freudenthalCoverBase x i =
      freudenthalCoverBase x j) :
    (freudenthalCoverPermutation x).symm j ≤
      (freudenthalCoverPermutation x).symm i := by
  by_contra hnot
  have hrank : (freudenthalCoverPermutation x).symm i <
      (freudenthalCoverPermutation x).symm j :=
    lt_of_not_ge hnot
  have hkey := Tuple.monotone_sort (freudenthalCoverKey x)
    hrank.le
  simp only [Function.comp_apply, freudenthalCoverPermutation,
    Equiv.apply_symm_apply, freudenthalCoverKey] at hkey
  rw [Prod.Lex.toLex_le_toLex] at hkey
  have hfrac : freudenthalCoverFraction x i ≤
      freudenthalCoverFraction x j := by
    simp only [freudenthalCoverFraction]
    rw [hbase]
    linarith [hx.2.1 i j hij]
  rcases hkey with hstrict | ⟨heq, hindex⟩
  · change freudenthalCoverFraction x j <
      freudenthalCoverFraction x i at hstrict
    exact (not_lt_of_ge hfrac) hstrict
  · change j ≤ i at hindex
    have hijEq : i = j := le_antisymm hij hindex
    subst j
    exact (lt_irrefl _ hrank)

/-- Every vertex of the selected path is an integer point of `Gamma`.
The positivity assumption on `N` is necessary when `n > 0`: for `N = 0`
there cannot be an `n`-dimensional lattice simplex in a singleton. -/
theorem integerFreudenthalPathVertex_cover_isGammaPoint
    {N n : ℕ} (hN : 0 < N) {x : Fin n → ℝ}
    (hx : IsRealGammaPoint (N : ℝ) x) (k : Fin (n + 1)) :
    IsGammaPoint (N : ℤ)
      (integerFreudenthalPathVertex
        (freudenthalCoverBase x)
        (freudenthalCoverPermutation x) k) := by
  constructor
  · intro i
    simp only [integerFreudenthalPathVertex]
    have hbase := freudenthalCoverBase_nonneg hx i
    split <;> omega
  constructor
  · intro i j hij
    have hbase := monotone_freudenthalCoverBase hx hij
    simp only [integerFreudenthalPathVertex]
    by_cases hi : ((freudenthalCoverPermutation x).symm i).val < k.val
    · have hRank := coverPermutation_symm_anti_of_base_eq hx hij
      by_cases hbaseEq : freudenthalCoverBase x i =
          freudenthalCoverBase x j
      · have hj : ((freudenthalCoverPermutation x).symm j).val <
            k.val := by
          exact lt_of_le_of_lt
            (Fin.le_iff_val_le_val.mp (hRank hbaseEq)) hi
        rw [if_pos hi, if_pos hj, hbaseEq]
      · have hbaseStrict : freudenthalCoverBase x i <
            freudenthalCoverBase x j := lt_of_le_of_ne hbase hbaseEq
        by_cases hj : ((freudenthalCoverPermutation x).symm j).val < k.val
        · rw [if_pos hi, if_pos hj]
          omega
        · rw [if_pos hi, if_neg hj]
          omega
    · rw [if_neg hi]
      split <;> omega
  · intro i
    simp only [integerFreudenthalPathVertex]
    have hbase := freudenthalCoverBase_le_sub_one hN hx i
    split <;> omega

/-- The certified literal `Gamma` top simplex selected for a real point. -/
noncomputable def gammaCoverTopSimplex {N n : ℕ} (hN : 0 < N)
    (x : Fin n → ℝ) (hx : IsRealGammaPoint (N : ℝ) x) :
    Finset (GammaPoint N n) :=
  Finset.univ.image fun k : Fin (n + 1) ↦
    ⟨integerFreudenthalPathVertex
        (freudenthalCoverBase x)
        (freudenthalCoverPermutation x) k,
      integerFreudenthalPathVertex_cover_isGammaPoint hN hx k⟩

theorem gammaCoverTopSimplex_isTop {N n : ℕ} (hN : 0 < N)
    (x : Fin n → ℝ) (hx : IsRealGammaPoint (N : ℝ) x) :
    IsGammaFreudenthalTopSimplex
      (gammaCoverTopSimplex hN x hx) := by
  refine ⟨freudenthalCoverBase x,
    freudenthalCoverPermutation x, ?_⟩
  rw [freudenthalSimplex_eq_image_integerPath]
  ext y
  simp [gammaCoverTopSimplex]

theorem gammaCoverTopSimplex_nonempty {N n : ℕ} (hN : 0 < N)
    (x : Fin n → ℝ) (hx : IsRealGammaPoint (N : ℝ) x) :
    (gammaCoverTopSimplex hN x hx).Nonempty := by
  refine ⟨⟨integerFreudenthalPathVertex
      (freudenthalCoverBase x)
      (freudenthalCoverPermutation x) 0,
    integerFreudenthalPathVertex_cover_isGammaPoint hN hx 0⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

/-- Realizing the certified cover simplex returns precisely the explicit
real path used in the ordered-region coverage proof. -/
theorem gammaFaceRealization_gammaCoverTopSimplex {N n : ℕ}
    (hN : 0 < N) (x : Fin n → ℝ)
    (hx : IsRealGammaPoint (N : ℝ) x) :
    gammaFaceRealization (gammaCoverTopSimplex hN x hx) =
      Finset.univ.image
        (realFreudenthalPathVertex
          (freudenthalCoverBase x)
          (freudenthalCoverPermutation x)) := by
  rw [gammaFaceRealization_eq_image_val_cast]
  have hval :
      (gammaCoverTopSimplex hN x hx).image Subtype.val =
        freudenthalSimplex (freudenthalCoverBase x)
          (permutationList (freudenthalCoverPermutation x)) := by
    rw [freudenthalSimplex_eq_image_integerPath]
    ext y
    simp [gammaCoverTopSimplex]
  rw [hval, freudenthalSimplex_eq_image_integerPath]
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    change realFreudenthalPathVertex
        (freudenthalCoverBase x)
        (freudenthalCoverPermutation x) k =
      (fun i ↦ (integerFreudenthalPathVertex
        (freudenthalCoverBase x)
        (freudenthalCoverPermutation x) k i : ℝ))
    exact (cast_integerFreudenthalPathVertex
      (freudenthalCoverBase x)
      (freudenthalCoverPermutation x) k).symm
  · intro hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_image.mpr
    refine ⟨integerFreudenthalPathVertex
      (freudenthalCoverBase x)
      (freudenthalCoverPermutation x) k, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    · change (fun i ↦ (integerFreudenthalPathVertex
          (freudenthalCoverBase x)
          (freudenthalCoverPermutation x) k i : ℝ)) =
        realFreudenthalPathVertex
          (freudenthalCoverBase x)
          (freudenthalCoverPermutation x) k
      exact cast_integerFreudenthalPathVertex
        (freudenthalCoverBase x)
        (freudenthalCoverPermutation x) k

/-- For positive dilation, every real point of `Gamma` lies in the space
of the realized Freudenthal geometric complex. -/
theorem realGamma_subset_gammaFreudenthalGeometricComplex_space
    {N n : ℕ} (hN : 0 < N) :
    realGamma (N : ℝ) n ⊆
      (gammaFreudenthalGeometricComplex N n).space := by
  intro x hx
  change IsRealGammaPoint (N : ℝ) x at hx
  rw [Geometry.SimplicialComplex.mem_space_iff]
  let rho := gammaCoverTopSimplex hN x hx
  refine ⟨gammaFaceRealization rho, ?_, ?_⟩
  · rw [mem_gammaFreudenthalGeometricComplex_faces_iff]
    exact ⟨rho, (gammaCoverTopSimplex_isTop hN x hx).mem_complex
        |> (mem_gammaFreudenthalComplex_iff rho).mp,
      gammaCoverTopSimplex_nonempty hN x hx, rfl⟩
  · dsimp only [rho]
    rw [gammaFaceRealization_gammaCoverTopSimplex]
    have hfinset :
        ((Finset.univ.image
          (realFreudenthalPathVertex
            (freudenthalCoverBase x)
            (freudenthalCoverPermutation x)) :
              Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) =
          Set.range (realFreudenthalPathVertex
            (freudenthalCoverBase x)
            (freudenthalCoverPermutation x)) := by
      ext y
      simp
    rw [hfinset]
    have hordered := mem_orderedRegion_coverCell x
    rw [convexHull_realFreudenthalPath_eq_orderedRegion]
    exact hordered

/-- Every face of the realized complex lies inside the real monotone
simplex, independently of the positivity assumption on `N`. -/
theorem gammaFreudenthalGeometricComplex_space_subset_realGamma
    (N n : ℕ) :
    (gammaFreudenthalGeometricComplex N n).space ⊆
      realGamma (N : ℝ) n := by
  intro x hx
  rw [Geometry.SimplicialComplex.mem_space_iff] at hx
  obtain ⟨s, hsFace, hxs⟩ := hx
  rw [mem_gammaFreudenthalGeometricComplex_faces_iff] at hsFace
  obtain ⟨tau, _, _, rfl⟩ := hsFace
  apply (convexHull_min ?_ (convex_realGamma (N : ℝ) n)) hxs
  intro y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  exact gammaVertexRealization_isRealGammaPoint v

/-- Exact coverage statement for the literal geometric Freudenthal
complex on `Gamma`. -/
theorem gammaFreudenthalGeometricComplex_space_eq_realGamma
    {N n : ℕ} (hN : 0 < N) :
    (gammaFreudenthalGeometricComplex N n).space =
      realGamma (N : ℝ) n := by
  exact Set.Subset.antisymm
    (gammaFreudenthalGeometricComplex_space_subset_realGamma N n)
    (realGamma_subset_gammaFreudenthalGeometricComplex_space hN)

/-! ## Affine transport to the standard simplex -/

/-- Injective affine transport of a finite affinely independent vertex
set is again affinely independent.  This specialized reindexing lemma
bridges mathlib's family-based statement and finite vertex sets. -/
theorem affineIndependent_image_realGammaToDelta {N : ℝ} {n : ℕ}
    {s : Finset (Fin n → ℝ)}
    (hs : AffineIndependent ℝ
      (fun x : (↑s : Set (Fin n → ℝ)) ↦ (x : Fin n → ℝ))) :
    AffineIndependent ℝ
      (fun x : (↑(s.image (realGammaToDeltaAffineMap N n)) :
          Set (Fin (n + 1) → ℝ)) ↦ (x : Fin (n + 1) → ℝ)) := by
  let source : Set (Fin n → ℝ) := (↑s : Set (Fin n → ℝ))
  let target : Set (Fin (n + 1) → ℝ) :=
    (↑(s.image (realGammaToDeltaAffineMap N n)) :
      Set (Fin (n + 1) → ℝ))
  have htarget : target =
      realGammaToDeltaAffineMap N n '' source := by
    ext y
    simp [source, target]
  let eImage : source ≃
      realGammaToDeltaAffineMap N n '' source :=
    Equiv.Set.image (realGammaToDeltaAffineMap N n) source
      (realGammaToDeltaAffineMap_injective N n)
  let e : source ≃ target :=
    eImage.trans (Equiv.setCongr htarget.symm)
  have he :
      (fun y : target ↦ (y : Fin (n + 1) → ℝ)) ∘ e =
        (realGammaToDeltaAffineMap N n) ∘
          (fun y : source ↦ (y : Fin n → ℝ)) := by
    funext y
    simp [e, eImage]
  have hmapped := hs.map' (realGammaToDeltaAffineMap N n)
    (realGammaToDeltaAffineMap_injective N n)
  change AffineIndependent ℝ
    ((realGammaToDeltaAffineMap N n) ∘
      (fun y : source ↦ (y : Fin n → ℝ))) at hmapped
  rw [← he] at hmapped
  exact (affineIndependent_equiv e).mp hmapped

/-- Empty-inclusive delta face family, defined as the literal affine
image of the already verified `Gamma` face family. -/
def IsRealizedDeltaFreudenthalFaceOrEmpty (N n : ℕ)
    (s : Finset (Fin (n + 1) → ℝ)) : Prop :=
  ∃ r : Finset (Fin n → ℝ),
    IsRealizedGammaFreudenthalFaceOrEmpty N n r ∧
      r.image (realGammaToDeltaAffineMap (N : ℝ) n) = s

/-- Nonempty affine images are the faces retained by the geometric
simplicial complex constructor. -/
def IsRealizedDeltaFreudenthalFace (N n : ℕ)
    (s : Finset (Fin (n + 1) → ℝ)) : Prop :=
  IsRealizedDeltaFreudenthalFaceOrEmpty N n s ∧ s.Nonempty

theorem affineIndependent_realizedDeltaFreudenthalFaceOrEmpty
    (N n : ℕ) (s : Finset (Fin (n + 1) → ℝ))
    (hs : IsRealizedDeltaFreudenthalFaceOrEmpty N n s) :
    AffineIndependent ℝ
      (fun x : (↑s : Set (Fin (n + 1) → ℝ)) ↦
        (x : Fin (n + 1) → ℝ)) := by
  obtain ⟨r, hr, rfl⟩ := hs
  exact affineIndependent_image_realGammaToDelta
    (affineIndependent_realizedGammaFreudenthalFaceOrEmpty N n r hr)

/-- The affine-image face family is genuinely downward closed.  The
source face is recovered by filtering its finite vertex set, so this does
not rely on an unproved inverse-image interface. -/
theorem isLowerSet_isRealizedDeltaFreudenthalFaceOrEmpty (N n : ℕ) :
    IsLowerSet {s : Finset (Fin (n + 1) → ℝ) |
      IsRealizedDeltaFreudenthalFaceOrEmpty N n s} := by
  intro s t hts hs
  obtain ⟨r, hr, hsEq⟩ := hs
  let q : Finset (Fin n → ℝ) :=
    r.filter fun y ↦ realGammaToDeltaAffineMap (N : ℝ) n y ∈ t
  have hqr : q ⊆ r := Finset.filter_subset _ _
  have hqFace : IsRealizedGammaFreudenthalFaceOrEmpty N n q :=
    isLowerSet_isRealizedGammaFreudenthalFaceOrEmpty N n hqr hr
  have hqImage :
      q.image (realGammaToDeltaAffineMap (N : ℝ) n) = t := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hy).2
    · intro hz
      have hzS : z ∈ s := hts hz
      rw [← hsEq] at hzS
      obtain ⟨y, hyr, hyz⟩ := Finset.mem_image.mp hzS
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_filter.mpr ⟨hyr, ?_⟩, hyz⟩
      simpa [hyz] using hz
  exact ⟨q, hqFace, hqImage⟩

/-- Injective affine transport preserves the verified convex-hull
intersection axiom. -/
theorem inter_subset_convexHull_realizedDeltaFreudenthalFaceOrEmpty
    (N n : ℕ) {s t : Finset (Fin (n + 1) → ℝ)}
    (hs : IsRealizedDeltaFreudenthalFaceOrEmpty N n s)
    (ht : IsRealizedDeltaFreudenthalFaceOrEmpty N n t) :
    convexHull ℝ (s : Set (Fin (n + 1) → ℝ)) ∩
        convexHull ℝ (t : Set (Fin (n + 1) → ℝ)) ⊆
      convexHull ℝ (s ∩ t : Set (Fin (n + 1) → ℝ)) := by
  obtain ⟨r, hr, rfl⟩ := hs
  obtain ⟨q, hq, rfl⟩ := ht
  let f := realGammaToDeltaAffineMap (N : ℝ) n
  have hf : Function.Injective f :=
    realGammaToDeltaAffineMap_injective (N : ℝ) n
  have hrSet :
      ((↑(r.image f) : Set (Fin (n + 1) → ℝ))) =
        f '' (↑r : Set (Fin n → ℝ)) := by
    ext y
    simp
  have hqSet :
      ((↑(q.image f) : Set (Fin (n + 1) → ℝ))) =
        f '' (↑q : Set (Fin n → ℝ)) := by
    ext y
    simp
  intro x hx
  have hxR : x ∈ f '' convexHull ℝ (↑r : Set (Fin n → ℝ)) := by
    rw [realGammaToDeltaAffineMap_image_convexHull, ← hrSet]
    exact hx.1
  have hxQ : x ∈ f '' convexHull ℝ (↑q : Set (Fin n → ℝ)) := by
    rw [realGammaToDeltaAffineMap_image_convexHull, ← hqSet]
    exact hx.2
  obtain ⟨y, hyr, hyx⟩ := hxR
  obtain ⟨z, hzq, hzx⟩ := hxQ
  have hyz : y = z := hf (hyx.trans hzx.symm)
  subst z
  have hyCommon : y ∈ convexHull ℝ
      ((↑r : Set (Fin n → ℝ)) ∩ (↑q : Set (Fin n → ℝ))) :=
    inter_subset_convexHull_realizedGammaFreudenthalFaceOrEmpty
      N n hr hq ⟨hyr, hzq⟩
  have hyCommon' : y ∈ convexHull ℝ
      (↑(r ∩ q) : Set (Fin n → ℝ)) := by
    simpa only [Finset.coe_inter] using hyCommon
  have hImageInter : (r ∩ q).image f =
      r.image f ∩ q.image f :=
    Finset.image_inter r q hf
  have hCommonSet :
      ((↑((r ∩ q).image f) : Set (Fin (n + 1) → ℝ))) =
        f '' (↑(r ∩ q) : Set (Fin n → ℝ)) := by
    ext w
    simp
  have hresult : x ∈ convexHull ℝ
      (↑(r.image f ∩ q.image f) : Set (Fin (n + 1) → ℝ)) := by
    rw [← hImageInter, hCommonSet,
      ← realGammaToDeltaAffineMap_image_convexHull]
    exact ⟨y, hyCommon', hyx⟩
  simpa only [Finset.coe_inter] using hresult

/-- The geometric Freudenthal simplicial complex in the real standard
simplex `Delta`, obtained by fully verified affine transport. -/
noncomputable def deltaFreudenthalGeometricComplex (N n : ℕ) :
    Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ) :=
  Geometry.SimplicialComplex.ofErase
    {s : Finset (Fin (n + 1) → ℝ) |
      IsRealizedDeltaFreudenthalFaceOrEmpty N n s}
    (affineIndependent_realizedDeltaFreudenthalFaceOrEmpty N n)
    (isLowerSet_isRealizedDeltaFreudenthalFaceOrEmpty N n)
    (by
      intro s hs t ht
      exact inter_subset_convexHull_realizedDeltaFreudenthalFaceOrEmpty
        N n hs ht)

theorem mem_deltaFreudenthalGeometricComplex_faces_iff
    (N n : ℕ) (s : Finset (Fin (n + 1) → ℝ)) :
    s ∈ (deltaFreudenthalGeometricComplex N n).faces ↔
      IsRealizedDeltaFreudenthalFace N n s := by
  change
    (IsRealizedDeltaFreudenthalFaceOrEmpty N n s ∧
      s ∉ ({∅} : Set (Finset (Fin (n + 1) → ℝ)))) ↔ _
  simp [IsRealizedDeltaFreudenthalFace,
    Finset.nonempty_iff_ne_empty]

/-- The space of the delta complex is exactly the affine image of the
space of the gamma complex.  Both inclusions retain explicit source-face
witnesses. -/
theorem image_gammaFreudenthalGeometricComplex_space_eq_delta_space
    (N n : ℕ) :
    realGammaToDeltaAffineMap (N : ℝ) n ''
        (gammaFreudenthalGeometricComplex N n).space =
      (deltaFreudenthalGeometricComplex N n).space := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Geometry.SimplicialComplex.mem_space_iff] at hy ⊢
    obtain ⟨r, hrFace, hyr⟩ := hy
    have hrReal :=
      (mem_gammaFreudenthalGeometricComplex_faces_iff N n r).mp
        hrFace
    obtain ⟨tau, htau, htauNe, htauReal⟩ := hrReal
    have hrOrEmpty :
        IsRealizedGammaFreudenthalFaceOrEmpty N n r :=
      ⟨tau, htau, htauReal⟩
    refine ⟨r.image (realGammaToDeltaAffineMap (N : ℝ) n), ?_, ?_⟩
    · rw [mem_deltaFreudenthalGeometricComplex_faces_iff]
      constructor
      · exact ⟨r, hrOrEmpty, rfl⟩
      · rw [← htauReal]
        exact (htauNe.image gammaVertexRealization).image _
    · have hImageSet :
          ((↑(r.image (realGammaToDeltaAffineMap (N : ℝ) n)) :
              Set (Fin (n + 1) → ℝ))) =
            realGammaToDeltaAffineMap (N : ℝ) n ''
              (↑r : Set (Fin n → ℝ)) := by
        ext z
        simp
      rw [hImageSet, ← realGammaToDeltaAffineMap_image_convexHull]
      exact ⟨y, hyr, rfl⟩
  · intro hx
    rw [Geometry.SimplicialComplex.mem_space_iff] at hx
    obtain ⟨s, hsFace, hxs⟩ := hx
    have hsReal :=
      (mem_deltaFreudenthalGeometricComplex_faces_iff N n s).mp
        hsFace
    obtain ⟨⟨r, hrOrEmpty, hrImage⟩, hsNe⟩ := hsReal
    have hrNe : r.Nonempty := by
      by_contra h
      have hrEmpty : r = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst r
      simp at hrImage
      rw [← hrImage] at hsNe
      exact Finset.not_nonempty_empty hsNe
    obtain ⟨tau, htau, htauReal⟩ := hrOrEmpty
    have htauNe : tau.Nonempty := by
      rw [← htauReal] at hrNe
      simpa [gammaFaceRealization] using hrNe
    have hrFace : r ∈
        (gammaFreudenthalGeometricComplex N n).faces :=
      (mem_gammaFreudenthalGeometricComplex_faces_iff N n r).mpr
        ⟨tau, htau, htauNe, htauReal⟩
    have hImageSet :
        ((↑(r.image (realGammaToDeltaAffineMap (N : ℝ) n)) :
            Set (Fin (n + 1) → ℝ))) =
          realGammaToDeltaAffineMap (N : ℝ) n ''
            (↑r : Set (Fin n → ℝ)) := by
      ext z
      simp
    rw [← hrImage, hImageSet,
      ← realGammaToDeltaAffineMap_image_convexHull] at hxs
    obtain ⟨y, hyr, hyx⟩ := hxs
    refine ⟨y, ?_, hyx⟩
    rw [Geometry.SimplicialComplex.mem_space_iff]
    exact ⟨r, hrFace, hyr⟩

/-- Exact coverage of the real standard simplex by the transported
Freudenthal geometric complex. -/
theorem deltaFreudenthalGeometricComplex_space_eq_realDelta
    {N n : ℕ} (hN : 0 < N) :
    (deltaFreudenthalGeometricComplex N n).space =
      realDelta (N : ℝ) n := by
  calc
    (deltaFreudenthalGeometricComplex N n).space =
        realGammaToDeltaAffineMap (N : ℝ) n ''
          (gammaFreudenthalGeometricComplex N n).space :=
      (image_gammaFreudenthalGeometricComplex_space_eq_delta_space
        N n).symm
    _ = realGammaToDeltaAffineMap (N : ℝ) n ''
          realGamma (N : ℝ) n := by
      rw [gammaFreudenthalGeometricComplex_space_eq_realGamma hN]
    _ = realDelta (N : ℝ) n :=
      realGammaToDeltaAffineMap_image_gamma (N : ℝ)
        (by exact_mod_cast hN.le) n

/-! ## Identification with the original abstract Freudenthal complex -/

/-- Literal real realization of a face of the original abstract
Freudenthal complex on `Point N n`, including the empty face. -/
def IsLiteralDeltaFreudenthalFaceOrEmpty (N n : ℕ)
    (s : Finset (Fin (n + 1) → ℝ)) : Prop :=
  ∃ tau : Finset (Point N n),
    IsFreudenthalSimplex tau ∧ deltaFaceRealization tau = s

/-- The affine-image definition used to construct the geometric complex
is exactly the literal realization of the independently defined abstract
Freudenthal complex. -/
theorem realizedDeltaFreudenthalFaceOrEmpty_iff_literal
    (N n : ℕ) (s : Finset (Fin (n + 1) → ℝ)) :
    IsRealizedDeltaFreudenthalFaceOrEmpty N n s ↔
      IsLiteralDeltaFreudenthalFaceOrEmpty N n s := by
  constructor
  · rintro ⟨r, ⟨eta, heta, hetaReal⟩, rfl⟩
    have hetaMem : eta ∈ gammaFreudenthalComplex N n :=
      (mem_gammaFreudenthalComplex_iff eta).mpr heta
    have hetaRelabel : eta ∈
        (freudenthalComplex N n).relabel (pointGammaEquiv N n) := by
      rw [freudenthalComplex_relabel_pointGammaEquiv]
      exact hetaMem
    obtain ⟨tau, htauMem, htauImage⟩ :=
      (FiniteSimplicialComplex.mem_relabel_iff
        (freudenthalComplex N n) (pointGammaEquiv N n) eta).mp
          hetaRelabel
    refine ⟨tau, (mem_freudenthalComplex_iff tau).mp htauMem, ?_⟩
    calc
      deltaFaceRealization tau =
          (gammaFaceRealization
            (tau.image (pointGammaEquiv N n))).image
              (realGammaToDeltaAffineMap (N : ℝ) n) :=
        (image_realGammaToDelta_gammaFaceRealization_image_equiv
          tau).symm
      _ = (gammaFaceRealization eta).image
            (realGammaToDeltaAffineMap (N : ℝ) n) := by
        rw [htauImage]
      _ = r.image (realGammaToDeltaAffineMap (N : ℝ) n) := by
        rw [hetaReal]
  · rintro ⟨tau, htau, rfl⟩
    let eta : Finset (GammaPoint N n) :=
      tau.image (pointGammaEquiv N n)
    have htauMem : tau ∈ freudenthalComplex N n :=
      (mem_freudenthalComplex_iff tau).mpr htau
    have hetaRelabel : eta ∈
        (freudenthalComplex N n).relabel (pointGammaEquiv N n) := by
      apply (FiniteSimplicialComplex.mem_relabel_iff
        (freudenthalComplex N n) (pointGammaEquiv N n) eta).mpr
      exact ⟨tau, htauMem, rfl⟩
    have hetaMem : eta ∈ gammaFreudenthalComplex N n := by
      rw [← freudenthalComplex_relabel_pointGammaEquiv]
      exact hetaRelabel
    have heta : IsGammaFreudenthalSimplex eta :=
      (mem_gammaFreudenthalComplex_iff eta).mp hetaMem
    refine ⟨gammaFaceRealization eta, ⟨eta, heta, rfl⟩, ?_⟩
    exact image_realGammaToDelta_gammaFaceRealization_image_equiv tau

/-- Consequently, the nonempty geometric faces are exactly the literal
realizations of nonempty faces of the original abstract complex. -/
theorem mem_deltaFreudenthalGeometricComplex_faces_iff_literal
    (N n : ℕ) (s : Finset (Fin (n + 1) → ℝ)) :
    s ∈ (deltaFreudenthalGeometricComplex N n).faces ↔
      ∃ tau : Finset (Point N n),
        IsFreudenthalSimplex tau ∧ tau.Nonempty ∧
          deltaFaceRealization tau = s := by
  rw [mem_deltaFreudenthalGeometricComplex_faces_iff]
  constructor
  · rintro ⟨hs, hsNe⟩
    obtain ⟨tau, htau, htauReal⟩ :=
      (realizedDeltaFreudenthalFaceOrEmpty_iff_literal N n s).mp hs
    have htauNe : tau.Nonempty := by
      by_contra h
      have htauEmpty : tau = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp h
      subst tau
      simp at htauReal
      rw [← htauReal] at hsNe
      exact Finset.not_nonempty_empty hsNe
    exact ⟨tau, htau, htauNe, htauReal⟩
  · rintro ⟨tau, htau, htauNe, rfl⟩
    constructor
    · apply (realizedDeltaFreudenthalFaceOrEmpty_iff_literal
        N n (deltaFaceRealization tau)).mpr
      exact ⟨tau, htau, rfl⟩
    · have hcard := card_deltaFaceRealization tau
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      rw [hEmpty, Finset.card_empty] at hcard
      exact (Finset.card_pos.mpr htauNe).ne hcard

/-- The affine coordinate map carries nonempty geometric Gamma faces to
Delta faces and reflects them.  This is the simplicial-map content of the
geometric coordinate change, stated without pretending the unequal
ambient vector spaces form a global affine equivalence. -/
theorem image_realGammaToDelta_mem_delta_faces_iff
    (N n : ℕ) (r : Finset (Fin n → ℝ)) :
    r.image (realGammaToDeltaAffineMap (N : ℝ) n) ∈
        (deltaFreudenthalGeometricComplex N n).faces ↔
      r ∈ (gammaFreudenthalGeometricComplex N n).faces := by
  rw [mem_deltaFreudenthalGeometricComplex_faces_iff,
    mem_gammaFreudenthalGeometricComplex_faces_iff]
  constructor
  · rintro ⟨⟨q, hq, hqr⟩, hImageNe⟩
    have hqr' : q = r := by
      apply Finset.image_injective
        (realGammaToDeltaAffineMap_injective (N : ℝ) n)
      exact hqr
    subst q
    obtain ⟨tau, htau, htauReal⟩ := hq
    have hrNe : r.Nonempty := hImageNe.of_image
    have htauNe : tau.Nonempty := by
      rw [← htauReal] at hrNe
      exact hrNe.of_image
    exact ⟨tau, htau, htauNe, htauReal⟩
  · rintro ⟨tau, htau, htauNe, htauReal⟩
    constructor
    · exact ⟨r, ⟨tau, htau, htauReal⟩, rfl⟩
    · have hrNe : r.Nonempty := by
        rw [← htauReal]
        exact htauNe.image gammaVertexRealization
      exact hrNe.image _

/-- Corollary 4.9 in the paper's literal top-dimensional wording: at
positive scale, the `I`-cells are exactly the vertex sets of the
`n`-simplices of the geometric triangulation of `Delta`.  The separate
space equality proves that this complex triangulates all of `Delta`. -/
theorem isCell_iff_realization_mem_delta_faces_and_card_of_pos
    {N n : ℕ} (hN : 0 < N) (sigma : Finset (Point N n)) :
    (pointOrders N n).IsCell sigma Finset.univ ↔
      deltaFaceRealization sigma ∈
          (deltaFreudenthalGeometricComplex N n).faces ∧
        sigma.card = n + 1 := by
  rw [isCell_univ_iff_isFreudenthalTopSimplex_of_pos hN]
  constructor
  · intro hsigma
    constructor
    · apply (mem_deltaFreudenthalGeometricComplex_faces_iff_literal
        N n (deltaFaceRealization sigma)).mpr
      have hsigmaNe : sigma.Nonempty := by
        apply Finset.card_pos.mp
        rw [hsigma.card]
        omega
      exact ⟨sigma,
        Or.inr ⟨sigma, hsigma, Finset.Subset.rfl⟩, hsigmaNe, rfl⟩
    · exact hsigma.card
  · rintro ⟨hsigmaFace, hsigmaCard⟩
    obtain ⟨tau, htau, _, htauReal⟩ :=
      (mem_deltaFreudenthalGeometricComplex_faces_iff_literal
        N n (deltaFaceRealization sigma)).mp hsigmaFace
    have htauEq : tau = sigma := by
      apply Finset.image_injective deltaVertexRealization_injective
      exact htauReal
    subst tau
    have hsigmaMem : sigma ∈ freudenthalComplex N n :=
      (mem_freudenthalComplex_iff sigma).mpr htau
    have hsigmaTop : sigma ∈
        (freudenthalComplex N n).topSimplices (n + 1) :=
      Finset.mem_filter.mpr ⟨hsigmaMem, hsigmaCard⟩
    rw [← freudenthalFacets_eq_topSimplices] at hsigmaTop
    exact (mem_freudenthalFacets_iff sigma).mp hsigmaTop

end IntegerSimplex

end BeyondSperner
