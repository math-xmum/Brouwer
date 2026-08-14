import BeyondSperner.Freudenthal.Isomorphism
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-!
# Real affine realization of the change of coordinates

This file begins the geometric layer needed for the literal form of
Corollary 4.9.  It defines the real simplices `Delta` and `Gamma`, the
cumulative-coordinate affine map `s`, and its inverse-on-the-simplex `t`.
The maps are proved inverse on the stated domains; no global affine
equivalence between ambient spaces of different dimensions is asserted.
-/

namespace BeyondSperner

open Classical
open Set

namespace IntegerSimplex

/-- Real points of the dilated standard simplex `Delta`. -/
def IsRealDeltaPoint (N : ℝ) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = N

/-- Real points of the monotone simplex `Gamma`. -/
def IsRealGammaPoint (N : ℝ) {n : ℕ}
    (y : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧
  (∀ i j, i ≤ j → y i ≤ y j) ∧
  ∀ i, y i ≤ N

/-- The real dilated standard simplex as a set. -/
def realDelta (N : ℝ) (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | IsRealDeltaPoint N x}

/-- The real monotone simplex as a set. -/
def realGamma (N : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {y | IsRealGammaPoint N y}

/-- The real dilated standard simplex is convex. -/
theorem convex_realDelta (N : ℝ) (n : ℕ) :
    Convex ℝ (realDelta N n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i))
      (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, hy.2]
    rw [← add_mul, hab, one_mul]

/-- The real monotone simplex is convex. -/
theorem convex_realGamma (N : ℝ) (n : ℕ) :
    Convex ℝ (realGamma N n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i))
      (mul_nonneg hb (hy.1 i))
  constructor
  · intro i j hij
    exact add_le_add (mul_le_mul_of_nonneg_left
      (hx.2.1 i j hij) ha) (mul_le_mul_of_nonneg_left
      (hy.2.1 i j hij) hb)
  · intro i
    calc
      a * x i + b * y i ≤ a * N + b * N :=
        add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 i) ha)
          (mul_le_mul_of_nonneg_left (hy.2.2 i) hb)
      _ = N := by rw [← add_mul, hab, one_mul]

/-- Cumulative coordinates over the reals. -/
def realPrefixMap {n : ℕ} (x : Fin (n + 1) → ℝ) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) ↦ k.val ≤ j.val), x k

private theorem realPrefixMap_eq_sum_Iic {n : ℕ}
    (x : Fin (n + 1) → ℝ) (j : Fin n) :
    realPrefixMap x j = ∑ k ∈ Finset.Iic j.castSucc, x k := by
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    change k.val ≤ j.val ↔ k.val ≤ j.val
    rfl
  · intro k _
    rfl

theorem realPrefixMap_eq_of_val_zero {n : ℕ}
    (x : Fin (n + 1) → ℝ) (q : Fin n) (hq : q.val = 0) :
    realPrefixMap x q = x 0 := by
  rw [realPrefixMap_eq_sum_Iic]
  have hIic : Finset.Iic q.castSucc = {0} := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_singleton]
    constructor
    · intro hk
      apply Fin.ext
      change k.val = 0
      change k.val ≤ q.val at hk
      omega
    · rintro rfl
      exact Fin.zero_le _
  rw [hIic]
  simp

theorem realPrefixMap_eq_prev_add {n : ℕ}
    (x : Fin (n + 1) → ℝ) (q : Fin n) (hq : q.val ≠ 0) :
    realPrefixMap x q =
      realPrefixMap x ⟨q.val - 1, by omega⟩ + x q.castSucc := by
  rw [realPrefixMap_eq_sum_Iic, realPrefixMap_eq_sum_Iic]
  let p : Fin (n + 1) := (⟨q.val - 1, by omega⟩ : Fin n).castSucc
  have hpq : p < q.castSucc := by
    change q.val - 1 < q.val
    exact Nat.sub_lt (Nat.zero_lt_of_ne_zero hq) Nat.one_pos
  have hIic : Finset.Iic q.castSucc = insert q.castSucc (Finset.Iic p) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert]
    constructor
    · intro h
      by_cases hk : k = q.castSucc
      · exact Or.inl hk
      · right
        have hklt : k < q.castSucc := lt_of_le_of_ne h hk
        change k.val ≤ q.val - 1
        have hklt' : k.val < q.val := by
          exact Fin.lt_def.mp hklt
        omega
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.trans hpq.le
  change (∑ k ∈ Finset.Iic q.castSucc, x k) =
    (∑ k ∈ Finset.Iic p, x k) + x q.castSucc
  rw [hIic, Finset.sum_insert]
  · ac_rfl
  · simp [Finset.mem_Iic, not_le_of_gt hpq]

/-- The inverse coordinate formula `t` over the reals. -/
def realGammaCoords (N : ℝ) {n : ℕ}
    (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc y N - Fin.cons 0 y

@[simp]
theorem realGammaCoords_zero (N : ℝ) (y : Fin 0 → ℝ) (k : Fin 1) :
    realGammaCoords N y k = N := by
  have hk : k = 0 := Fin.eq_zero k
  subst k
  have hzeroLast : (0 : Fin 1) = Fin.last 0 := by rfl
  rw [realGammaCoords, Pi.sub_apply, hzeroLast, Fin.snoc_last]
  simp

@[simp]
theorem realGammaCoords_apply_zero {N : ℝ} {n : ℕ}
    (y : Fin (n + 1) → ℝ) :
    realGammaCoords N y 0 = y 0 := by
  simp [realGammaCoords]

theorem realGammaCoords_apply_castSucc_of_ne_zero {N : ℝ} {n : ℕ}
    (y : Fin (n + 1) → ℝ) (q : Fin (n + 1)) (hq : q ≠ 0) :
    realGammaCoords N y q.castSucc =
      y q - y ⟨q.val - 1, by omega⟩ := by
  simp only [realGammaCoords, Pi.sub_apply]
  rw [Fin.snoc_castSucc]
  have hqval : 0 < q.val := by
    exact Nat.pos_of_ne_zero fun h ↦ hq (Fin.ext h)
  have hsucc : q.castSucc =
      (⟨q.val - 1, by omega⟩ : Fin (n + 1)).succ := by
    apply Fin.ext
    simp
    omega
  rw [hsucc, Fin.cons_succ]

@[simp]
theorem realGammaCoords_apply_last {N : ℝ} {n : ℕ}
    (y : Fin (n + 1) → ℝ) :
    realGammaCoords N y (Fin.last (n + 1)) =
      N - y (Fin.last n) := by
  simp [realGammaCoords]

/-- Consecutive differences telescope to the original cumulative
coordinates. -/
theorem realPrefixMap_realGammaCoords {N : ℝ} {n : ℕ}
    (y : Fin n → ℝ) :
    realPrefixMap (realGammaCoords N y) = y := by
  cases n with
  | zero =>
      funext q
      exact Fin.elim0 q
  | succ n =>
      funext q
      induction q using Fin.induction with
      | zero =>
          rw [realPrefixMap_eq_of_val_zero]
          · exact realGammaCoords_apply_zero y
          · rfl
      | succ q ih =>
          rw [realPrefixMap_eq_prev_add]
          · have hprevIndex :
                (⟨q.succ.val - 1, by omega⟩ : Fin (n + 1)) =
                  q.castSucc := by
                apply Fin.ext
                simp
            rw [hprevIndex, ih,
              realGammaCoords_apply_castSucc_of_ne_zero]
            · rw [hprevIndex]
              ring
            · simp
          · simp

/-- The recovered coordinates have total mass `N`. -/
theorem sum_realGammaCoords {N : ℝ} {n : ℕ} (y : Fin n → ℝ) :
    ∑ k, realGammaCoords N y k = N := by
  simp [realGammaCoords, Finset.sum_sub_distrib]

/-- The real cumulative-coordinate map is injective on a fixed affine
coordinate-sum hyperplane. -/
theorem realPrefixMap_injective_on_sum {n : ℕ} {N : ℝ}
    {x z : Fin (n + 1) → ℝ}
    (hx : ∑ i, x i = N) (hz : ∑ i, z i = N)
    (hp : realPrefixMap x = realPrefixMap z) : x = z := by
  have hfront : ∀ q : Fin n, x q.castSucc = z q.castSucc := by
    intro q
    let _ : NeZero n := ⟨Nat.ne_of_gt q.pos⟩
    by_cases hq : q.val = 0
    · have hqeq : q = 0 := Fin.ext hq
      have h0 := congrFun hp q
      rw [realPrefixMap_eq_of_val_zero x q hq,
        realPrefixMap_eq_of_val_zero z q hq] at h0
      simpa [hqeq] using h0
    · let p : Fin n := ⟨q.val - 1, by omega⟩
      have hcurr := congrFun hp q
      have hprev := congrFun hp p
      rw [realPrefixMap_eq_prev_add x q hq,
        realPrefixMap_eq_prev_add z q hq] at hcurr
      have hprev' :
          realPrefixMap x ⟨q.val - 1, by omega⟩ =
            realPrefixMap z ⟨q.val - 1, by omega⟩ := by
        simpa [p] using hprev
      linarith
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨q, rfl⟩ | rfl
  · exact hfront q
  · have hsumFront : (∑ q : Fin n, x q.castSucc) =
        ∑ q : Fin n, z q.castSucc := by
      apply Finset.sum_congr rfl
      intro q _
      exact hfront q
    have hx' := hx
    have hz' := hz
    rw [Fin.sum_univ_castSucc] at hx' hz'
    linarith

/-- The formula `t(s(x)) = x` on the affine hyperplane containing
`Delta`. -/
theorem realGammaCoords_realPrefixMap {N : ℝ} {n : ℕ}
    {x : Fin (n + 1) → ℝ} (hx : ∑ i, x i = N) :
    realGammaCoords N (realPrefixMap x) = x := by
  apply realPrefixMap_injective_on_sum (sum_realGammaCoords _) hx
  exact realPrefixMap_realGammaCoords _

/-- The map `s` sends `Delta` into `Gamma`. -/
theorem realPrefixMap_isRealGammaPoint {N : ℝ} {n : ℕ}
    {x : Fin (n + 1) → ℝ} (hx : IsRealDeltaPoint N x) :
    IsRealGammaPoint N (realPrefixMap x) := by
  constructor
  · intro i
    exact Finset.sum_nonneg fun k _ ↦ hx.1 k
  constructor
  · intro i j hij
    let Si : Finset (Fin (n + 1)) :=
      Finset.univ.filter fun k : Fin (n + 1) ↦ k.val ≤ i.val
    let Sj : Finset (Fin (n + 1)) :=
      Finset.univ.filter fun k : Fin (n + 1) ↦ k.val ≤ j.val
    have hsub : Si ⊆ Sj := by
      intro k hk
      simp only [Si, Sj, Finset.mem_filter,
        Finset.mem_univ, true_and] at hk ⊢
      exact hk.trans hij
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ ↦ hx.1 k)
  · intro i
    have hsub :
        (Finset.univ.filter fun k : Fin (n + 1) ↦ k.val ≤ i.val) ⊆
          (Finset.univ : Finset (Fin (n + 1))) :=
      Finset.filter_subset _ _
    have hle : realPrefixMap x i ≤ ∑ k, x k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ ↦ hx.1 k)
    simpa [hx.2] using hle

/-- The inverse formula `t` sends `Gamma` into `Delta`. -/
theorem realGammaCoords_isRealDeltaPoint {N : ℝ} {n : ℕ}
    {y : Fin n → ℝ} (hN : 0 ≤ N) (hy : IsRealGammaPoint N y) :
    IsRealDeltaPoint N (realGammaCoords N y) := by
  constructor
  · cases n with
    | zero =>
        intro k
        rw [realGammaCoords_zero]
        exact hN
    | succ n =>
        intro k
        by_cases hkZero : k = 0
        · subst k
          simpa using hy.1 0
        have hkPos : 0 < k := Fin.pos_iff_ne_zero.mpr hkZero
        rcases Fin.eq_castSucc_or_eq_last k with ⟨q, rfl⟩ | rfl
        · rw [realGammaCoords_apply_castSucc_of_ne_zero]
          · exact sub_nonneg.mpr (hy.2.1 _ _ (by
              apply Fin.le_iff_val_le_val.mpr
              simp))
          · exact Fin.ne_of_val_ne (by simpa using hkPos.ne')
        · rw [realGammaCoords_apply_last]
          exact sub_nonneg.mpr (hy.2.2 (Fin.last n))
  · exact sum_realGammaCoords y

/-- The real change of coordinates as a bijection between the two simplex
subtypes. -/
noncomputable def realDeltaGammaEquiv (N : ℝ) (hN : 0 ≤ N) (n : ℕ) :
    {x : Fin (n + 1) → ℝ // IsRealDeltaPoint N x} ≃
      {y : Fin n → ℝ // IsRealGammaPoint N y} where
  toFun x := ⟨realPrefixMap x.1,
    realPrefixMap_isRealGammaPoint x.2⟩
  invFun y := ⟨realGammaCoords N y.1,
    realGammaCoords_isRealDeltaPoint hN y.2⟩
  left_inv x := Subtype.ext (realGammaCoords_realPrefixMap x.2.2)
  right_inv y := Subtype.ext (realPrefixMap_realGammaCoords y.1)

/-- The cumulative-coordinate linear map on the ambient real vector
spaces. -/
def realPrefixLinearMap (n : ℕ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := realPrefixMap
  map_add' x z := by
    funext j
    simp [realPrefixMap, Finset.sum_add_distrib]
  map_smul' c x := by
    funext j
    simp [realPrefixMap, Finset.mul_sum]

/-- The linear part of `t`; the constant `N` occurs only in its affine
translation. -/
def realGammaDifferenceLinearMap (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun y := Fin.snoc y 0 - Fin.cons 0 y
  map_add' y z := by
    have hsnoc : Fin.snoc (y + z) (0 : ℝ) =
        (Fin.snoc y (0 : ℝ) : Fin (n + 1) → ℝ) +
          Fin.snoc z (0 : ℝ) := by
      funext k
      cases k using Fin.lastCases <;> simp
    have hcons : Fin.cons (0 : ℝ) (y + z) =
        (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) +
          Fin.cons (0 : ℝ) z := by
      funext k
      cases k using Fin.cases <;> simp
    funext k
    change
      ((Fin.snoc (y + z) (0 : ℝ) : Fin (n + 1) → ℝ) k -
          (Fin.cons (0 : ℝ) (y + z) : Fin (n + 1) → ℝ) k) =
        ((Fin.snoc y (0 : ℝ) : Fin (n + 1) → ℝ) k -
            (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) k) +
          ((Fin.snoc z (0 : ℝ) : Fin (n + 1) → ℝ) k -
            (Fin.cons (0 : ℝ) z : Fin (n + 1) → ℝ) k)
    rw [congrFun hsnoc k, congrFun hcons k]
    simp
    ring
  map_smul' c y := by
    have hsnoc : Fin.snoc (c • y) (0 : ℝ) =
        c • (Fin.snoc y (0 : ℝ) : Fin (n + 1) → ℝ) := by
      funext k
      cases k using Fin.lastCases <;> simp
    have hcons : Fin.cons (0 : ℝ) (c • y) =
        c • (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) := by
      funext k
      cases k using Fin.cases <;> simp
    funext k
    change
      ((Fin.snoc (c • y) (0 : ℝ) : Fin (n + 1) → ℝ) k -
          (Fin.cons (0 : ℝ) (c • y) : Fin (n + 1) → ℝ) k) =
        c * ((Fin.snoc y (0 : ℝ) : Fin (n + 1) → ℝ) k -
          (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) k)
    rw [congrFun hsnoc k, congrFun hcons k]
    simp
    ring

/-- The affine map `s : R^(n+1) -> R^n`. -/
def realDeltaToGammaAffineMap (n : ℕ) :
    (Fin (n + 1) → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
  (realPrefixLinearMap n).toAffineMap

/-- The affine map `t : R^n -> R^(n+1)` with remaining mass in its final
coordinate. -/
def realGammaToDeltaAffineMap (N : ℝ) (n : ℕ) :
    (Fin n → ℝ) →ᵃ[ℝ] (Fin (n + 1) → ℝ) where
  toFun := realGammaCoords N
  linear := realGammaDifferenceLinearMap n
  map_vadd' y v := by
    have hsnoc : Fin.snoc (v + y) N =
        (Fin.snoc v (0 : ℝ) : Fin (n + 1) → ℝ) +
          Fin.snoc y N := by
      funext k
      cases k using Fin.lastCases <;> simp
    have hcons : Fin.cons (0 : ℝ) (v + y) =
        (Fin.cons (0 : ℝ) v : Fin (n + 1) → ℝ) +
          Fin.cons (0 : ℝ) y := by
      funext k
      cases k using Fin.cases <;> simp
    funext k
    change
      ((Fin.snoc (v + y) N : Fin (n + 1) → ℝ) k -
          (Fin.cons (0 : ℝ) (v + y) : Fin (n + 1) → ℝ) k) =
        ((Fin.snoc v (0 : ℝ) : Fin (n + 1) → ℝ) k -
            (Fin.cons (0 : ℝ) v : Fin (n + 1) → ℝ) k) +
          ((Fin.snoc y N : Fin (n + 1) → ℝ) k -
            (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) k)
    rw [congrFun hsnoc k, congrFun hcons k]
    simp
    ring

@[simp]
theorem realDeltaToGammaAffineMap_apply {n : ℕ}
    (x : Fin (n + 1) → ℝ) :
    realDeltaToGammaAffineMap n x = realPrefixMap x := rfl

@[simp]
theorem realGammaToDeltaAffineMap_apply {N : ℝ} {n : ℕ}
    (y : Fin n → ℝ) :
    realGammaToDeltaAffineMap N n y = realGammaCoords N y := rfl

theorem realDeltaToGammaAffineMap_image_delta (N : ℝ) (hN : 0 ≤ N)
    (n : ℕ) :
    realDeltaToGammaAffineMap n '' realDelta N n = realGamma N n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact realPrefixMap_isRealGammaPoint hx
  · intro hy
    refine ⟨realGammaCoords N y,
      realGammaCoords_isRealDeltaPoint hN hy, ?_⟩
    exact realPrefixMap_realGammaCoords y

theorem realGammaToDeltaAffineMap_image_gamma (N : ℝ) (hN : 0 ≤ N)
    (n : ℕ) :
    realGammaToDeltaAffineMap N n '' realGamma N n = realDelta N n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact realGammaCoords_isRealDeltaPoint hN hy
  · intro hx
    refine ⟨realPrefixMap x,
      realPrefixMap_isRealGammaPoint hx, ?_⟩
    exact realGammaCoords_realPrefixMap hx.2

/-- Although `t` is not a bijection between the ambient spaces, it is
globally injective. -/
theorem realGammaToDeltaAffineMap_injective (N : ℝ) (n : ℕ) :
    Function.Injective (realGammaToDeltaAffineMap N n) := by
  intro y z h
  calc
    y = realPrefixMap (realGammaCoords N y) :=
      (realPrefixMap_realGammaCoords y).symm
    _ = realPrefixMap (realGammaCoords N z) := congrArg realPrefixMap h
    _ = z := realPrefixMap_realGammaCoords z

/-- Real realization of an integer point of `Delta`. -/
def deltaVertexRealization {N n : ℕ}
    (a : Point N n) : Fin (n + 1) → ℝ :=
  fun i ↦ (a.1 i).val

/-- Real realization of an integer point of `Gamma`. -/
def gammaVertexRealization {N n : ℕ}
    (y : GammaPoint N n) : Fin n → ℝ :=
  fun i ↦ y.1 i

/-- Distinct integer vertices of `Delta` remain distinct in the real
realization. -/
theorem deltaVertexRealization_injective {N n : ℕ} :
    Function.Injective
      (deltaVertexRealization : Point N n → Fin (n + 1) → ℝ) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change (((a.1 i).val : ℕ) : ℝ) = (((b.1 i).val : ℕ) : ℝ) at hi
  exact_mod_cast hi

/-- Distinct integer vertices of `Gamma` remain distinct in the real
realization. -/
theorem gammaVertexRealization_injective {N n : ℕ} :
    Function.Injective
      (gammaVertexRealization : GammaPoint N n → Fin n → ℝ) := by
  intro y z h
  apply Subtype.ext
  funext i
  have hi := congrFun h i
  change ((y.1 i : ℤ) : ℝ) = ((z.1 i : ℤ) : ℝ) at hi
  exact_mod_cast hi

/-- Real vertex set attached to a finite abstract face in `Gamma`. -/
noncomputable def gammaFaceRealization {N n : ℕ}
    (rho : Finset (GammaPoint N n)) : Finset (Fin n → ℝ) :=
  rho.image gammaVertexRealization

/-- Real vertex set attached to a finite abstract face in `Delta`. -/
noncomputable def deltaFaceRealization {N n : ℕ}
    (rho : Finset (Point N n)) : Finset (Fin (n + 1) → ℝ) :=
  rho.image deltaVertexRealization

@[simp]
theorem card_gammaFaceRealization {N n : ℕ}
    (rho : Finset (GammaPoint N n)) :
    (gammaFaceRealization rho).card = rho.card := by
  exact Finset.card_image_iff.mpr
    gammaVertexRealization_injective.injOn

@[simp]
theorem card_deltaFaceRealization {N n : ℕ}
    (rho : Finset (Point N n)) :
    (deltaFaceRealization rho).card = rho.card := by
  exact Finset.card_image_iff.mpr
    deltaVertexRealization_injective.injOn

@[simp]
theorem gammaFaceRealization_empty {N n : ℕ} :
    gammaFaceRealization (N := N) (n := n) ∅ = ∅ := by
  simp [gammaFaceRealization]

@[simp]
theorem deltaFaceRealization_empty {N n : ℕ} :
    deltaFaceRealization (N := N) (n := n) ∅ = ∅ := by
  simp [deltaFaceRealization]

theorem gammaFaceRealization_mono {N n : ℕ}
    {rho sigma : Finset (GammaPoint N n)} (h : rho ⊆ sigma) :
    gammaFaceRealization rho ⊆ gammaFaceRealization sigma :=
  Finset.image_mono _ h

theorem deltaFaceRealization_mono {N n : ℕ}
    {rho sigma : Finset (Point N n)} (h : rho ⊆ sigma) :
    deltaFaceRealization rho ⊆ deltaFaceRealization sigma :=
  Finset.image_mono _ h

/-- Injectivity of vertex realization makes it commute with finite
intersections exactly. -/
theorem gammaFaceRealization_inter {N n : ℕ}
    (rho sigma : Finset (GammaPoint N n)) :
    gammaFaceRealization (rho ∩ sigma) =
      gammaFaceRealization rho ∩ gammaFaceRealization sigma := by
  exact Finset.image_inter rho sigma gammaVertexRealization_injective

/-- The corresponding exact intersection identity on `Delta` vertices. -/
theorem deltaFaceRealization_inter {N n : ℕ}
    (rho sigma : Finset (Point N n)) :
    deltaFaceRealization (rho ∩ sigma) =
      deltaFaceRealization rho ∩ deltaFaceRealization sigma := by
  exact Finset.image_inter rho sigma deltaVertexRealization_injective

theorem deltaVertexRealization_isRealDeltaPoint {N n : ℕ}
    (a : Point N n) :
    IsRealDeltaPoint (N : ℝ) (deltaVertexRealization a) := by
  constructor
  · intro i
    exact Nat.cast_nonneg _
  · simpa only [deltaVertexRealization, Nat.cast_sum] using
      congrArg (fun m : ℕ ↦ (m : ℝ)) a.2

theorem gammaVertexRealization_isRealGammaPoint {N n : ℕ}
    (y : GammaPoint N n) :
    IsRealGammaPoint (N : ℝ) (gammaVertexRealization y) := by
  rcases y.2 with ⟨hzero, hmono, htop⟩
  constructor
  · intro i
    change (0 : ℝ) ≤ (y.1 i : ℝ)
    exact_mod_cast hzero i
  constructor
  · intro i j hij
    change (y.1 i : ℝ) ≤ (y.1 j : ℝ)
    exact_mod_cast hmono i j hij
  · intro i
    change (y.1 i : ℝ) ≤ (N : ℝ)
    exact_mod_cast htop i

/-- The integer equivalence `pointGammaEquiv` is the restriction of the
real affine map `s` to integer vertices. -/
theorem realPrefixMap_deltaVertexRealization {N n : ℕ}
    (a : Point N n) :
    realPrefixMap (deltaVertexRealization a) =
      gammaVertexRealization ((pointGammaEquiv N n) a) := by
  funext j
  change realPrefixMap (deltaVertexRealization a) j =
    ((pointPrefix a j : ℤ) : ℝ)
  unfold realPrefixMap deltaVertexRealization pointPrefix prefixMap pointCoords
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  norm_num

/-- On integer vertices, the real affine inverse `t` agrees with the inverse
of `pointGammaEquiv`. -/
theorem realGammaCoords_gammaVertexRealization {N n : ℕ}
    (y : GammaPoint N n) :
    realGammaCoords (N : ℝ) (gammaVertexRealization y) =
      deltaVertexRealization ((pointGammaEquiv N n).symm y) := by
  apply realPrefixMap_injective_on_sum
  · exact sum_realGammaCoords _
  · exact (deltaVertexRealization_isRealDeltaPoint _).2
  · rw [realPrefixMap_realGammaCoords,
      realPrefixMap_deltaVertexRealization]
    simp

/-- Applying the real affine map `t` to a realized finite vertex set in
`Gamma` gives exactly the realization of its inverse-relabeling in
`Delta`. -/
theorem image_realGammaToDelta_gammaFaceRealization {N n : ℕ}
    (rho : Finset (GammaPoint N n)) :
    (gammaFaceRealization rho).image
        (realGammaToDeltaAffineMap (N : ℝ) n) =
      deltaFaceRealization (rho.image (pointGammaEquiv N n).symm) := by
  ext x
  simp only [gammaFaceRealization, deltaFaceRealization,
    Finset.mem_image]
  constructor
  · rintro ⟨yReal, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(pointGammaEquiv N n).symm y,
      ⟨y, hy, rfl⟩, ?_⟩
    simpa using (realGammaCoords_gammaVertexRealization y).symm
  · rintro ⟨a, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨gammaVertexRealization y, ⟨y, hy, rfl⟩, ?_⟩
    simpa using realGammaCoords_gammaVertexRealization y

/-- In particular, on a source face the vertex-set transport is the
literal affine image claimed in Corollary 4.9. -/
theorem image_realGammaToDelta_gammaFaceRealization_image_equiv
    {N n : ℕ} (rho : Finset (Point N n)) :
    (gammaFaceRealization (rho.image (pointGammaEquiv N n))).image
        (realGammaToDeltaAffineMap (N : ℝ) n) =
      deltaFaceRealization rho := by
  rw [image_realGammaToDelta_gammaFaceRealization]
  congr 1
  ext a
  simp

/-- Affine maps carry convex hulls to convex hulls.  This specialization is
the transport identity used to move Freudenthal simplices from `Gamma` to
`Delta`. -/
theorem realGammaToDeltaAffineMap_image_convexHull {N : ℝ} {n : ℕ}
    (s : Set (Fin n → ℝ)) :
    realGammaToDeltaAffineMap N n '' convexHull ℝ s =
      convexHull ℝ (realGammaToDeltaAffineMap N n '' s) :=
  AffineMap.image_convexHull _ _

end IntegerSimplex

end BeyondSperner
