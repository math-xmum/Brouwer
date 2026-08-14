import BeyondSperner.Orders.LinearOrders
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.PiLex
import Mathlib.Tactic

/-!
# Integer points in a simplex

The arithmetic and coordinate-change layer of Section 4.  Coordinates of the
`n`-simplex are indexed by `Fin (n+1)`.  An index `i : Fin n` represents the
paper's coordinate `i+1`; the corresponding transfer decreases coordinate
`i+1` and increases coordinate `i`.
-/

namespace BeyondSperner

open Classical

namespace IntegerSimplex

/-- Integer points of the dilated standard simplex. -/
def IsPoint (N : ℤ) {n : ℕ} (a : Fin (n + 1) → ℤ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ ∑ i, a i = N

/-- Coordinates read cyclically beginning with `i`. -/
def cyclicKey {n : ℕ} (i : Fin (n + 1)) (a : Fin (n + 1) → ℤ) :
    Πₗ _ : Fin (n + 1), ℤ :=
  toLex fun k ↦ a (finCycle i k)

theorem cyclicKey_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (cyclicKey i) := by
  intro a b h
  funext j
  let k : Fin (n + 1) := (finCycle i).symm j
  have hk := congrArg (fun z : Πₗ _ : Fin (n + 1), ℤ ↦ z k) h
  simpa [cyclicKey, k] using hk

private theorem finCycle_succ {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    finCycle i k.succ = finCycle (finRotate _ i) k.castSucc := by
  simp only [finCycle_apply, finRotate_apply]
  rw [← Fin.coeSucc_eq_succ]
  ac_rfl

private theorem finCycle_next_last {n : ℕ} (i : Fin (n + 1)) :
    finCycle (finRotate _ i) (Fin.last n) = i := by
  have hlast : Fin.last n = (-1 : Fin (n + 1)) := by
    apply Fin.ext
    simp [Fin.coe_neg_one]
  simp only [finCycle_apply, finRotate_apply, hlast]
  abel

private theorem finRotate_finCycle {n : ℕ} (i k : Fin (n + 1)) :
    finRotate _ (finCycle i k) = finCycle (finRotate _ i) k := by
  simp only [finCycle_apply, finRotate_apply]
  ac_rfl

/-- If all compared vectors have the same `i`-th coordinate, deleting that
common first coordinate identifies the `i`-order with the next cyclic order. -/
theorem cyclicKey_lt_iff_next_of_eq {n : ℕ} (i : Fin (n + 1))
    {a b : Fin (n + 1) → ℤ} (hi : a i = b i) :
    cyclicKey i a < cyclicKey i b ↔
      cyclicKey (finRotate _ i) a < cyclicKey (finRotate _ i) b := by
  constructor
  · rintro ⟨k, hkprev, hklt⟩
    revert hkprev hklt
    refine Fin.cases ?_ (fun q hkprev hklt ↦ ?_) k
    · intro _ hklt
      have : a i < b i := by simpa [cyclicKey] using hklt
      exact (lt_irrefl _ (hi ▸ this)).elim

    · refine ⟨q.castSucc, fun r hr ↦ ?_, ?_⟩
      · let s : Fin n := ⟨r.val, lt_of_lt_of_le hr q.isLt.le⟩
        have hrs : r = s.castSucc := Fin.ext rfl
        have hsq : s < q := hr
        have hsucc := hkprev s.succ (Fin.succ_lt_succ_iff.mpr hsq)
        change a (finCycle i s.succ) = b (finCycle i s.succ) at hsucc
        rw [finCycle_succ] at hsucc
        change a (finCycle (finRotate _ i) r) =
          b (finCycle (finRotate _ i) r)
        rw [hrs]
        exact hsucc
      · change a (finCycle i q.succ) < b (finCycle i q.succ) at hklt
        rw [finCycle_succ] at hklt
        exact hklt
  · rintro ⟨k, hkprev, hklt⟩
    rcases Fin.eq_castSucc_or_eq_last k with ⟨q, rfl⟩ | rfl
    · refine ⟨q.succ, fun r hr ↦ ?_, ?_⟩
      · revert hr
        refine Fin.cases ?_ (fun s hr ↦ ?_) r
        · intro _
          simpa [cyclicKey] using hi
        · have hs : s < q := by
            change s.val + 1 < q.val + 1 at hr
            omega
          have hprev := hkprev s.castSucc (by exact hs)
          change a (finCycle (finRotate _ i) s.castSucc) =
            b (finCycle (finRotate _ i) s.castSucc) at hprev
          rw [← finCycle_succ] at hprev
          exact hprev
      · change a (finCycle (finRotate _ i) q.castSucc) <
          b (finCycle (finRotate _ i) q.castSucc) at hklt
        rw [← finCycle_succ] at hklt
        exact hklt
    · change a (finCycle (finRotate _ i) (Fin.last n)) <
        b (finCycle (finRotate _ i) (Fin.last n)) at hklt
      rw [finCycle_next_last] at hklt
      have : a i < b i := hklt
      exact (lt_irrefl _ (hi ▸ this)).elim

/-- The paper's cyclic transfer `S_i`: one unit moves from coordinate `i`
to the coordinate immediately preceding it in the cyclic order. -/
def cyclicStep {n : ℕ} (i : Fin (n + 1))
    (a : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  a + Pi.single ((finRotate _).symm i) 1 - Pi.single i 1

@[simp]
theorem cyclicStep_apply {n : ℕ} (i : Fin (n + 1))
    (a : Fin (n + 1) → ℤ) (k : Fin (n + 1)) :
    cyclicStep i a k =
      a k + (if k = (finRotate _).symm i then 1 else 0) -
        (if k = i then 1 else 0) := by
  simp [cyclicStep, Pi.single_apply]

private theorem finRotate_ne_self_of_pos {n : ℕ} (hn : 0 < n)
    (i : Fin (n + 1)) : finRotate _ i ≠ i := by
  by_cases hilast : i = Fin.last n
  · subst i
    rw [finRotate_last]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  · exact ne_of_gt ((lt_finRotate_iff_ne_last i).2 hilast)

private theorem finRotate_symm_ne_self_of_pos {n : ℕ} (hn : 0 < n)
    (i : Fin (n + 1)) : (finRotate _).symm i ≠ i := by
  intro h
  have := congrArg (finRotate (n + 1)) h
  simp only [Equiv.apply_symm_apply] at this
  exact finRotate_ne_self_of_pos hn i this.symm

/-- Lemma 4.1 in cyclicly invariant form.  Every order other than the
coordinate from which mass is removed sees the positive change first. -/
theorem cyclicKey_lt_cyclicStep_of_ne {n : ℕ} (hn : 0 < n)
    (i j : Fin (n + 1)) (hji : j ≠ i) (a : Fin (n + 1) → ℤ) :
    cyclicKey j a < cyclicKey j (cyclicStep i a) := by
  let p : Fin (n + 1) := (finRotate _).symm i
  let k : Fin (n + 1) := (finCycle j).symm p
  have hcyclek : finCycle j k = p := (finCycle j).apply_symm_apply p
  have hklast : k ≠ Fin.last n := by
    intro hk
    have hij : i = j := calc
      i = finRotate _ p := by simp [p]
      _ = finRotate _ (finCycle j k) := by rw [hcyclek]
      _ = finCycle (finRotate _ j) k := finRotate_finCycle j k
      _ = finCycle (finRotate _ j) (Fin.last n) := by rw [hk]
      _ = j := finCycle_next_last j
    exact hji hij.symm
  obtain ⟨q, hq⟩ := Fin.eq_castSucc_of_ne_last hklast
  have hcycleq : finCycle j q.castSucc = p := by rw [hq, hcyclek]
  have hcycleSucc : finCycle j q.succ = i := calc
    finCycle j q.succ = finCycle (finRotate _ j) q.castSucc := finCycle_succ j q
    _ = finRotate _ (finCycle j q.castSucc) := (finRotate_finCycle j q.castSucc).symm
    _ = finRotate _ p := by rw [hcycleq]
    _ = i := by simp [p]
  have hpi : p ≠ i := finRotate_symm_ne_self_of_pos hn i
  refine ⟨q.castSucc, fun r hr ↦ ?_, ?_⟩
  · have hrq : r ≠ q.castSucc := ne_of_lt hr
    have hrs : r ≠ q.succ := by
      intro hrs
      subst r
      exact (not_lt_of_ge q.castSucc_le_succ) hr
    have hrp : finCycle j r ≠ p := by
      intro h
      exact hrq ((finCycle j).injective (h.trans hcycleq.symm))
    have hri : finCycle j r ≠ i := by
      intro h
      exact hrs ((finCycle j).injective (h.trans hcycleSucc.symm))
    change a (finCycle j r) = cyclicStep i a (finCycle j r)
    rw [cyclicStep_apply, if_neg (by simpa [p] using hrp), if_neg hri]
    ring
  · change a (finCycle j q.castSucc) < cyclicStep i a (finCycle j q.castSucc)
    rw [hcycleq]
    rw [cyclicStep_apply, if_pos (by rfl), if_neg hpi]
    omega

/-- A cyclic transfer preserves the coordinate sum. -/
theorem sum_cyclicStep {n : ℕ} (i : Fin (n + 1))
    (a : Fin (n + 1) → ℤ) :
    ∑ k, cyclicStep i a k = ∑ k, a k := by
  simp [cyclicStep, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- A cyclic transfer stays in the integer simplex when its source
coordinate is positive. -/
theorem cyclicStep_isPoint {n : ℕ} (hn : 0 < n) {N : ℤ}
    (i : Fin (n + 1)) (a : Fin (n + 1) → ℤ)
    (ha : IsPoint N a) (hpos : 0 < a i) :
    IsPoint N (cyclicStep i a) := by
  have hpi : (finRotate _).symm i ≠ i :=
    finRotate_symm_ne_self_of_pos hn i
  constructor
  · intro k
    by_cases hkp : k = (finRotate _).symm i
    · subst k
      have hnonneg := ha.1 ((finRotate _).symm i)
      rw [cyclicStep_apply, if_pos rfl, if_neg hpi]
      omega
    · by_cases hki : k = i
      · subst k
        rw [cyclicStep_apply, if_neg hpi.symm, if_pos rfl]
        omega
      · rw [cyclicStep_apply, if_neg hkp, if_neg hki]
        simpa using ha.1 k
  · rw [sum_cyclicStep, ha.2]

/-- Move one unit from coordinate `k` to a distinct coordinate `j`. -/
def coordinateTransfer {n : ℕ} (k j : Fin (n + 1))
    (a : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  a + Pi.single j 1 - Pi.single k 1

@[simp]
theorem coordinateTransfer_apply {n : ℕ} (k j : Fin (n + 1))
    (a : Fin (n + 1) → ℤ) (r : Fin (n + 1)) :
    coordinateTransfer k j a r =
      a r + (if r = j then 1 else 0) - (if r = k then 1 else 0) := by
  simp [coordinateTransfer, Pi.single_apply]

theorem coordinateTransfer_isPoint {n : ℕ} {N : ℤ}
    {k j : Fin (n + 1)} (hjk : j ≠ k) (a : Fin (n + 1) → ℤ)
    (ha : IsPoint N a) (hpos : 0 < a k) :
    IsPoint N (coordinateTransfer k j a) := by
  constructor
  · intro r
    by_cases hrj : r = j
    · subst r
      rw [coordinateTransfer_apply, if_pos rfl, if_neg hjk]
      have := ha.1 j
      omega
    · by_cases hrk : r = k
      · subst r
        rw [coordinateTransfer_apply, if_neg hjk.symm, if_pos rfl]
        omega
      · rw [coordinateTransfer_apply, if_neg hrj, if_neg hrk]
        simpa using ha.1 r
  · simp [coordinateTransfer, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ha.2]

/-- If `i` occurs no later than `j` after `k` in cyclic order and does not
equal `k`, then the `i`-lexicographic order sees the increase at `j` before
the decrease at `k`. -/
private theorem cyclicKey_lt_coordinateTransfer_of_pos_le {n : ℕ}
    (k j i : Fin (n + 1))
    (hipos : 0 < ((finCycle k).symm i).val)
    (hposle : ((finCycle k).symm i).val ≤ ((finCycle k).symm j).val)
    (a : Fin (n + 1) → ℤ) :
    cyclicKey i a < cyclicKey i (coordinateTransfer k j a) := by
  let pi : Fin (n + 1) := (finCycle k).symm i
  let pj : Fin (n + 1) := (finCycle k).symm j
  let q : Fin (n + 1) := ⟨pj.val - pi.val, by omega⟩
  let s : Fin (n + 1) := ⟨n + 1 - pi.val, by omega⟩
  have hpipos : 0 < pi.val := by simpa [pi] using hipos
  have hpile : pi.val ≤ pj.val := by simpa [pi, pj] using hposle
  have hcyclePi : finCycle k pi = i := (finCycle k).apply_symm_apply i
  have hcyclePj : finCycle k pj = j := (finCycle k).apply_symm_apply j
  have hcomp : ∀ r : Fin (n + 1),
      finCycle i r = finCycle k (pi + r) := by
    intro r
    rw [← hcyclePi]
    simp only [finCycle_apply]
    ac_rfl
  have hpiq : pi + q = pj := by
    apply Fin.ext
    change (pi.val + q.val) % (n + 1) = pj.val
    rw [Nat.mod_eq_of_lt (by simp [q]; omega)]
    simp only [q]
    omega
  have hpis : pi + s = 0 := by
    apply Fin.ext
    change (pi.val + s.val) % (n + 1) = 0
    have heq : pi.val + s.val = n + 1 := by simp [s]
    rw [heq, Nat.mod_self]
  have hcycleQ : finCycle i q = j := by
    rw [hcomp, hpiq, hcyclePj]
  have hcycleS : finCycle i s = k := by
    rw [hcomp, hpis]
    simp [finCycle_apply]
  have hqs : q < s := by
    change pj.val - pi.val < n + 1 - pi.val
    omega
  have hjk : j ≠ k := by
    intro h
    have hp : pj = 0 := by
      apply (finCycle k).injective
      rw [hcyclePj, h]
      simp [finCycle_apply]
    have : pj.val = 0 := congrArg Fin.val hp
    omega
  refine ⟨q, fun r hr ↦ ?_, ?_⟩
  · have hrq : r ≠ q := ne_of_lt hr
    have hrs : r ≠ s := by
      intro hrs
      subst r
      exact (not_lt_of_ge hqs.le) hr
    have hrj : finCycle i r ≠ j := by
      intro h
      exact hrq ((finCycle i).injective (h.trans hcycleQ.symm))
    have hrk : finCycle i r ≠ k := by
      intro h
      exact hrs ((finCycle i).injective (h.trans hcycleS.symm))
    change a (finCycle i r) = coordinateTransfer k j a (finCycle i r)
    rw [coordinateTransfer_apply, if_neg hrj, if_neg hrk]
    ring
  · change a (finCycle i q) < coordinateTransfer k j a (finCycle i q)
    rw [hcycleQ, coordinateTransfer_apply, if_pos rfl, if_neg hjk]
    omega

/-- The cyclic lexicographic orders of Section 4, transported to an arbitrary
finite collection of distinct coordinate vectors. -/
noncomputable def cyclicOrders {n : ℕ} {V : Type*}
    (p : V ↪ (Fin (n + 1) → ℤ)) :
    IndexedLinearOrders (Fin (n + 1)) V where
  order i := LinearOrder.lift' (cyclicKey i ∘ p)
    ((cyclicKey_injective i).comp p.injective)

/-- Each cyclic lexicographic order refines its first coordinate. -/
theorem cyclicOrders_refines {n : ℕ} {V : Type*}
    (p : V ↪ (Fin (n + 1) → ℤ)) (i : Fin (n + 1)) {x y : V}
    (hxy : p x i < p y i) :
    ((cyclicOrders p) i).lt x y := by
  change cyclicKey i (p x) < cyclicKey i (p y)
  exact ⟨0, by
    intro j hj
    exact (Fin.not_lt_zero j hj).elim, by simpa [cyclicKey] using hxy⟩

/-- The finite carrier `D` of nonnegative integer points with coordinate sum
`N`.  Coordinates are bounded by `N` in the type itself. -/
def Point (N n : ℕ) :=
  {a : Fin (n + 1) → Fin (N + 1) // ∑ i, (a i).val = N}

instance (N n : ℕ) : Fintype (Point N n) := Subtype.fintype _

noncomputable instance (N n : ℕ) : DecidableEq (Point N n) := Classical.decEq _

/-- Integer-coordinate realization of `D`. -/
def pointCoords {N n : ℕ} (a : Point N n) : Fin (n + 1) → ℤ :=
  fun i ↦ ((a.1 i).val : ℤ)

theorem pointCoords_injective {N n : ℕ} :
    Function.Injective (pointCoords : Point N n → Fin (n + 1) → ℤ) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact Int.ofNat_injective (congrFun h i)

/-- The canonical embedding of the finite integer simplex into its coordinate
space. -/
def pointEmbedding (N n : ℕ) : Point N n ↪ (Fin (n + 1) → ℤ) :=
  ⟨pointCoords, pointCoords_injective⟩

/-- The paper's cyclic lexicographic orders on `D`. -/
noncomputable def pointOrders (N n : ℕ) :
    IndexedLinearOrders (Fin (n + 1)) (Point N n) :=
  cyclicOrders (pointEmbedding N n)

theorem pointCoords_isPoint {N n : ℕ} (a : Point N n) :
    IsPoint (N : ℤ) (pointCoords a) := by
  constructor
  · intro i
    change (0 : ℤ) ≤ ((a.1 i).val : ℤ)
    exact_mod_cast (Nat.zero_le (a.1 i).val)
  · change (∑ i, ((a.1 i).val : ℤ)) = (N : ℤ)
    exact_mod_cast a.2

/-- Every nonnegative integral coordinate vector with sum `N` is represented
by the finite type `Point N n`. -/
def pointOfIsPoint {N n : ℕ} (a : Fin (n + 1) → ℤ)
    (ha : IsPoint (N : ℤ) a) : Point N n := by
  refine ⟨fun i ↦ ⟨(a i).toNat, ?_⟩, ?_⟩
  · have hle : a i ≤ ∑ j, a j :=
      Finset.single_le_sum (fun j _ ↦ ha.1 j) (Finset.mem_univ i)
    rw [ha.2] at hle
    have hcoe : ((a i).toNat : ℤ) = a i := Int.toNat_of_nonneg (ha.1 i)
    omega
  · have hsum : (∑ i, ((a i).toNat : ℤ)) = (N : ℤ) := by
      calc
        ∑ i, ((a i).toNat : ℤ) = ∑ i, a i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Int.toNat_of_nonneg (ha.1 i)
        _ = (N : ℤ) := ha.2
    exact_mod_cast hsum

@[simp]
theorem pointCoords_pointOfIsPoint {N n : ℕ} (a : Fin (n + 1) → ℤ)
    (ha : IsPoint (N : ℤ) a) :
    pointCoords (pointOfIsPoint a ha) = a := by
  funext i
  exact Int.toNat_of_nonneg (ha.1 i)

/-- The finite set of actual integer-simplex points whose coordinate vectors
belong to `S`.  This is useful when a combinatorial construction is first
performed on integer vectors: no vector is silently treated as a point. -/
noncomputable def realizeCoordinateSet (N n : ℕ)
    (S : Finset (Fin (n + 1) → ℤ)) : Finset (Point N n) :=
  Finset.univ.filter fun a ↦ pointCoords a ∈ S

/-- If every vector of `S` satisfies the integer-simplex equations, then
`realizeCoordinateSet` has coordinate image exactly `S`. -/
theorem image_pointCoords_realizeCoordinateSet {N n : ℕ}
    (S : Finset (Fin (n + 1) → ℤ))
    (hS : ∀ x ∈ S, IsPoint (N : ℤ) x) :
    (realizeCoordinateSet N n S).image pointCoords = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp ha).2
  · intro hx
    let a : Point N n := pointOfIsPoint x (hS x hx)
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [show pointCoords a = x by
        exact pointCoords_pointOfIsPoint x (hS x hx)]
      exact hx
    · exact pointCoords_pointOfIsPoint x (hS x hx)

theorem pointOrders_refines {N n : ℕ} (i : Fin (n + 1)) {a b : Point N n}
    (h : pointCoords a i < pointCoords b i) :
    ((pointOrders N n) i).lt a b :=
  cyclicOrders_refines (pointEmbedding N n) i h

/-- Lemma 4.2: in positive dimension, every coordinate varies on a full
dominant cell.  The proof uses both ingredients that matter mathematically:
full cardinality makes the minimum map injective, while equality of one
coordinate identifies two adjacent cyclic lexicographic orders on the cell. -/
theorem exists_pair_coord_ne_of_isCell {N n : ℕ} (hn : 0 < n)
    {σ : Finset (Point N n)}
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) :
    ∃ a ∈ σ, ∃ b ∈ σ, pointCoords a i ≠ pointCoords b i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hcard : σ.card = (d + 1) + 1 := by
    simpa using hcell.2
  have hσ : σ.Nonempty := Finset.card_pos.mp (by omega)
  let m : Fin ((d + 1) + 1) → Point N (d + 1) := fun j ↦
    @Finset.min' (Point N (d + 1)) ((pointOrders N (d + 1)) j) σ hσ
  have himage : σ = Finset.univ.image m := by
    simpa [m] using
      (pointOrders N (d + 1)).eq_image_min_of_isDominant hσ hcell.1
  have himageCard :
      ((Finset.univ : Finset (Fin ((d + 1) + 1))).image m).card =
        (Finset.univ : Finset (Fin ((d + 1) + 1))).card := by
    rw [← himage]
    simpa using hcell.2
  have hminInj : Set.InjOn m
      (Finset.univ : Finset (Fin ((d + 1) + 1))) :=
    Finset.injOn_of_card_image_eq himageCard
  let j : Fin ((d + 1) + 1) := finRotate _ i
  have hij : i ≠ j := by
    by_cases hilast : i = Fin.last (d + 1)
    · subst i
      simp only [j, finRotate_last]
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    · exact ne_of_lt ((lt_finRotate_iff_ne_last i).2 hilast)
  have hmne : m i ≠ m j := fun h ↦
    hij (hminInj (Finset.mem_univ i) (Finset.mem_univ j) h)
  have hmimem : m i ∈ σ := by
    simpa [m] using
      (@Finset.min'_mem (Point N (d + 1))
        ((pointOrders N (d + 1)) i) σ hσ)
  have hmjmem : m j ∈ σ := by
    simpa [m] using
      (@Finset.min'_mem (Point N (d + 1))
        ((pointOrders N (d + 1)) j) σ hσ)
  by_contra! hconst
  have hcoord : pointCoords (m i) i = pointCoords (m j) i :=
    hconst (m i) hmimem (m j) hmjmem
  have hle_i : ((pointOrders N (d + 1)) i).le (m i) (m j) := by
    simpa [m] using
      (@Finset.min'_le (Point N (d + 1))
        ((pointOrders N (d + 1)) i) σ (m j) hmjmem)
  have hlt_i : ((pointOrders N (d + 1)) i).lt (m i) (m j) :=
    by
      let : LinearOrder (Point N (d + 1)) := (pointOrders N (d + 1)) i
      exact lt_of_le_of_ne hle_i hmne
  change cyclicKey i (pointCoords (m i)) <
    cyclicKey i (pointCoords (m j)) at hlt_i
  have hlt_j : cyclicKey j (pointCoords (m i)) <
      cyclicKey j (pointCoords (m j)) := by
    exact (cyclicKey_lt_iff_next_of_eq i hcoord).mp hlt_i
  have hle_j : ((pointOrders N (d + 1)) j).le (m j) (m i) := by
    simpa [m] using
      (@Finset.min'_le (Point N (d + 1))
        ((pointOrders N (d + 1)) j) σ (m i) hmimem)
  change cyclicKey j (pointCoords (m j)) ≤
    cyclicKey j (pointCoords (m i)) at hle_j
  exact (not_le_of_gt hlt_j) hle_j

/-- The directed form of Lemma 4.3: on a full cell, one vertex can exceed
another in any fixed coordinate by at most one. -/
theorem coord_le_add_one_of_isCell {N n : ℕ} (hn : 0 < n)
    {σ : Finset (Point N n)}
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    {a b : Point N n} (haσ : a ∈ σ) (hbσ : b ∈ σ)
    (i : Fin (n + 1)) :
    pointCoords b i ≤ pointCoords a i + 1 := by
  by_contra hle
  have hgap : pointCoords a i + 1 < pointCoords b i := by omega
  have hpos : 0 < pointCoords b i := by
    have := (pointCoords_isPoint a).1 i
    omega
  let hzPoint := cyclicStep_isPoint hn i (pointCoords b)
    (pointCoords_isPoint b) hpos
  let z : Point N n :=
    pointOfIsPoint (cyclicStep i (pointCoords b)) hzPoint
  have hzcoords : pointCoords z = cyclicStep i (pointCoords b) := by
    exact pointCoords_pointOfIsPoint _ _
  obtain ⟨j, _, hj⟩ := hcell.1.2 z
  by_cases hji : j = i
  · subst j
    have hpi : (finRotate _).symm i ≠ i :=
      finRotate_symm_ne_self_of_pos hn i
    have hzi : pointCoords z i = pointCoords b i - 1 := by
      rw [hzcoords, cyclicStep_apply, if_neg hpi.symm, if_pos rfl]
      ring
    have hlt : ((pointOrders N n) i).lt a z :=
      pointOrders_refines i (by omega)
    have hzle := hj a haσ
    change cyclicKey i (pointCoords a) < cyclicKey i (pointCoords z) at hlt
    change cyclicKey i (pointCoords z) ≤ cyclicKey i (pointCoords a) at hzle
    exact (not_le_of_gt hlt) hzle
  · have hlt : ((pointOrders N n) j).lt b z := by
      change cyclicKey j (pointCoords b) < cyclicKey j (pointCoords z)
      rw [hzcoords]
      exact cyclicKey_lt_cyclicStep_of_ne hn i j hji (pointCoords b)
    have hzle := hj b hbσ
    change cyclicKey j (pointCoords b) < cyclicKey j (pointCoords z) at hlt
    change cyclicKey j (pointCoords z) ≤ cyclicKey j (pointCoords b) at hzle
    exact (not_le_of_gt hlt) hzle

/-- Lemma 4.3: every coordinate has range at most one on a full cell. -/
theorem coord_range_of_isCell {N n : ℕ} (hn : 0 < n)
    {σ : Finset (Point N n)}
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    {a b : Point N n} (haσ : a ∈ σ) (hbσ : b ∈ σ)
    (i : Fin (n + 1)) :
    pointCoords a i ≤ pointCoords b i + 1 ∧
      pointCoords b i ≤ pointCoords a i + 1 :=
  ⟨coord_le_add_one_of_isCell hn hcell hbσ haσ i,
    coord_le_add_one_of_isCell hn hcell haσ hbσ i⟩

/-- Lemma 4.7: a `C`-cell is contained in every coordinate face whose
index is missing from `C`. -/
theorem coord_eq_zero_of_isCell_of_not_mem {N n : ℕ}
    {C : Finset (Fin (n + 1))} {σ : Finset (Point N n)}
    (hcell : (pointOrders N n).IsCell σ C)
    {a : Point N n} (haσ : a ∈ σ) {k : Fin (n + 1)} (hkC : k ∉ C) :
    pointCoords a k = 0 := by
  by_contra hzero
  have hposk : 0 < pointCoords a k := by
    have := (pointCoords_isPoint a).1 k
    omega
  let pos : Fin (n + 1) → ℕ := fun i ↦ ((finCycle k).symm i).val
  let P : Finset ℕ := C.image pos
  have hP : P.Nonempty := hcell.1.1.image pos
  let M : ℕ := P.max' hP
  have hMmem : M ∈ P := Finset.max'_mem P hP
  obtain ⟨j, hjC, hjM⟩ := Finset.mem_image.mp hMmem
  have hjk : j ≠ k := fun h ↦ hkC (h ▸ hjC)
  have hposjM : pos j = M := hjM
  have hzPoint : IsPoint (N : ℤ)
      (coordinateTransfer k j (pointCoords a)) :=
    coordinateTransfer_isPoint hjk (pointCoords a)
      (pointCoords_isPoint a) hposk
  let z : Point N n :=
    pointOfIsPoint (coordinateTransfer k j (pointCoords a)) hzPoint
  have hzcoords : pointCoords z = coordinateTransfer k j (pointCoords a) :=
    pointCoords_pointOfIsPoint _ _
  obtain ⟨i, hiC, hzi⟩ := hcell.1.2 z
  have hipos : 0 < ((finCycle k).symm i).val := by
    apply Nat.pos_of_ne_zero
    intro hi0
    have hpre : (finCycle k).symm i = 0 := Fin.ext hi0
    have hik : i = k := calc
      i = finCycle k ((finCycle k).symm i) :=
        ((finCycle k).apply_symm_apply i).symm
      _ = finCycle k 0 := by rw [hpre]
      _ = k := by simp [finCycle_apply]
    exact hkC (hik ▸ hiC)
  have hposle : ((finCycle k).symm i).val ≤
      ((finCycle k).symm j).val := by
    have hiP : pos i ∈ P := Finset.mem_image.mpr ⟨i, hiC, rfl⟩
    have hiM : pos i ≤ M := Finset.le_max' P (pos i) hiP
    change pos i ≤ pos j
    exact hiM.trans_eq hposjM.symm
  have hlt : ((pointOrders N n) i).lt a z := by
    change cyclicKey i (pointCoords a) < cyclicKey i (pointCoords z)
    rw [hzcoords]
    exact cyclicKey_lt_coordinateTransfer_of_pos_le k j i hipos hposle
      (pointCoords a)
  have hzle := hzi a haσ
  change cyclicKey i (pointCoords a) < cyclicKey i (pointCoords z) at hlt
  change cyclicKey i (pointCoords z) ≤ cyclicKey i (pointCoords a) at hzle
  exact (not_le_of_gt hlt) hzle

/-- `D` is nonempty: put all mass in coordinate zero. -/
instance pointNonempty (N n : ℕ) : Nonempty (Point N n) := by
  let a : Fin (n + 1) → Fin (N + 1) := fun i ↦
    if i = 0 then ⟨N, Nat.lt_succ_self N⟩ else 0
  refine ⟨⟨a, ?_⟩⟩
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [a]
  · intro b _ hb
    simp [a, hb]
  · simp

/-- Complex-level form of Lemma 4.7 for an arbitrary index face `C`.
Every vertex of every simplex generated by a `C`-cell has zero coordinates
outside `C`.  The empty-index case is handled from the literal definition of
the associated complex rather than by assuming that `C` is nonempty. -/
theorem coord_eq_zero_of_mem_associatedComplex_of_not_mem
    {N n : ℕ} {C : Finset (Fin (n + 1))}
    {tau : Finset (Point N n)}
    (htau : tau ∈ (pointOrders N n).associatedComplex C)
    {a : Point N n} (ha : a ∈ tau)
    {k : Fin (n + 1)} (hkC : k ∉ C) :
    pointCoords a k = 0 := by
  have hassoc : (pointOrders N n).IsAssociatedSimplex C tau :=
    (Finset.mem_filter.mp htau).2
  by_cases hC : C = ∅
  · rw [IndexedLinearOrders.IsAssociatedSimplex, if_pos hC] at hassoc
    subst tau
    simp at ha
  · rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg hC] at hassoc
    rcases hassoc with hEmpty | ⟨sigma, hcell, htauSub⟩
    · subst tau
      simp at ha
    · exact coord_eq_zero_of_isCell_of_not_mem hcell (htauSub ha) hkC

/-- The operator `S_{i+1}` of Section 4. -/
def step {n : ℕ} (i : Fin n) (a : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  a + Pi.single i.castSucc 1 - Pi.single i.succ 1

@[simp]
theorem step_apply {n : ℕ} (i : Fin n) (a : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) :
    step i a j = a j + (if j = i.castSucc then 1 else 0) -
      (if j = i.succ then 1 else 0) := by
  simp [step, Pi.single_apply]

/-- A transfer preserves the coordinate sum. -/
theorem sum_step {n : ℕ} (i : Fin n) (a : Fin (n + 1) → ℤ) :
    ∑ j, step i a j = ∑ j, a j := by
  simp [step, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- A transfer preserves the integer simplex whenever the coordinate being
decreased is positive. -/
theorem step_isPoint {n : ℕ} {N : ℤ} (i : Fin n) (a : Fin (n + 1) → ℤ)
    (ha : IsPoint N a) (hpos : 0 < a i.succ) : IsPoint N (step i a) := by
  have hne : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
  constructor
  · intro j
    by_cases hjlo : j = i.castSucc
    · subst j
      rw [step_apply]
      simp only [ite_true, if_neg hne]
      have := ha.1 i.castSucc
      omega
    · by_cases hjhi : j = i.succ
      · subst j
        rw [step_apply]
        simp only [if_neg hne.symm, ite_true]
        omega
      · simp [step_apply, hjlo, hjhi, ha.1 j]
  · calc
      ∑ j, step i a j = ∑ j, a j := sum_step i a
      _ = N := ha.2

/-- Prefix-sum affine coordinate change `s : Δ → Γ` from Section 4. -/
def prefixMap {n : ℕ} (a : Fin (n + 1) → ℤ) (j : Fin n) : ℤ :=
  ∑ k ∈ (Finset.univ.filter fun k : Fin (n + 1) ↦ k.val ≤ j.val), a k

private theorem prefixMap_eq_sum_Iic {n : ℕ} (a : Fin (n + 1) → ℤ)
    (j : Fin n) :
    prefixMap a j = ∑ k ∈ Finset.Iic j.castSucc, a k := by
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    change k.val ≤ j.val ↔ k.val ≤ j.val
    rfl
  · intro k _
    rfl

@[simp]
theorem prefixMap_zero {n : ℕ} (a : Fin (n + 2) → ℤ) :
    prefixMap a (0 : Fin (n + 1)) = a 0 := by
  rw [prefixMap_eq_sum_Iic]
  have hIic : Finset.Iic (0 : Fin (n + 2)) = {0} := by
    ext k
    simp [Finset.mem_Iic]
  change (∑ k ∈ Finset.Iic (0 : Fin (n + 2)), a k) = a 0
  rw [hIic]
  simp

/-- Successive prefix coordinates differ by the newly included coordinate. -/
theorem prefixMap_succ {n : ℕ} (a : Fin (n + 2) → ℤ) (j : Fin n) :
    prefixMap a j.succ = prefixMap a j.castSucc + a j.succ.castSucc := by
  rw [prefixMap_eq_sum_Iic, prefixMap_eq_sum_Iic]
  let lo : Fin (n + 2) := j.castSucc.castSucc
  let hi : Fin (n + 2) := j.succ.castSucc
  have hlohi : lo < hi := by simp [lo, hi]
  have hIic : Finset.Iic hi = insert hi (Finset.Iic lo) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert]
    constructor
    · intro h
      by_cases hk : k = hi
      · exact Or.inl hk
      · right
        have hklt : k < hi := lt_of_le_of_ne h hk
        change k.val ≤ j.val
        change k.val < j.val + 1 at hklt
        omega
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.trans hlohi.le
  change (∑ k ∈ Finset.Iic hi, a k) =
    (∑ k ∈ Finset.Iic lo, a k) + a hi
  rw [hIic, Finset.sum_insert]
  · ac_rfl
  · simp [Finset.mem_Iic, not_le_of_gt hlohi]

theorem prefixMap_eq_of_val_zero {n : ℕ}
    (a : Fin (n + 1) → ℤ) (q : Fin n) (hq : q.val = 0) :
    prefixMap a q = a 0 := by
  rw [prefixMap_eq_sum_Iic]
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

theorem prefixMap_eq_prev_add {n : ℕ}
    (a : Fin (n + 1) → ℤ) (q : Fin n) (hq : q.val ≠ 0) :
    prefixMap a q =
      prefixMap a ⟨q.val - 1, by omega⟩ + a q.castSucc := by
  rw [prefixMap_eq_sum_Iic, prefixMap_eq_sum_Iic]
  let p : Fin (n + 1) := (⟨q.val - 1, by omega⟩ : Fin n).castSucc
  have hpq : p < q.castSucc := by
    change q.val - 1 < q.val
    have : 0 < q.val := Nat.pos_of_ne_zero hq
    omega
  have hIic : Finset.Iic q.castSucc = insert q.castSucc (Finset.Iic p) := by
    ext k
    simp only [Finset.mem_Iic, Finset.mem_insert]
    constructor
    · intro h
      by_cases hk : k = q.castSucc
      · exact Or.inl hk
      · right
        have hklt : k < q.castSucc := lt_of_le_of_ne h hk
        change k.val < q.val at hklt
        change k.val ≤ q.val - 1
        omega
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.trans hpq.le
  change (∑ k ∈ Finset.Iic q.castSucc, a k) =
    (∑ k ∈ Finset.Iic p, a k) + a q.castSucc
  rw [hIic, Finset.sum_insert]
  · ac_rfl
  · simp [Finset.mem_Iic, not_le_of_gt hpq]

/-- On a fixed coordinate-sum hyperplane, the prefix map is injective.  No
nonnegativity hypothesis is needed for this algebraic statement. -/
theorem prefixMap_injective_on_sum {n : ℕ} {N : ℤ}
    {a b : Fin (n + 1) → ℤ}
    (ha : ∑ i, a i = N) (hb : ∑ i, b i = N)
    (hp : prefixMap a = prefixMap b) : a = b := by
  have hfront : ∀ q : Fin n, a q.castSucc = b q.castSucc := by
    intro q
    let : NeZero n := ⟨Nat.ne_of_gt q.pos⟩
    by_cases hq : q.val = 0
    · have hqeq : q = 0 := Fin.ext hq
      have h0 := congrFun hp q
      rw [prefixMap_eq_of_val_zero a q hq,
        prefixMap_eq_of_val_zero b q hq] at h0
      simpa [hqeq] using h0
    · let p : Fin n := ⟨q.val - 1, by omega⟩
      have hcurr := congrFun hp q
      have hprev := congrFun hp p
      rw [prefixMap_eq_prev_add a q hq,
        prefixMap_eq_prev_add b q hq] at hcurr
      have hprev' :
          prefixMap a ⟨q.val - 1, by omega⟩ =
            prefixMap b ⟨q.val - 1, by omega⟩ := by
        simpa [p] using hprev
      omega
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨q, rfl⟩ | rfl
  · exact hfront q
  · have hsumFront : (∑ q : Fin n, a q.castSucc) =
        ∑ q : Fin n, b q.castSucc := by
      apply Finset.sum_congr rfl
      intro q _
      exact hfront q
    have hasa := ha
    have hasb := hb
    rw [Fin.sum_univ_castSucc] at hasa hasb
    omega

/-- The point-valued specialization of `prefixMap_injective_on_sum`, used to
transport the coordinate change to `Point N n`. -/
theorem prefixMap_injective_on_isPoint {n : ℕ} {N : ℤ}
    {a b : Fin (n + 1) → ℤ} (ha : IsPoint N a) (hb : IsPoint N b)
    (hp : prefixMap a = prefixMap b) : a = b := by
  exact prefixMap_injective_on_sum ha.2 hb.2 hp

/-- The cumulative-coordinate realization of an actual point of `D`. -/
def pointPrefix {N n : ℕ} (a : Point N n) : Fin n → ℤ :=
  prefixMap (pointCoords a)

theorem pointPrefix_injective {N n : ℕ} :
    Function.Injective (pointPrefix : Point N n → Fin n → ℤ) := by
  intro a b h
  apply pointCoords_injective
  exact prefixMap_injective_on_isPoint (pointCoords_isPoint a)
    (pointCoords_isPoint b) h

/-- The prefix map as an embedding of the finite point set. -/
def pointPrefixEmbedding (N n : ℕ) : Point N n ↪ (Fin n → ℤ) :=
  ⟨pointPrefix, pointPrefix_injective⟩

/-- Integer points of the monotone simplex `Γ` in cumulative coordinates. -/
def IsGammaPoint (N : ℤ) {n : ℕ} (y : Fin n → ℤ) : Prop :=
  (∀ i, 0 ≤ y i) ∧
  (∀ i j, i ≤ j → y i ≤ y j) ∧
  ∀ i, y i ≤ N

/-- The prefix map sends integer points of `Δ` to integer points of `Γ`. -/
theorem prefixMap_isGammaPoint {n : ℕ} {N : ℤ} {a : Fin (n + 1) → ℤ}
    (ha : IsPoint N a) : IsGammaPoint N (prefixMap a) := by
  constructor
  · intro i
    exact Finset.sum_nonneg fun k _ ↦ ha.1 k
  constructor
  · intro i j hij
    let Si : Finset (Fin (n + 1)) :=
      Finset.univ.filter fun k : Fin (n + 1) ↦ k.val ≤ i.val
    let Sj : Finset (Fin (n + 1)) :=
      Finset.univ.filter fun k : Fin (n + 1) ↦ k.val ≤ j.val
    have hsub : Si ⊆ Sj := by
      intro k hk
      simp only [Si, Sj, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk.trans hij
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ ↦ ha.1 k)
  · intro i
    have hsub : (Finset.univ.filter fun k : Fin (n + 1) ↦ k.val ≤ i.val) ⊆
        (Finset.univ : Finset (Fin (n + 1))) := Finset.filter_subset _ _
    have hle : prefixMap a i ≤ ∑ k, a k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ ↦ ha.1 k)
    simpa [ha.2] using hle

theorem pointPrefix_isGammaPoint {N n : ℕ} (a : Point N n) :
    IsGammaPoint (N : ℤ) (pointPrefix a) :=
  prefixMap_isGammaPoint (pointCoords_isPoint a)

private theorem prefixMap_eq_sum_range {n : ℕ} (a : Fin (n + 1) → ℤ)
    (j : Fin n) :
    prefixMap a j =
      ∑ k ∈ (Finset.univ.filter fun k : Fin (n + 1) ↦ k.val ≤ j.val), a k := rfl

private theorem sum_pi_single_on {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (k : α) :
    ∑ x ∈ S, (Pi.single k (1 : ℤ)) x = if k ∈ S then 1 else 0 := by
  by_cases hk : k ∈ S <;> simp [Pi.single_apply, hk]

/-- Applying `S_{i+1}` before `s` adds the `i`-th standard unit vector.
This is the computational content of Lemma 4.6. -/
theorem prefixMap_step {n : ℕ} (i : Fin n) (a : Fin (n + 1) → ℤ) :
    prefixMap (step i a) =
      prefixMap a + (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
  funext j
  let S : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun k : Fin (n + 1) ↦ k.val ≤ j.val
  have hlo : i.castSucc ∈ S ↔ i.val ≤ j.val := by simp [S]
  have hhi : i.succ ∈ S ↔ i.val + 1 ≤ j.val := by simp [S]
  calc
    prefixMap (step i a) j =
        (∑ k ∈ S, a k) + (if i.castSucc ∈ S then 1 else 0) -
          (if i.succ ∈ S then 1 else 0) := by
      simp only [prefixMap, S, step, Pi.add_apply, Pi.sub_apply,
        Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [sum_pi_single_on, sum_pi_single_on]
    _ = prefixMap a j + (Pi.single i (1 : ℤ) : Fin n → ℤ) j := by
      simp only [prefixMap, S, Pi.single_apply]
      by_cases hij : j = i
      · subst j
        have hlowmem : i.castSucc ∈ S := hlo.mpr le_rfl
        have hhighnot : i.succ ∉ S := fun h ↦ by
          have := hhi.mp h
          omega
        simp
      · rcases lt_or_gt_of_ne hij with hji | hij'
        · have hlownot : i.castSucc ∉ S := fun h ↦
            (not_le_of_gt hji) (hlo.mp h)
          have hhighnot : i.succ ∉ S := fun h ↦ by
            have := hhi.mp h
            omega
          rw [if_neg hlownot, if_neg hhighnot,
            if_neg hij]
          ring
        · have hlowmem : i.castSucc ∈ S := hlo.mpr (le_of_lt hij')
          have hhighmem : i.succ ∈ S := hhi.mpr (by omega)
          rw [if_pos hlowmem, if_pos hhighmem,
            if_neg hij'.ne']
          ring

/-- Translation commutes with every transfer. -/
theorem step_add {n : ℕ} (i : Fin n) (a b : Fin (n + 1) → ℤ) :
    step i (a + b) = a + step i b := by
  ext j
  simp [step_apply]
  ring

/-- Prefix coordinates are additive. -/
theorem prefixMap_add {n : ℕ} (a b : Fin (n + 1) → ℤ) :
    prefixMap (a + b) = prefixMap a + prefixMap b := by
  ext j
  simp [prefixMap, Finset.sum_add_distrib]

/-- The Freudenthal step sequence in cumulative coordinates. -/
def freudenthalSequence {n : ℕ} (u : Fin n → ℤ) :
    List (Fin n) → List (Fin n → ℤ)
  | [] => [u]
  | i :: l => u :: freudenthalSequence (u + Pi.single i 1) l

theorem length_freudenthalSequence {n : ℕ} (u : Fin n → ℤ)
    (l : List (Fin n)) : (freudenthalSequence u l).length = l.length + 1 := by
  induction l generalizing u with
  | nil => rfl
  | cons i l ih => simp [freudenthalSequence, ih]

theorem freudenthalSequence_coordinate_eq_of_not_mem
    {n : ℕ} (u : Fin n → ℤ) (l : List (Fin n)) {i : Fin n}
    (hi : i ∉ l) {v : Fin n → ℤ} (hv : v ∈ freudenthalSequence u l) :
    v i = u i := by
  induction l generalizing u v with
  | nil =>
      simp [freudenthalSequence] at hv
      subst v
      rfl
  | cons j l ih =>
      simp only [freudenthalSequence, List.mem_cons] at hv
      have hiData : i ≠ j ∧ i ∉ l := by simpa using hi
      have hij : i ≠ j := hiData.1
      have hiL : i ∉ l := hiData.2
      rcases hv with rfl | hv
      · rfl
      · have hcoord := ih (u := u + Pi.single j 1) hiL hv
        simpa [Pi.single_apply, hij] using hcoord

/-- A Freudenthal step sequence has no repeated vertex when no coordinate is
used twice. -/
theorem freudenthalSequence_nodup {n : ℕ} (u : Fin n → ℤ)
    {l : List (Fin n)} (hl : l.Nodup) :
    (freudenthalSequence u l).Nodup := by
  induction l generalizing u with
  | nil => simp [freudenthalSequence]
  | cons i l ih =>
      have hi : i ∉ l := (List.nodup_cons.mp hl).1
      have hl' : l.Nodup := (List.nodup_cons.mp hl).2
      rw [freudenthalSequence]
      apply List.nodup_cons.mpr
      constructor
      · intro hu
        have hcoord := freudenthalSequence_coordinate_eq_of_not_mem
          (u + Pi.single i 1) l hi hu
        simp at hcoord
      · exact ih (u := u + Pi.single i 1) hl'

/-- The step sequence associated with a list of coordinate indices. -/
def stepSequence {n : ℕ} (a : Fin (n + 1) → ℤ) :
    List (Fin n) → List (Fin (n + 1) → ℤ)
  | [] => [a]
  | i :: l => a :: (stepSequence (step i a) l)

/-- The endpoint obtained after performing every transfer in a list. -/
def stepEndpoint {n : ℕ} (a : Fin (n + 1) → ℤ) :
    List (Fin n) → (Fin (n + 1) → ℤ)
  | [] => a
  | i :: l => stepEndpoint (step i a) l

theorem stepEndpoint_mem_stepSequence {n : ℕ}
    (a : Fin (n + 1) → ℤ) (l : List (Fin n)) :
    stepEndpoint a l ∈ stepSequence a l := by
  induction l generalizing a with
  | nil => simp [stepEndpoint, stepSequence]
  | cons i l ih =>
      simp only [stepEndpoint, stepSequence, List.mem_cons]
      exact Or.inr (ih (a := step i a))

theorem length_stepSequence {n : ℕ} (a : Fin (n + 1) → ℤ)
    (l : List (Fin n)) : (stepSequence a l).length = l.length + 1 := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih => simp [stepSequence, ih]

/-- Every vertex in a transfer sequence lies on the same affine
coordinate-sum hyperplane as its initial vertex. -/
theorem sum_eq_of_mem_stepSequence {n : ℕ}
    (a : Fin (n + 1) → ℤ) (l : List (Fin n))
    {b : Fin (n + 1) → ℤ} (hb : b ∈ stepSequence a l) :
    ∑ i, b i = ∑ i, a i := by
  induction l generalizing a with
  | nil =>
      simp only [stepSequence, List.mem_singleton] at hb
      subst b
      rfl
  | cons i l ih =>
      simp only [stepSequence, List.mem_cons] at hb
      rcases hb with rfl | hb
      · rfl
      · exact (ih (a := step i a) hb).trans (sum_step i a)

/-- Vertices of the step simplex `a + σ(ι)`. -/
def stepSimplex {n : ℕ} (a : Fin (n + 1) → ℤ) (l : List (Fin n)) :
    Finset (Fin (n + 1) → ℤ) := (stepSequence a l).toFinset

theorem stepEndpoint_mem_stepSimplex {n : ℕ}
    (a : Fin (n + 1) → ℤ) (l : List (Fin n)) :
    stepEndpoint a l ∈ stepSimplex a l := by
  simpa [stepSimplex] using stepEndpoint_mem_stepSequence a l

theorem sum_eq_of_mem_stepSimplex {n : ℕ}
    (a : Fin (n + 1) → ℤ) (l : List (Fin n))
    {b : Fin (n + 1) → ℤ} (hb : b ∈ stepSimplex a l) :
    ∑ i, b i = ∑ i, a i := by
  apply sum_eq_of_mem_stepSequence a l
  simpa [stepSimplex] using hb

/-- Vertices of a Freudenthal simplex in cumulative coordinates. -/
def freudenthalSimplex {n : ℕ} (u : Fin n → ℤ) (l : List (Fin n)) :
    Finset (Fin n → ℤ) := (freudenthalSequence u l).toFinset

/-- Translating the initial point translates the entire step sequence. -/
theorem stepSequence_add {n : ℕ} (a b : Fin (n + 1) → ℤ)
    (l : List (Fin n)) :
    stepSequence (a + b) l = (stepSequence b l).map (fun x ↦ a + x) := by
  induction l generalizing b with
  | nil => simp [stepSequence]
  | cons i l ih =>
      simp only [stepSequence, List.map_cons]
      rw [step_add, ih]

/-- Under the prefix map, a step sequence becomes the usual Freudenthal
sequence obtained by successively adding unit vectors. -/
theorem prefixMap_stepSequence {n : ℕ} (a : Fin (n + 1) → ℤ)
    (l : List (Fin n)) :
    (stepSequence a l).map prefixMap =
      (freudenthalSequence (prefixMap a) l) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
      simp only [stepSequence, List.map_cons]
      rw [ih, prefixMap_step]
      rfl

/-- Lemma 4.6, at the level of vertex sets: the cumulative-coordinate map
takes `a + σ(ι)` exactly to the corresponding Freudenthal vertex set. -/
theorem image_prefixMap_stepSimplex {n : ℕ} (a : Fin (n + 1) → ℤ)
    (l : List (Fin n)) :
    (stepSimplex a l).image prefixMap = freudenthalSimplex (prefixMap a) l := by
  rw [stepSimplex, freudenthalSimplex, ← prefixMap_stepSequence]
  ext y
  simp

/-- The list attached to a permutation of the nonzero coordinate indices. -/
def permutationList {n : ℕ} (ω : Equiv.Perm (Fin n)) : List (Fin n) :=
  List.ofFn ω

@[simp]
theorem length_permutationList {n : ℕ} (ω : Equiv.Perm (Fin n)) :
    (permutationList ω).length = n := by
  simp [permutationList]

theorem nodup_permutationList {n : ℕ} (ω : Equiv.Perm (Fin n)) :
    (permutationList ω).Nodup := by
  exact List.nodup_ofFn.mpr ω.injective

/-- Conversely, any duplicate-free list of all `Fin n` indices is the list
of a genuine permutation.  This prevents later face constructions from
using an arbitrary list where the paper requires a permutation. -/
theorem exists_permutationList_eq_of_nodup_length {n : ℕ}
    (l : List (Fin n)) (hl : l.Nodup) (hlen : l.length = n) :
    ∃ omega : Equiv.Perm (Fin n), permutationList omega = l := by
  have hcard : l.toFinset.card = Fintype.card (Fin n) := by
    rw [List.toFinset_card_of_nodup hl, hlen]
    simp
  have huniv : l.toFinset = Finset.univ :=
    Finset.eq_univ_of_card l.toFinset hcard
  have hall : ∀ x : Fin n, x ∈ l := by
    intro x
    simp [← List.mem_toFinset, huniv]
  let e0 : Fin l.length ≃ Fin n := hl.getEquivOfForallMemList l hall
  let e : Equiv.Perm (Fin n) := (finCongr hlen.symm).trans e0
  refine ⟨e, ?_⟩
  apply List.ext_get
  · simp [permutationList, hlen]
  · intro q hq1 hq2
    simp [permutationList, e, e0,
      List.Nodup.getEquivOfForallMemList]

/-- A permutation step simplex has exactly `n+1` vertices. -/
theorem card_stepSimplex_permutation {n : ℕ} (a : Fin (n + 1) → ℤ)
    (ω : Equiv.Perm (Fin n)) :
    (stepSimplex a (permutationList ω)).card = n + 1 := by
  have hfreud : (freudenthalSequence (prefixMap a) (permutationList ω)).Nodup :=
    freudenthalSequence_nodup (prefixMap a) (nodup_permutationList ω)
  have hstep : (stepSequence a (permutationList ω)).Nodup := by
    apply List.Nodup.of_map prefixMap
    rw [prefixMap_stepSequence]
    exact hfreud
  rw [stepSimplex, List.toFinset_card_of_nodup hstep,
    length_stepSequence, length_permutationList]

end IntegerSimplex

end BeyondSperner
