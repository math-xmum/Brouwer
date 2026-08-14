import BeyondSperner.Freudenthal.DimensionZero

/-!
# Coordinate faces of the integer simplex

The induction in Theorem 4.8 identifies the face `x_k = 0` of an
`(n+1)`-dimensional integer simplex with the `n`-dimensional integer simplex.
This file constructs that identification explicitly, including its inverse.
-/

namespace BeyondSperner

open Classical

namespace IntegerSimplex

/-- Inserting the same entry into two finite lexicographic tuples does not
change their strict comparison.  This is the order-theoretic core of deleting
a coordinate which is constant on a face. -/
theorem toLex_insertNth_lt_iff {m : ℕ} {α : Type*} [LinearOrder α]
    (q : Fin (m + 1)) (c : α) (a b : Fin m → α) :
    toLex (Fin.insertNth (α := fun _ ↦ α) q c a) <
      toLex (Fin.insertNth (α := fun _ ↦ α) q c b) ↔
      toLex a < toLex b := by
  constructor
  · rintro ⟨r, hprev, hlt⟩
    have hrq : r ≠ q := by
      intro hrq
      subst r
      simp [Fin.insertNth_apply_same] at hlt
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hrq
    refine ⟨j, ?_, ?_⟩
    · intro s hs
      have hmono : q.succAbove s < q.succAbove j :=
        Fin.strictMono_succAbove q hs
      have heq := hprev (q.succAbove s) hmono
      simpa [Fin.insertNth_apply_succAbove] using heq
    · simpa [Fin.insertNth_apply_succAbove] using hlt
  · rintro ⟨j, hprev, hlt⟩
    refine ⟨q.succAbove j, ?_, ?_⟩
    · intro r hr
      by_cases hrq : r = q
      · subst r
        simp [Fin.insertNth_apply_same]
      · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hrq
        have hsj : s < j :=
          (Fin.strictMono_succAbove q).lt_iff_lt.mp hr
        simpa [Fin.insertNth_apply_succAbove] using hprev s hsj
    · simpa [Fin.insertNth_apply_succAbove] using hlt

/-- In the cyclic coordinate list starting at inserted coordinate `i+1`, the
position occupied by the new coordinate zero. -/
def zeroPosition {n : ℕ} (i : Fin (n + 1)) : Fin (n + 2) :=
  ⟨n + 1 - i.val, by omega⟩

@[simp]
theorem finCycle_succ_zeroPosition {n : ℕ} (i : Fin (n + 1)) :
    finCycle i.succ (zeroPosition i) = 0 := by
  apply Fin.ext
  simp only [finCycle_apply, Fin.val_add, Fin.val_succ, zeroPosition,
    Fin.val_zero]
  have heq : i.val + 1 + (n + 1 - i.val) = n + 2 := by omega
  rw [Nat.add_comm, heq, Nat.mod_self]

/-- After removing that zero position, the high cyclic coordinate list is
exactly the successor embedding of the lower cyclic coordinate list. -/
theorem finCycle_succ_succAbove_zeroPosition {n : ℕ}
    (i j : Fin (n + 1)) :
    finCycle i.succ ((zeroPosition i).succAbove j) =
      (finCycle i j).succ := by
  apply Fin.ext
  simp only [finCycle_apply, Fin.val_add, Fin.val_succ]
  by_cases hj : j.castSucc < zeroPosition i
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    change j.val < n + 1 - i.val at hj
    change (j.val + (i.val + 1)) % (n + 2) =
      (j.val + i.val) % (n + 1) + 1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · have hpos : zeroPosition i < j.succ := by
      change n + 1 - i.val < j.val + 1
      change ¬j.val < n + 1 - i.val at hj
      omega
    rw [Fin.succAbove_of_lt_succ _ _ hpos]
    change ¬j.val < n + 1 - i.val at hj
    change (j.val + 1 + (i.val + 1)) % (n + 2) =
      (j.val + i.val) % (n + 1) + 1
    have hhigh : (j.val + 1 + (i.val + 1)) % (n + 2) =
        j.val + 1 + (i.val + 1) - (n + 2) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hlow : (j.val + i.val) % (n + 1) =
        j.val + i.val - (n + 1) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hhigh, hlow]
    omega

/-- Position of the deleted coordinate `k` in the ambient cyclic list which
starts at the embedded lower index `k.succAbove i`.  The two branches are the
two possible sides of the linear cut at `k`. -/
def faceDeletedPosition {n : ℕ} (k : Fin (n + 2))
    (i : Fin (n + 1)) : Fin (n + 2) :=
  if h : i.castSucc < k then
    ⟨k.val - i.val, by omega⟩
  else
    ⟨n + 1 + k.val - i.val, by
      have hki : k.val ≤ i.val := by
        change ¬i.val < k.val at h
        omega
      omega⟩

@[simp]
theorem finCycle_faceDeletedPosition {n : ℕ} (k : Fin (n + 2))
    (i : Fin (n + 1)) :
    finCycle (k.succAbove i) (faceDeletedPosition k i) = k := by
  by_cases h : i.castSucc < k
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have hv : i.val < k.val := h
    apply Fin.ext
    simp only [finCycle_apply, Fin.val_add, Fin.val_castSucc,
      faceDeletedPosition, dif_pos h]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have h' : k ≤ i.castSucc := Fin.not_lt.mp h
    rw [Fin.succAbove_of_le_castSucc _ _ h']
    have hv : ¬i.val < k.val := h
    apply Fin.ext
    simp only [finCycle_apply, Fin.val_add, Fin.val_succ,
      faceDeletedPosition, dif_neg h]
    have heq : n + 1 + k.val - i.val + (i.val + 1) =
        n + 2 + k.val := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt k.isLt]

/-- Naturality of cyclic enumeration under deletion of an arbitrary
coordinate.  This is the exact combinatorial identity needed to transport the
paper's cyclic lexicographic orders to every coordinate face. -/
theorem finCycle_face_succAbove {n : ℕ} (k : Fin (n + 2))
    (i j : Fin (n + 1)) :
    finCycle (k.succAbove i) ((faceDeletedPosition k i).succAbove j) =
      k.succAbove (finCycle i j) := by
  by_cases hi : i.castSucc < k
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    have hiv : i.val < k.val := hi
    by_cases hj : j.castSucc < faceDeletedPosition k i
    · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
      have hjv : j.val < k.val - i.val := by
        change j.val < (faceDeletedPosition k i).val at hj
        simpa [faceDeletedPosition, hi] using hj
      have hsum : j.val + i.val < n + 1 := by omega
      have hbelow : (finCycle i j).castSucc < k := by
        change (j.val + i.val) % (n + 1) < k.val
        rw [Nat.mod_eq_of_lt hsum]
        omega
      rw [Fin.succAbove_of_castSucc_lt _ _ hbelow]
      apply Fin.ext
      simp only [finCycle_apply, Fin.val_add, Fin.val_castSucc]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hsum]
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.not_lt.mp hj)]
      have hjv : k.val - i.val ≤ j.val := by
        have hj' : ¬j.val < (faceDeletedPosition k i).val := hj
        simpa [faceDeletedPosition, hi] using (Nat.not_lt.mp hj')
      by_cases hwrap : j.val + i.val < n + 1
      · have habove : k ≤ (finCycle i j).castSucc := by
          change k.val ≤ (j.val + i.val) % (n + 1)
          rw [Nat.mod_eq_of_lt hwrap]
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ habove]
        apply Fin.ext
        simp only [finCycle_apply, Fin.val_add, Fin.val_succ]
        change (j.val + 1 + i.val) % (n + 2) =
          (j.val + i.val) % (n + 1) + 1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hwrap]
        omega
      · have hbelow : (finCycle i j).castSucc < k := by
          change (j.val + i.val) % (n + 1) < k.val
          rw [Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)]
          omega
        rw [Fin.succAbove_of_castSucc_lt _ _ hbelow]
        apply Fin.ext
        simp only [finCycle_apply, Fin.val_add, Fin.val_succ,
          Fin.val_castSucc]
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  · have hki : k ≤ i.castSucc := Fin.not_lt.mp hi
    rw [Fin.succAbove_of_le_castSucc _ _ hki]
    have hiv : k.val ≤ i.val := hki
    by_cases hj : j.castSucc < faceDeletedPosition k i
    · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
      have hjv : j.val < n + 1 + k.val - i.val := by
        change j.val < (faceDeletedPosition k i).val at hj
        simpa [faceDeletedPosition, hi] using hj
      by_cases hwrap : j.val + i.val < n + 1
      · have habove : k ≤ (finCycle i j).castSucc := by
          change k.val ≤ (j.val + i.val) % (n + 1)
          rw [Nat.mod_eq_of_lt hwrap]
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ habove]
        apply Fin.ext
        simp only [finCycle_apply, Fin.val_add, Fin.val_succ]
        change (j.val + (i.val + 1)) % (n + 2) =
          (j.val + i.val) % (n + 1) + 1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hwrap]
        omega
      · have hbelow : (finCycle i j).castSucc < k := by
          change (j.val + i.val) % (n + 1) < k.val
          rw [Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)]
          omega
        rw [Fin.succAbove_of_castSucc_lt _ _ hbelow]
        apply Fin.ext
        simp only [finCycle_apply, Fin.val_add, Fin.val_succ,
          Fin.val_castSucc]
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.not_lt.mp hj)]
      have hjv : n + 1 + k.val - i.val ≤ j.val := by
        have hj' : ¬j.val < (faceDeletedPosition k i).val := hj
        simpa [faceDeletedPosition, hi] using (Nat.not_lt.mp hj')
      have habove : k ≤ (finCycle i j).castSucc := by
        change k.val ≤ (j.val + i.val) % (n + 1)
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [Fin.succAbove_of_le_castSucc _ _ habove]
      apply Fin.ext
      simp only [finCycle_apply, Fin.val_add, Fin.val_succ]
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-- Delete one index from `Fin (n+2)`: the remaining indices are explicitly
equivalent to `Fin (n+1)`. -/
noncomputable def faceIndexEquiv {n : ℕ} (k : Fin (n + 2)) :
    Fin (n + 1) ≃ {i : Fin (n + 2) // i ≠ k} where
  toFun j := ⟨k.succAbove j, Fin.succAbove_ne k j⟩
  invFun i := Classical.choose (Fin.exists_succAbove_eq i.2)
  left_inv := by
    intro j
    exact (Fin.succAboveEmb k).injective (Classical.choose_spec
      (Fin.exists_succAbove_eq
        (show k.succAbove j ≠ k from Fin.succAbove_ne k j)))
  right_inv := by
    intro i
    apply Subtype.ext
    exact Classical.choose_spec (Fin.exists_succAbove_eq i.2)

@[simp]
theorem faceIndexEquiv_apply_val {n : ℕ} (k : Fin (n + 2))
    (j : Fin (n + 1)) :
    (faceIndexEquiv k j).1 = k.succAbove j := rfl

/-- The ambient image of the lower-dimensional index type is exactly
`I \ {k}`. -/
theorem image_univ_faceIndexEquiv {n : ℕ} (k : Fin (n + 2)) :
    (Finset.univ : Finset (Fin (n + 1))).image
        (fun j ↦ (faceIndexEquiv k j).1) =
      (Finset.univ : Finset (Fin (n + 2))).erase k := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    simp [Fin.succAbove_ne]
  · intro hi
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hik
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by
      simpa using hj⟩

/-- Insert a zero into an integer coordinate vector.  This unbundled version
is used to compare transfer sequences before packaging them as `Point`s. -/
def insertZeroCoords {n : ℕ} (k : Fin (n + 2))
    (a : Fin (n + 1) → ℤ) : Fin (n + 2) → ℤ :=
  Fin.insertNth k 0 a

/-- Delete a coordinate from an unbundled vector. -/
def eraseCoords {n : ℕ} (k : Fin (n + 2))
    (b : Fin (n + 2) → ℤ) : Fin (n + 1) → ℤ :=
  fun j ↦ b (k.succAbove j)

/-- Collapse coordinate zero into coordinate one and then delete it.  Unlike
plain deletion, this preserves the total coordinate sum even away from the
face `x_0 = 0`. -/
def collapseZeroCoords {n : ℕ}
    (b : Fin (n + 2) → ℤ) : Fin (n + 1) → ℤ :=
  fun j ↦ b j.succ + if j = 0 then b 0 else 0

/-- Repeatedly move one unit from coordinate zero to its cyclic predecessor.
No point condition is imposed at the definition level; validity is proved
separately under the exact source-coordinate bound. -/
def moveZeroMass {n : ℕ} (a : Fin (n + 2) → ℤ) :
    ℕ → (Fin (n + 2) → ℤ)
  | 0 => a
  | t + 1 => cyclicStep 0 (moveZeroMass a t)

theorem moveZeroMass_apply {n : ℕ} (a : Fin (n + 2) → ℤ)
    (t : ℕ) (r : Fin (n + 2)) :
    moveZeroMass a t r =
      a r + (t : ℤ) *
          (if r = (finRotate (n + 2)).symm 0 then 1 else 0) -
        (t : ℤ) * (if r = 0 then 1 else 0) := by
  induction t with
  | zero => simp [moveZeroMass]
  | succ t ih =>
      rw [moveZeroMass, cyclicStep_apply, ih]
      push_cast
      split <;> split <;> ring

theorem sum_moveZeroMass {n : ℕ} (a : Fin (n + 2) → ℤ)
    (t : ℕ) :
    ∑ r, moveZeroMass a t r = ∑ r, a r := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [moveZeroMass, sum_cyclicStep, ih]

theorem finRotate_symm_zero_ne_zero (n : ℕ) :
    (finRotate (n + 2)).symm (0 : Fin (n + 2)) ≠ 0 := by
  intro h
  have h' := congrArg (finRotate (n + 2)) h
  simp at h'

/-- Repeated zero transfers remain in the integer simplex exactly as long as
the number of transfers does not exceed the original zero coordinate. -/
theorem moveZeroMass_isPoint {n : ℕ} {N : ℤ}
    (a : Fin (n + 2) → ℤ) (ha : IsPoint N a) (t : ℕ)
    (ht : (t : ℤ) ≤ a 0) :
    IsPoint N (moveZeroMass a t) := by
  constructor
  · intro r
    rw [moveZeroMass_apply]
    by_cases hrp : r = (finRotate (n + 2)).symm 0
    · rw [if_pos hrp]
      have hr0 : r ≠ 0 := by
        rw [hrp]
        exact finRotate_symm_zero_ne_zero n
      rw [if_neg hr0]
      have har := ha.1 r
      simp only [mul_one, mul_zero, sub_zero]
      exact add_nonneg har (Int.natCast_nonneg t)
    · rw [if_neg hrp]
      by_cases hr0 : r = 0
      · subst r
        rw [if_pos rfl]
        omega
      · rw [if_neg hr0]
        simpa using ha.1 r
  · rw [sum_moveZeroMass, ha.2]

/-- Every nonzero cyclic order weakly increases while zero mass is moved to
the predecessor coordinate. -/
theorem cyclicKey_le_moveZeroMass {n : ℕ}
    (j : Fin (n + 2)) (hj : j ≠ 0)
    (a : Fin (n + 2) → ℤ) (t : ℕ) :
    cyclicKey j a ≤ cyclicKey j (moveZeroMass a t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      exact ih.trans (le_of_lt
        (cyclicKey_lt_cyclicStep_of_ne (Nat.succ_pos n) 0 j hj
          (moveZeroMass a t)))

/-- Repeatedly move mass out of an arbitrary coordinate `k` to its cyclic
predecessor. -/
def moveCoordinateMass {n : ℕ} (k : Fin (n + 2))
    (a : Fin (n + 2) → ℤ) : ℕ → (Fin (n + 2) → ℤ)
  | 0 => a
  | t + 1 => cyclicStep k (moveCoordinateMass k a t)

theorem moveCoordinateMass_apply {n : ℕ} (k : Fin (n + 2))
    (a : Fin (n + 2) → ℤ) (t : ℕ) (r : Fin (n + 2)) :
    moveCoordinateMass k a t r =
      a r + (t : ℤ) *
          (if r = (finRotate (n + 2)).symm k then 1 else 0) -
        (t : ℤ) * (if r = k then 1 else 0) := by
  induction t with
  | zero => simp [moveCoordinateMass]
  | succ t ih =>
      rw [moveCoordinateMass, cyclicStep_apply, ih]
      push_cast
      split <;> split <;> ring

theorem sum_moveCoordinateMass {n : ℕ} (k : Fin (n + 2))
    (a : Fin (n + 2) → ℤ) (t : ℕ) :
    ∑ r, moveCoordinateMass k a t r = ∑ r, a r := by
  induction t with
  | zero => rfl
  | succ t ih => rw [moveCoordinateMass, sum_cyclicStep, ih]

theorem finRotate_symm_ne_self_face {n : ℕ} (k : Fin (n + 2)) :
    (finRotate (n + 2)).symm k ≠ k := by
  intro h
  have h' := congrArg (finRotate (n + 2)) h
  simp only [Equiv.apply_symm_apply] at h'
  by_cases hlast : k = Fin.last (n + 1)
  · subst k
    have hv := congrArg Fin.val h'
    simp at hv
  · exact (ne_of_lt ((lt_finRotate_iff_ne_last k).2 hlast)) h'

theorem moveCoordinateMass_isPoint {n : ℕ} {N : ℤ}
    (k : Fin (n + 2)) (a : Fin (n + 2) → ℤ)
    (ha : IsPoint N a) (t : ℕ) (ht : (t : ℤ) ≤ a k) :
    IsPoint N (moveCoordinateMass k a t) := by
  constructor
  · intro r
    rw [moveCoordinateMass_apply]
    by_cases hrp : r = (finRotate (n + 2)).symm k
    · rw [if_pos hrp]
      have hrk : r ≠ k := by
        rw [hrp]
        exact finRotate_symm_ne_self_face k
      rw [if_neg hrk]
      simp only [mul_one, mul_zero, sub_zero]
      exact add_nonneg (ha.1 r) (Int.natCast_nonneg t)
    · rw [if_neg hrp]
      by_cases hrk : r = k
      · subst r
        rw [if_pos rfl]
        omega
      · rw [if_neg hrk]
        simpa using ha.1 r
  · rw [sum_moveCoordinateMass, ha.2]

theorem cyclicKey_le_moveCoordinateMass {n : ℕ}
    (k j : Fin (n + 2)) (hjk : j ≠ k)
    (a : Fin (n + 2) → ℤ) (t : ℕ) :
    cyclicKey j a ≤ cyclicKey j (moveCoordinateMass k a t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      exact ih.trans (le_of_lt
        (cyclicKey_lt_cyclicStep_of_ne (Nat.succ_pos n) k j hjk
          (moveCoordinateMass k a t)))

@[simp]
theorem insertZeroCoords_apply_self {n : ℕ} (k : Fin (n + 2))
    (a : Fin (n + 1) → ℤ) : insertZeroCoords k a k = 0 := by
  simp [insertZeroCoords, Fin.insertNth_apply_same]

@[simp]
theorem insertZeroCoords_apply_succAbove {n : ℕ} (k : Fin (n + 2))
    (a : Fin (n + 1) → ℤ) (j : Fin (n + 1)) :
    insertZeroCoords k a (k.succAbove j) = a j := by
  simp [insertZeroCoords, Fin.insertNth_apply_succAbove]

/-- Cyclic keys commute with insertion of zero at an arbitrary coordinate,
up to insertion of the common zero at the corresponding cyclic position. -/
theorem cyclicKey_insertZeroCoords {n : ℕ} (k : Fin (n + 2))
    (i : Fin (n + 1)) (a : Fin (n + 1) → ℤ) :
    cyclicKey (k.succAbove i) (insertZeroCoords k a) =
      toLex (Fin.insertNth (α := fun _ ↦ ℤ) (faceDeletedPosition k i) 0
        (fun j ↦ a (finCycle i j))) := by
  change toLex (fun r ↦
      insertZeroCoords k a (finCycle (k.succAbove i) r)) =
    toLex (Fin.insertNth (α := fun _ ↦ ℤ) (faceDeletedPosition k i) 0
      (fun j ↦ a (finCycle i j)))
  rw [toLex_inj]
  funext r
  by_cases hr : r = faceDeletedPosition k i
  · subst r
    rw [Fin.insertNth_apply_same, finCycle_faceDeletedPosition]
    exact insertZeroCoords_apply_self k a
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hr
    rw [finCycle_face_succAbove, Fin.insertNth_apply_succAbove]
    exact insertZeroCoords_apply_succAbove k a (finCycle i j)

/-- Exact compatibility of all cyclic lexicographic orders with deletion of
an arbitrary constant-zero coordinate. -/
theorem cyclicKey_insertZeroCoords_lt_iff {n : ℕ} (k : Fin (n + 2))
    (i : Fin (n + 1)) (a b : Fin (n + 1) → ℤ) :
    cyclicKey (k.succAbove i) (insertZeroCoords k a) <
        cyclicKey (k.succAbove i) (insertZeroCoords k b) ↔
      cyclicKey i a < cyclicKey i b := by
  rw [cyclicKey_insertZeroCoords k i a, cyclicKey_insertZeroCoords k i b]
  exact toLex_insertNth_lt_iff (faceDeletedPosition k i) 0
    (fun j ↦ a (finCycle i j)) (fun j ↦ b (finCycle i j))

/-- The cyclic key of a vector on the first coordinate face is obtained from
the lower cyclic key by inserting the common zero at its unique cyclic
position. -/
theorem cyclicKey_insertZeroCoords_zero {n : ℕ}
    (i : Fin (n + 1)) (a : Fin (n + 1) → ℤ) :
    cyclicKey i.succ (insertZeroCoords (0 : Fin (n + 2)) a) =
      toLex (Fin.insertNth (α := fun _ ↦ ℤ) (zeroPosition i) 0
        (fun j ↦ a (finCycle i j))) := by
  change toLex (fun r ↦ insertZeroCoords 0 a (finCycle i.succ r)) =
    toLex (Fin.insertNth (α := fun _ ↦ ℤ) (zeroPosition i) 0
      (fun j ↦ a (finCycle i j)))
  rw [toLex_inj]
  funext r
  by_cases hr : r = zeroPosition i
  · subst r
    rw [Fin.insertNth_apply_same, finCycle_succ_zeroPosition]
    exact insertZeroCoords_apply_self 0 a
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hr
    rw [show finCycle i.succ ((zeroPosition i).succAbove j) =
      (finCycle i j).succ from
        finCycle_succ_succAbove_zeroPosition i j]
    rw [Fin.insertNth_apply_succAbove]
    exact insertZeroCoords_apply_succAbove 0 a (finCycle i j)

/-- Exact compatibility of the cyclic lexicographic orders on the first
coordinate face. -/
theorem cyclicKey_insertZeroCoords_zero_lt_iff {n : ℕ}
    (i : Fin (n + 1)) (a b : Fin (n + 1) → ℤ) :
    cyclicKey i.succ (insertZeroCoords (0 : Fin (n + 2)) a) <
        cyclicKey i.succ (insertZeroCoords 0 b) ↔
      cyclicKey i a < cyclicKey i b := by
  rw [cyclicKey_insertZeroCoords_zero i a,
    cyclicKey_insertZeroCoords_zero i b]
  exact toLex_insertNth_lt_iff (zeroPosition i) 0
    (fun j ↦ a (finCycle i j)) (fun j ↦ b (finCycle i j))

theorem insertZeroCoords_isPoint {n : ℕ} {N : ℤ}
    (k : Fin (n + 2)) {a : Fin (n + 1) → ℤ}
    (ha : IsPoint N a) : IsPoint N (insertZeroCoords k a) := by
  constructor
  · intro i
    by_cases hi : i = k
    · subst i
      simp
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa using ha.1 j
  · rw [Fin.sum_univ_succAbove (insertZeroCoords k a) k]
    simp [ha.2]

@[simp]
theorem eraseCoords_insertZeroCoords {n : ℕ} (k : Fin (n + 2))
    (a : Fin (n + 1) → ℤ) :
    eraseCoords k (insertZeroCoords k a) = a := by
  funext j
  simp [eraseCoords]

theorem collapseZeroCoords_isPoint {n : ℕ} {N : ℤ}
    {b : Fin (n + 2) → ℤ} (hb : IsPoint N b) :
    IsPoint N (collapseZeroCoords b) := by
  constructor
  · intro j
    by_cases hj : j = 0
    · subst j
      simp only [collapseZeroCoords, ↓reduceIte]
      exact add_nonneg (hb.1 ((0 : Fin (n + 1)).succ))
        (hb.1 (0 : Fin (n + 2)))
    · simp [collapseZeroCoords, hj, hb.1]
  · have hsum := hb.2
    rw [Fin.sum_univ_succ] at hsum
    rw [show (∑ j, collapseZeroCoords b j) =
        (∑ j : Fin (n + 1), b j.succ) + b 0 by
      simp [collapseZeroCoords, Finset.sum_add_distrib]]
    omega

theorem collapseZeroCoords_eq_erase_of_zero {n : ℕ}
    {b : Fin (n + 2) → ℤ} (hb0 : b 0 = 0) :
    collapseZeroCoords b = eraseCoords 0 b := by
  funext j
  simp [collapseZeroCoords, eraseCoords, hb0]

/-- Delete zero from a high-dimensional transfer index, returning the
corresponding lower-dimensional index when it exists. -/
def dropZeroIndex {n : ℕ} (i : Fin (n + 1)) : Option (Fin n) :=
  if hi : i = 0 then none else some (i.pred hi)

/-- Remove transfer zero from a high-dimensional list and decrement every
remaining transfer index. -/
def dropZeroList {n : ℕ} (l : List (Fin (n + 1))) : List (Fin n) :=
  l.filterMap dropZeroIndex

theorem dropZeroList_permutation_nodup {n : ℕ}
    (Omega : Equiv.Perm (Fin (n + 1))) :
    (dropZeroList (permutationList Omega)).Nodup := by
  apply (nodup_permutationList Omega).filterMap
  intro i j q hqi hqj
  by_cases hi : i = 0
  · simp [dropZeroIndex, hi] at hqi
  · by_cases hj : j = 0
    · simp [dropZeroIndex, hj] at hqj
    · simp only [dropZeroIndex, dif_neg hi, dif_neg hj,
        Option.mem_def] at hqi hqj
      have hpredi : i.pred hi = q := Option.some.inj hqi
      have hpredj : j.pred hj = q := Option.some.inj hqj
      rw [← Fin.succ_pred i hi, ← Fin.succ_pred j hj,
        hpredi, hpredj]

theorem mem_dropZeroList_permutation {n : ℕ}
    (Omega : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    j ∈ dropZeroList (permutationList Omega) := by
  rw [dropZeroList, List.mem_filterMap]
  refine ⟨j.succ, ?_, ?_⟩
  · rw [permutationList, List.mem_ofFn]
    exact Omega.surjective j.succ
  · simp [dropZeroIndex, Fin.succ_ne_zero]

theorem dropZeroList_permutation_length {n : ℕ}
    (Omega : Equiv.Perm (Fin (n + 1))) :
    (dropZeroList (permutationList Omega)).length = n := by
  let l := dropZeroList (permutationList Omega)
  have hlNodup : l.Nodup := dropZeroList_permutation_nodup Omega
  have hlUniv : l.toFinset = Finset.univ := by
    ext j
    simp [l, mem_dropZeroList_permutation Omega j]
  rw [← List.toFinset_card_of_nodup hlNodup, hlUniv]
  simp

theorem exists_dropZeroPermutation {n : ℕ}
    (Omega : Equiv.Perm (Fin (n + 1))) :
    ∃ omega : Equiv.Perm (Fin n),
      permutationList omega = dropZeroList (permutationList Omega) :=
  exists_permutationList_eq_of_nodup_length _
    (dropZeroList_permutation_nodup Omega)
    (dropZeroList_permutation_length Omega)

/-- Every nonzero high transfer restricts to its predecessor transfer after
deleting coordinate zero. -/
theorem eraseCoords_zero_step_of_ne {n : ℕ}
    (i : Fin (n + 1)) (hi : i ≠ 0) (a : Fin (n + 2) → ℤ) :
    eraseCoords 0 (step i a) = step (i.pred hi) (eraseCoords 0 a) := by
  funext j
  change step i a j.succ = step (i.pred hi) (fun r ↦ a r.succ) j
  rw [step_apply, step_apply]
  have hipos : 0 < i.val := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hi
    apply Fin.ext
    exact hzero
  have hadd : j.succ = i.castSucc ↔
      j = (i.pred hi).castSucc := by
    constructor <;> intro h <;> apply Fin.ext
    · have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      change j.val = (i.pred hi).val
      rw [Fin.val_pred]
      omega
    · have hv := congrArg Fin.val h
      change j.val = (i.pred hi).val at hv
      rw [Fin.val_pred] at hv
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
  have hsub : j.succ = i.succ ↔ j = (i.pred hi).succ := by
    rw [Fin.succ_pred i hi]
    exact Fin.succ_inj
  rw [if_congr hadd rfl rfl, if_congr hsub rfl rfl]

/-- Collapsing coordinate zero makes transfer zero invisible. -/
theorem collapseZeroCoords_step_zero {n : ℕ}
    (a : Fin (n + 2) → ℤ) :
    collapseZeroCoords (step 0 a) = collapseZeroCoords a := by
  funext j
  by_cases hj : j = 0
  · subst j
    simp [collapseZeroCoords, step_apply]
  · have hjsucc : j.succ ≠ (1 : Fin (n + 2)) := by
      intro h
      apply hj
      have hone : (1 : Fin (n + 2)) =
          (0 : Fin (n + 1)).succ := by
        apply Fin.ext
        simp
      rw [hone] at h
      exact Fin.succ_inj.mp h
    simp [collapseZeroCoords, hj, step_apply, hjsucc]

/-- Every other high transfer becomes its predecessor transfer after
collapsing coordinate zero. -/
theorem collapseZeroCoords_step_of_ne {n : ℕ}
    (i : Fin (n + 1)) (hi : i ≠ 0) (a : Fin (n + 2) → ℤ) :
    collapseZeroCoords (step i a) =
      step (i.pred hi) (collapseZeroCoords a) := by
  funext j
  have hzero : step i a 0 = a 0 := by
    have hiCast : (0 : Fin (n + 2)) ≠ i.castSucc := by
      intro h
      apply hi
      apply Fin.ext
      simpa using congrArg Fin.val h.symm
    have hiSucc : (0 : Fin (n + 2)) ≠ i.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [step_apply, hiCast, hiSucc]
  have herase := congrFun (eraseCoords_zero_step_of_ne i hi a) j
  change step i a j.succ + (if j = 0 then step i a 0 else 0) =
    step (i.pred hi) (collapseZeroCoords a) j
  rw [hzero]
  change eraseCoords 0 (step i a) j +
      (if j = 0 then a 0 else 0) =
    step (i.pred hi) (collapseZeroCoords a) j
  rw [herase]
  rw [step_apply, step_apply]
  simp only [collapseZeroCoords]
  rw [show eraseCoords 0 a j = a j.succ by rfl]
  split <;> ring

/-- Collapsing every vertex of a high transfer simplex and deleting transfer
zero gives exactly the lower transfer simplex. -/
theorem image_collapseZeroCoords_stepSimplex {n : ℕ}
    (a : Fin (n + 2) → ℤ) (l : List (Fin (n + 1))) :
    (stepSimplex a l).image collapseZeroCoords =
      stepSimplex (collapseZeroCoords a) (dropZeroList l) := by
  induction l generalizing a with
  | nil => simp [stepSimplex, stepSequence, dropZeroList]
  | cons i l ih =>
      by_cases hi : i = 0
      · subst i
        rw [stepSimplex]
        simp only [stepSequence, List.toFinset_cons, Finset.image_insert]
        rw [dropZeroList, List.filterMap_cons]
        simp only [dropZeroIndex]
        change insert (collapseZeroCoords a)
            ((stepSimplex (step 0 a) l).image collapseZeroCoords) =
          stepSimplex (collapseZeroCoords a) (dropZeroList l)
        rw [ih, collapseZeroCoords_step_zero]
        apply Finset.insert_eq_self.mpr
        cases dropZeroList l <;> simp [stepSimplex, stepSequence]
      · rw [stepSimplex]
        simp only [stepSequence, List.toFinset_cons, Finset.image_insert]
        rw [dropZeroList, List.filterMap_cons]
        simp only [dropZeroIndex, dif_neg hi]
        change insert (collapseZeroCoords a)
            ((stepSimplex (step i a) l).image collapseZeroCoords) =
          stepSimplex (collapseZeroCoords a)
            (i.pred hi :: dropZeroList l)
        rw [ih]
        simp only [stepSimplex, stepSequence, List.toFinset_cons]
        rw [collapseZeroCoords_step_of_ne i hi]

/-- For a positive deleted coordinate `k`, merge its mass into the preceding
coordinate and then delete it.  This is the linear-coordinate contraction
adapted to the adjacent transfers defining Freudenthal simplices. -/
def collapsePositiveCoords {n : ℕ} (k : Fin (n + 2)) (hk : k ≠ 0)
    (b : Fin (n + 2) → ℤ) : Fin (n + 1) → ℤ :=
  fun j ↦ b (k.succAbove j) + if j = k.pred hk then b k else 0

theorem collapsePositiveCoords_isPoint {n : ℕ} {N : ℤ}
    (k : Fin (n + 2)) (hk : k ≠ 0) {b : Fin (n + 2) → ℤ}
    (hb : IsPoint N b) : IsPoint N (collapsePositiveCoords k hk b) := by
  constructor
  · intro j
    simp only [collapsePositiveCoords]
    split
    · exact add_nonneg (hb.1 _) (hb.1 k)
    · simpa using hb.1 (k.succAbove j)
  · have hsum :
        (∑ j, collapsePositiveCoords k hk b j) =
          (∑ j, b (k.succAbove j)) + b k := by
      simp [collapsePositiveCoords, Finset.sum_add_distrib]
    rw [hsum, add_comm, ← Fin.sum_univ_succAbove b k, hb.2]

theorem collapsePositiveCoords_eq_erase_of_zero {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) {b : Fin (n + 2) → ℤ}
    (hbk : b k = 0) :
    collapsePositiveCoords k hk b = eraseCoords k b := by
  funext j
  simp [collapsePositiveCoords, eraseCoords, hbk]

/-- The high transfer immediately preceding a positive deleted coordinate
only redistributes mass inside the merged coordinate, so contraction makes
it invisible. -/
theorem collapsePositiveCoords_step_pred {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (a : Fin (n + 2) → ℤ) :
    collapsePositiveCoords k hk (step (k.pred hk) a) =
      collapsePositiveCoords k hk a := by
  funext j
  simp only [collapsePositiveCoords, step_apply]
  by_cases hj : j = k.pred hk
  · subst j
    have hsucc : (k.pred hk).succ = k := Fin.succ_pred k hk
    have hlt : (k.pred hk).castSucc < k := by
      simpa [hsucc] using
        (Fin.castSucc_lt_succ (i := k.pred hk))
    have habove : k.succAbove (k.pred hk) = (k.pred hk).castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact hlt
    rw [habove, hsucc]
    simp [ne_of_lt hlt, ne_of_gt hlt]
  · have haboveNeCast : k.succAbove j ≠ (k.pred hk).castSucc := by
      intro h
      have hpivot : k.succAbove (k.pred hk) =
          (k.pred hk).castSucc := by
        rw [Fin.succAbove_of_castSucc_lt]
        simpa [Fin.succ_pred k hk] using
          (Fin.castSucc_lt_succ (i := k.pred hk))
      exact hj ((Fin.succAboveEmb k).injective (h.trans hpivot.symm))
    have haboveNeSucc : k.succAbove j ≠ (k.pred hk).succ := by
      rw [Fin.succ_pred k hk]
      exact Fin.succAbove_ne k j
    simp [hj, haboveNeCast]

/-- The coordinate surjection implemented by `collapsePositiveCoords`: the
deleted coordinate maps to its predecessor, and every other coordinate is
the inverse image of `k.succAbove`. -/
noncomputable def collapsePositiveIndex {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (q : Fin (n + 2)) : Fin (n + 1) :=
  if hq : q = k then k.pred hk
  else Classical.choose (Fin.exists_succAbove_eq hq)

@[simp]
theorem collapsePositiveIndex_self {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) :
    collapsePositiveIndex k hk k = k.pred hk := by
  simp [collapsePositiveIndex]

@[simp]
theorem collapsePositiveIndex_succAbove {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (j : Fin (n + 1)) :
    collapsePositiveIndex k hk (k.succAbove j) = j := by
  rw [collapsePositiveIndex, dif_neg (Fin.succAbove_ne k j)]
  apply (Fin.succAboveEmb k).injective
  exact Classical.choose_spec
    (Fin.exists_succAbove_eq (Fin.succAbove_ne k j))

theorem collapsePositiveIndex_val {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (q : Fin (n + 2)) :
    (collapsePositiveIndex k hk q).val =
      if q < k then q.val else q.val - 1 := by
  by_cases hq : q = k
  · subst q
    simp [collapsePositiveIndex, Fin.val_pred]
  · rw [collapsePositiveIndex, dif_neg hq]
    let p : Fin (n + 1) :=
      Classical.choose (Fin.exists_succAbove_eq hq)
    have hspec : k.succAbove p = q :=
      Classical.choose_spec (Fin.exists_succAbove_eq hq)
    by_cases hp : p.castSucc < k
    · rw [Fin.succAbove_of_castSucc_lt _ _ hp] at hspec
      have hqk : q < k := by simpa [← hspec] using hp
      rw [if_pos hqk]
      exact congrArg Fin.val hspec
    · have hle : k ≤ p.castSucc := Fin.not_lt.mp hp
      rw [Fin.succAbove_of_le_castSucc _ _ hle] at hspec
      have hnqk : ¬q < k := by
        rw [← hspec]
        exact not_lt_of_ge (hle.trans (Fin.castSucc_le_succ p))
      rw [if_neg hnqk]
      have hv := congrArg Fin.val hspec
      simp only [Fin.val_succ] at hv
      omega

/-- Contraction sends a coordinate delta function to the delta function at
the contracted coordinate index. -/
theorem collapsePositiveCoords_single {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (q : Fin (n + 2)) (z : ℤ) :
    collapsePositiveCoords k hk (Pi.single q z) =
      Pi.single (collapsePositiveIndex k hk q) z := by
  funext j
  by_cases hq : q = k
  · subst q
    simp [collapsePositiveCoords, Pi.single_apply, Fin.succAbove_ne]
  · have hspec : k.succAbove (collapsePositiveIndex k hk q) = q := by
      rw [collapsePositiveIndex, dif_neg hq]
      exact Classical.choose_spec (Fin.exists_succAbove_eq hq)
    by_cases hj : j = collapsePositiveIndex k hk q
    · subst j
      simp [collapsePositiveCoords, hspec, hq]
    · have hne : k.succAbove j ≠ q := by
        intro h
        apply hj
        apply (Fin.succAboveEmb k).injective
        exact h.trans hspec.symm
      simp [collapsePositiveCoords, hne, hq, hj]

theorem collapsePositiveCoords_add {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0)
    (a b : Fin (n + 2) → ℤ) :
    collapsePositiveCoords k hk (a + b) =
      collapsePositiveCoords k hk a + collapsePositiveCoords k hk b := by
  funext j
  simp only [collapsePositiveCoords, Pi.add_apply]
  split <;> ring

theorem collapsePositiveCoords_sub {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0)
    (a b : Fin (n + 2) → ℤ) :
    collapsePositiveCoords k hk (a - b) =
      collapsePositiveCoords k hk a - collapsePositiveCoords k hk b := by
  funext j
  simp only [collapsePositiveCoords, Pi.sub_apply]
  split <;> ring

theorem collapsePositiveIndex_step_target {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (i : Fin n) :
    collapsePositiveIndex k hk
        (((k.pred hk).succAbove i).castSucc) = i.castSucc := by
  by_cases hi : i.castSucc < k.pred hk
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    apply Fin.ext
    rw [collapsePositiveIndex_val]
    simp only [Fin.val_castSucc]
    have hlt : i.castSucc.castSucc < k := by
      change i.val < k.val
      have hkpos : 0 < k.val := Fin.pos_iff_ne_zero.mpr hk
      change i.val < (k.pred hk).val at hi
      rw [Fin.val_pred] at hi
      omega
    rw [if_pos hlt]
  · have hle : k.pred hk ≤ i.castSucc := Fin.not_lt.mp hi
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    apply Fin.ext
    rw [collapsePositiveIndex_val]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hnlt : ¬i.succ.castSucc < k := by
      change ¬i.val + 1 < k.val
      have hkpos : 0 < k.val := Fin.pos_iff_ne_zero.mpr hk
      change (k.pred hk).val ≤ i.val at hle
      rw [Fin.val_pred] at hle
      omega
    rw [if_neg hnlt]
    omega

theorem collapsePositiveIndex_step_source {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (i : Fin n) :
    collapsePositiveIndex k hk (((k.pred hk).succAbove i).succ) =
      i.succ := by
  have hsource : ((k.pred hk).succAbove i).succ =
      k.succAbove i.succ := calc
    ((k.pred hk).succAbove i).succ =
        (k.pred hk).succ.succAbove i.succ :=
      (Fin.succ_succAbove_succ (k.pred hk) i).symm
    _ = k.succAbove i.succ := by rw [Fin.succ_pred k hk]
  rw [hsource, collapsePositiveIndex_succAbove]

/-- Every high transfer other than the invisible predecessor transfer
contracts to the uniquely corresponding lower transfer. -/
theorem collapsePositiveCoords_step_succAbove_pred {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (i : Fin n)
    (a : Fin (n + 2) → ℤ) :
    collapsePositiveCoords k hk
        (step ((k.pred hk).succAbove i) a) =
      step i (collapsePositiveCoords k hk a) := by
  rw [step, collapsePositiveCoords_sub, collapsePositiveCoords_add,
    collapsePositiveCoords_single, collapsePositiveCoords_single,
    collapsePositiveIndex_step_target, collapsePositiveIndex_step_source]
  rfl

/-- Delete the high transfer immediately preceding a positive face
coordinate and reindex every other transfer in the lower dimension. -/
noncomputable def dropPositiveIndex {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (r : Fin (n + 1)) : Option (Fin n) :=
  if hr : r = k.pred hk then none
  else some (Classical.choose (Fin.exists_succAbove_eq hr))

@[simp]
theorem dropPositiveIndex_self {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) :
    dropPositiveIndex k hk (k.pred hk) = none := by
  simp [dropPositiveIndex]

@[simp]
theorem dropPositiveIndex_succAbove {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (i : Fin n) :
    dropPositiveIndex k hk ((k.pred hk).succAbove i) = some i := by
  rw [dropPositiveIndex, dif_neg (Fin.succAbove_ne (k.pred hk) i)]
  congr 1
  apply (Fin.succAboveEmb (k.pred hk)).injective
  exact Classical.choose_spec
    (Fin.exists_succAbove_eq (Fin.succAbove_ne (k.pred hk) i))

noncomputable def dropPositiveList {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0)
    (l : List (Fin (n + 1))) : List (Fin n) :=
  l.filterMap (dropPositiveIndex k hk)

theorem dropPositiveList_permutation_nodup {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0)
    (Omega : Equiv.Perm (Fin (n + 1))) :
    (dropPositiveList k hk (permutationList Omega)).Nodup := by
  apply (nodup_permutationList Omega).filterMap
  intro r s q hr hs
  by_cases hrp : r = k.pred hk
  · simp [dropPositiveIndex, hrp] at hr
  · by_cases hsp : s = k.pred hk
    · simp [dropPositiveIndex, hsp] at hs
    · simp only [dropPositiveIndex, dif_neg hrp, dif_neg hsp,
        Option.mem_def] at hr hs
      have hrq : Classical.choose (Fin.exists_succAbove_eq hrp) = q :=
        Option.some.inj hr
      have hsq : Classical.choose (Fin.exists_succAbove_eq hsp) = q :=
        Option.some.inj hs
      calc
        r = (k.pred hk).succAbove
            (Classical.choose (Fin.exists_succAbove_eq hrp)) :=
          (Classical.choose_spec (Fin.exists_succAbove_eq hrp)).symm
        _ = (k.pred hk).succAbove q := by rw [hrq]
        _ = (k.pred hk).succAbove
            (Classical.choose (Fin.exists_succAbove_eq hsp)) := by rw [hsq]
        _ = s := Classical.choose_spec (Fin.exists_succAbove_eq hsp)

theorem mem_dropPositiveList_permutation {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0)
    (Omega : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    i ∈ dropPositiveList k hk (permutationList Omega) := by
  rw [dropPositiveList, List.mem_filterMap]
  refine ⟨(k.pred hk).succAbove i, ?_, ?_⟩
  · rw [permutationList, List.mem_ofFn]
    exact Omega.surjective ((k.pred hk).succAbove i)
  · exact dropPositiveIndex_succAbove k hk i

theorem dropPositiveList_permutation_length {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0)
    (Omega : Equiv.Perm (Fin (n + 1))) :
    (dropPositiveList k hk (permutationList Omega)).length = n := by
  let l := dropPositiveList k hk (permutationList Omega)
  have hlNodup : l.Nodup := dropPositiveList_permutation_nodup k hk Omega
  have hlUniv : l.toFinset = Finset.univ := by
    ext i
    simp [l, mem_dropPositiveList_permutation k hk Omega i]
  rw [← List.toFinset_card_of_nodup hlNodup, hlUniv]
  simp

theorem exists_dropPositivePermutation {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0)
    (Omega : Equiv.Perm (Fin (n + 1))) :
    ∃ omega : Equiv.Perm (Fin n),
      permutationList omega =
        dropPositiveList k hk (permutationList Omega) :=
  exists_permutationList_eq_of_nodup_length _
    (dropPositiveList_permutation_nodup k hk Omega)
    (dropPositiveList_permutation_length k hk Omega)

/-- Contraction commutes with an arbitrary nondeleted high transfer after
reindexing it through `dropPositiveIndex`. -/
theorem collapsePositiveCoords_step_of_ne_pred {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0) (r : Fin (n + 1))
    (hr : r ≠ k.pred hk) (a : Fin (n + 2) → ℤ) :
    collapsePositiveCoords k hk (step r a) =
      step (Classical.choose (Fin.exists_succAbove_eq hr))
        (collapsePositiveCoords k hk a) := by
  let i : Fin n := Classical.choose (Fin.exists_succAbove_eq hr)
  have hrspec : (k.pred hk).succAbove i = r :=
    Classical.choose_spec (Fin.exists_succAbove_eq hr)
  change collapsePositiveCoords k hk (step r a) =
    step i (collapsePositiveCoords k hk a)
  calc
    collapsePositiveCoords k hk (step r a) =
        collapsePositiveCoords k hk
          (step ((k.pred hk).succAbove i) a) := by rw [hrspec]
    _ = step i (collapsePositiveCoords k hk a) :=
      collapsePositiveCoords_step_succAbove_pred k hk i a

/-- Contracting all vertices of a high transfer simplex and deleting its
invisible predecessor transfer gives exactly the lower transfer simplex. -/
theorem image_collapsePositiveCoords_stepSimplex {n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0)
    (a : Fin (n + 2) → ℤ) (l : List (Fin (n + 1))) :
    (stepSimplex a l).image (collapsePositiveCoords k hk) =
      stepSimplex (collapsePositiveCoords k hk a)
        (dropPositiveList k hk l) := by
  induction l generalizing a with
  | nil => simp [stepSimplex, stepSequence, dropPositiveList]
  | cons r l ih =>
      by_cases hr : r = k.pred hk
      · subst r
        rw [stepSimplex]
        simp only [stepSequence, List.toFinset_cons, Finset.image_insert]
        rw [dropPositiveList, List.filterMap_cons]
        simp only [dropPositiveIndex_self]
        change insert (collapsePositiveCoords k hk a)
            ((stepSimplex (step (k.pred hk) a) l).image
              (collapsePositiveCoords k hk)) =
          stepSimplex (collapsePositiveCoords k hk a)
            (dropPositiveList k hk l)
        rw [ih, collapsePositiveCoords_step_pred]
        apply Finset.insert_eq_self.mpr
        cases dropPositiveList k hk l <;>
          simp [stepSimplex, stepSequence]
      · rw [stepSimplex]
        simp only [stepSequence, List.toFinset_cons, Finset.image_insert]
        rw [dropPositiveList, List.filterMap_cons]
        simp only [dropPositiveIndex, dif_neg hr]
        change insert (collapsePositiveCoords k hk a)
            ((stepSimplex (step r a) l).image
              (collapsePositiveCoords k hk)) =
          stepSimplex (collapsePositiveCoords k hk a)
            (Classical.choose (Fin.exists_succAbove_eq hr) ::
              dropPositiveList k hk l)
        rw [ih]
        simp only [stepSimplex, stepSequence, List.toFinset_cons]
        rw [collapsePositiveCoords_step_of_ne_pred k hk r hr a]

/-- The unique lower transfer crossing the gap after deleting a nonlast
coordinate. -/
def interiorBridge {n : ℕ} (d : Fin (n + 1))
    (hd : d ≠ Fin.last n) : Fin n := d.castPred hd

@[simp]
theorem interiorBridge_castSucc {n : ℕ} (d : Fin (n + 1))
    (hd : d ≠ Fin.last n) :
    (interiorBridge d hd).castSucc = d := by
  exact Fin.castSucc_castPred d hd

@[simp]
theorem succAbove_interiorBridge {n : ℕ} (d : Fin (n + 1))
    (hd : d ≠ Fin.last n) :
    d.succAbove (interiorBridge d hd) = (interiorBridge d hd).succ := by
  have hle : d ≤ (interiorBridge d hd).castSucc := by
    rw [interiorBridge_castSucc]
  rw [Fin.succAbove_of_le_castSucc _ _ hle]

/-- Away from the bridge transfer, the target coordinate of an embedded
lower transfer is the embedded lower target coordinate. -/
theorem succAbove_transfer_target {n : ℕ} (d : Fin (n + 1))
    (hd : d ≠ Fin.last n) (i : Fin n)
    (hi : i ≠ interiorBridge d hd) :
    (d.succAbove i).castSucc = d.succ.succAbove i.castSucc := by
  by_cases hilow : i.castSucc < d
  · rw [Fin.succAbove_of_castSucc_lt _ _ hilow]
    have hlt : i.castSucc.castSucc < d.succ := by
      change i.val < d.val + 1
      change i.val < d.val at hilow
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
  · have hdle : d ≤ i.castSucc := Fin.not_lt.mp hilow
    have hdne : d ≠ i.castSucc := by
      intro h
      apply hi
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp [interiorBridge] at hv ⊢
      exact hv.symm
    have hdlt : d < i.castSucc := lt_of_le_of_ne hdle hdne
    rw [Fin.succAbove_of_le_castSucc _ _ hdle]
    rw [Fin.succAbove_of_le_castSucc]
    · rfl
    · change d.val + 1 ≤ i.val
      change d.val < i.val at hdlt
      omega

/-- The source coordinate identity holds even at the bridge transfer. -/
theorem succAbove_transfer_source {n : ℕ} (d : Fin (n + 1))
    (i : Fin n) :
    (d.succAbove i).succ = d.succ.succAbove i.succ :=
  (Fin.succ_succAbove_succ d i).symm

/-- Every nonbridge lower transfer is implemented by one high transfer and
keeps the inserted coordinate identically zero. -/
theorem step_succAbove_insertZeroCoords_interior_of_ne {n : ℕ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (i : Fin n) (hi : i ≠ interiorBridge d hd)
    (a : Fin (n + 1) → ℤ) :
    step (d.succAbove i) (insertZeroCoords d.succ a) =
      insertZeroCoords d.succ (step i a) := by
  funext q
  by_cases hq : q = d.succ
  · subst q
    rw [step_apply]
    have ht : (d.succAbove i).castSucc ≠ d.succ := by
      rw [succAbove_transfer_target d hd i hi]
      exact Fin.succAbove_ne d.succ i.castSucc
    have hs : (d.succAbove i).succ ≠ d.succ := by
      rw [succAbove_transfer_source]
      exact Fin.succAbove_ne d.succ i.succ
    simp [insertZeroCoords_apply_self, ht.symm, hs.symm]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq
    rw [← hj, step_apply, succAbove_transfer_target d hd i hi,
      succAbove_transfer_source, insertZeroCoords_apply_succAbove,
      insertZeroCoords_apply_succAbove, step_apply]
    simp only [Fin.succAbove_right_inj]

/-- The bridge lower transfer expands into two adjacent high transfers.  The
first enters the inserted coordinate and the second returns to the face. -/
theorem step_pair_insertZeroCoords_interior {n : ℕ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (a : Fin (n + 1) → ℤ) :
    step d (step (d.succAbove (interiorBridge d hd))
        (insertZeroCoords d.succ a)) =
      insertZeroCoords d.succ (step (interiorBridge d hd) a) := by
  let b : Fin n := interiorBridge d hd
  let r : Fin (n + 1) := d.succAbove b
  have hbcast : b.castSucc = d := interiorBridge_castSucc d hd
  have hrtarget : r.castSucc = d.succ := by
    apply Fin.ext
    simp [r, b, interiorBridge]
  have hrsource : r.succ = d.succ.succAbove b.succ := by
    exact succAbove_transfer_source d b
  have hdtarget : d.castSucc = d.succ.succAbove b.castSucc := by
    rw [hbcast, Fin.succAbove_of_castSucc_lt]
    exact Fin.castSucc_lt_succ
  change step d (step r (insertZeroCoords d.succ a)) =
    insertZeroCoords d.succ (step b a)
  funext q
  by_cases hq : q = d.succ
  · subst q
    rw [step_apply, step_apply]
    have hdc : d.castSucc ≠ d.succ := by simp [Fin.ext_iff]
    have hrs : r.succ ≠ d.succ := by
      rw [hrsource]
      exact Fin.succAbove_ne d.succ b.succ
    simp [insertZeroCoords_apply_self, hdc.symm,
      hrtarget, hrs.symm]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq
    rw [← hj, step_apply, step_apply, hrtarget, hrsource, hdtarget,
      insertZeroCoords_apply_succAbove,
      insertZeroCoords_apply_succAbove, step_apply]
    have heqSource :
        d.succ.succAbove j = d.succ.succAbove b.succ ↔
          j = b.succ := Fin.succAbove_right_inj
    rw [if_congr heqSource rfl rfl]
    simp [Fin.succAbove_ne]
    ring

/-- Expand the unique bridge transfer into two adjacent high transfers and
embed every other lower transfer through `d.succAbove`. -/
def interiorFaceLiftList {n : ℕ} (d : Fin (n + 1))
    (hd : d ≠ Fin.last n) : List (Fin n) → List (Fin (n + 1))
  | [] => []
  | i :: l =>
      if i = interiorBridge d hd then
        d.succAbove i :: d :: interiorFaceLiftList d hd l
      else d.succAbove i :: interiorFaceLiftList d hd l

theorem mem_interiorFaceLiftList_iff {n : ℕ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (l : List (Fin n)) (r : Fin (n + 1)) :
    r ∈ interiorFaceLiftList d hd l ↔
      (r = d ∧ interiorBridge d hd ∈ l) ∨
        ∃ i ∈ l, r = d.succAbove i := by
  induction l with
  | nil => simp [interiorFaceLiftList]
  | cons i l ih =>
      by_cases hi : i = interiorBridge d hd
      · subst i
        simp [interiorFaceLiftList, ih]
        tauto
      · simp [interiorFaceLiftList, hi, ih]
        aesop

theorem interiorFaceLiftList_length {n : ℕ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (l : List (Fin n)) :
    (interiorFaceLiftList d hd l).length =
      l.length + l.count (interiorBridge d hd) := by
  induction l with
  | nil => simp [interiorFaceLiftList]
  | cons i l ih =>
      by_cases hi : i = interiorBridge d hd
      · subst i
        simp [interiorFaceLiftList, ih]
        omega
      · simp [interiorFaceLiftList, hi, ih]
        omega

theorem interiorFaceLiftList_permutation_length {n : ℕ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (omega : Equiv.Perm (Fin n)) :
    (interiorFaceLiftList d hd (permutationList omega)).length = n + 1 := by
  rw [interiorFaceLiftList_length, length_permutationList]
  have hbmem : interiorBridge d hd ∈ permutationList omega := by
    simpa [permutationList] using omega.surjective (interiorBridge d hd)
  rw [List.count_eq_one_of_mem (nodup_permutationList omega) hbmem]

theorem interiorFaceLiftList_permutation_toFinset {n : ℕ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (omega : Equiv.Perm (Fin n)) :
    (interiorFaceLiftList d hd
      (permutationList omega)).toFinset = Finset.univ := by
  ext r
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  rw [mem_interiorFaceLiftList_iff]
  by_cases hr : r = d
  · left
    refine ⟨hr, ?_⟩
    simpa [permutationList] using omega.surjective (interiorBridge d hd)
  · right
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hr
    refine ⟨i, ?_, hi.symm⟩
    simpa [permutationList] using omega.surjective i

theorem interiorFaceLiftList_permutation_nodup {n : ℕ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (omega : Equiv.Perm (Fin n)) :
    (interiorFaceLiftList d hd (permutationList omega)).Nodup := by
  rw [← Multiset.coe_nodup]
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  change (interiorFaceLiftList d hd
      (permutationList omega)).toFinset.card =
    (interiorFaceLiftList d hd (permutationList omega)).length
  rw [interiorFaceLiftList_permutation_toFinset,
    interiorFaceLiftList_permutation_length]
  simp

theorem exists_interiorFaceLiftPermutation {n : ℕ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (omega : Equiv.Perm (Fin n)) :
    ∃ Omega : Equiv.Perm (Fin (n + 1)),
      permutationList Omega =
        interiorFaceLiftList d hd (permutationList omega) :=
  exists_permutationList_eq_of_nodup_length _
    (interiorFaceLiftList_permutation_nodup d hd omega)
    (interiorFaceLiftList_permutation_length d hd omega)

/-- The temporary off-face vertex created by the first half of the bridge is
still a point of the integer simplex.  Its only potentially problematic
coordinate is exactly the source of the valid lower bridge transfer. -/
theorem step_succAbove_interiorBridge_isPoint {n : ℕ} {N : ℤ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (a : Fin (n + 1) → ℤ)
    (ha : IsPoint N a)
    (hnext : IsPoint N (step (interiorBridge d hd) a)) :
    IsPoint N
      (step (d.succAbove (interiorBridge d hd))
        (insertZeroCoords d.succ a)) := by
  let b : Fin n := interiorBridge d hd
  have hsource : 0 < a b.succ := by
    have hnonneg := hnext.1 b.succ
    change 0 ≤ step b a b.succ at hnonneg
    rw [step_apply] at hnonneg
    have hne : b.succ ≠ b.castSucc := by simp [Fin.ext_iff]
    simp only [if_neg hne, if_pos] at hnonneg
    omega
  apply step_isPoint
  · exact insertZeroCoords_isPoint d.succ ha
  · rw [succAbove_transfer_source,
      insertZeroCoords_apply_succAbove]
    exact hsource

theorem base_mem_stepSequence {n : ℕ}
    (a : Fin (n + 1) → ℤ) (l : List (Fin n)) :
    a ∈ stepSequence a l := by
  cases l <;> simp [stepSequence]

/-- Every embedded lower vertex occurs in the lifted interior-face transfer
sequence.  At the bridge it occurs after two high transfers; elsewhere it
occurs after one. -/
theorem mem_stepSequence_interiorFaceLiftList_of_mem {n : ℕ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (a : Fin (n + 1) → ℤ) (l : List (Fin n))
    {x : Fin (n + 1) → ℤ}
    (hx : x ∈ stepSequence a l) :
    insertZeroCoords d.succ x ∈
      stepSequence (insertZeroCoords d.succ a)
        (interiorFaceLiftList d hd l) := by
  induction l generalizing a x with
  | nil =>
      have hxa : x = a := by simpa [stepSequence] using hx
      subst x
      simp [interiorFaceLiftList, stepSequence]
  | cons i l ih =>
      simp only [stepSequence, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact base_mem_stepSequence _ _
      · by_cases hi : i = interiorBridge d hd
        · subst i
          simp only [interiorFaceLiftList]
          right
          right
          rw [step_pair_insertZeroCoords_interior]
          exact ih (a := step (interiorBridge d hd) a) (x := x) hx
        · simp only [interiorFaceLiftList, if_neg hi, stepSequence,
            List.mem_cons]
          right
          rw [step_succAbove_insertZeroCoords_interior_of_ne d hd i hi]
          exact ih (a := step i a) (x := x) hx

/-- If all lower vertices are genuine simplex points, then so is every
vertex of the lifted interior-face transfer sequence, including the unique
temporary off-face bridge vertex. -/
theorem interiorFaceLiftList_stepSequence_isPoint {n : ℕ} {N : ℤ}
    (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    (a : Fin (n + 1) → ℤ) (l : List (Fin n))
    (hlow : ∀ x ∈ stepSequence a l, IsPoint N x) :
    ∀ y ∈ stepSequence (insertZeroCoords d.succ a)
        (interiorFaceLiftList d hd l), IsPoint N y := by
  induction l generalizing a with
  | nil =>
      intro y hy
      have hyeq : y = insertZeroCoords d.succ a := by
        simpa [interiorFaceLiftList, stepSequence] using hy
      subst y
      exact insertZeroCoords_isPoint d.succ
        (hlow a (by simp [stepSequence]))
  | cons i l ih =>
      have ha : IsPoint N a := hlow a (by simp [stepSequence])
      have htail : ∀ x ∈ stepSequence (step i a) l, IsPoint N x := by
        intro x hx
        exact hlow x (by simp only [stepSequence, List.mem_cons]; exact Or.inr hx)
      intro y hy
      by_cases hi : i = interiorBridge d hd
      · subst i
        rw [interiorFaceLiftList, if_pos rfl, stepSequence,
          stepSequence] at hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | rfl | hy
        · exact insertZeroCoords_isPoint d.succ ha
        · apply step_succAbove_interiorBridge_isPoint d hd a ha
          exact htail _ (base_mem_stepSequence _ _)
        · rw [step_pair_insertZeroCoords_interior] at hy
          exact ih (step (interiorBridge d hd) a) htail y hy
      · simp only [interiorFaceLiftList, if_neg hi, stepSequence,
          List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact insertZeroCoords_isPoint d.succ ha
        · rw [step_succAbove_insertZeroCoords_interior_of_ne d hd i hi] at hy
          exact ih (step i a) htail y hy

/-- Before entering the last coordinate face, move one unit of mass from the
last lower coordinate into the new last coordinate. -/
def lastFaceBase {n : ℕ} (a : Fin (n + 1) → ℤ) :
    Fin (n + 2) → ℤ :=
  insertZeroCoords (Fin.last (n + 1)) a -
      Pi.single (Fin.last n).castSucc 1 +
    Pi.single (Fin.last (n + 1)) 1

/-- The missing last high transfer takes `lastFaceBase a` exactly to the
embedded lower base point. -/
theorem step_lastFaceBase {n : ℕ} (a : Fin (n + 1) → ℤ) :
    step (Fin.last n) (lastFaceBase a) =
      insertZeroCoords (Fin.last (n + 1)) a := by
  funext q
  rw [step_apply]
  simp only [lastFaceBase, Pi.sub_apply, Pi.add_apply, Pi.single_apply]
  have hsource : (Fin.last n).succ = Fin.last (n + 1) := by
    apply Fin.ext
    simp
  rw [hsource]
  ring

/-- `lastFaceBase` is a genuine integer-simplex point exactly under the
positivity needed to remove one unit from the last lower coordinate. -/
theorem lastFaceBase_isPoint {n : ℕ} {N : ℤ}
    (a : Fin (n + 1) → ℤ) (ha : IsPoint N a)
    (hlast : 0 < a (Fin.last n)) :
    IsPoint N (lastFaceBase a) := by
  let k : Fin (n + 2) := Fin.last (n + 1)
  let d : Fin (n + 1) := Fin.last n
  have hins : IsPoint N (insertZeroCoords k a) :=
    insertZeroCoords_isPoint k ha
  constructor
  · intro q
    by_cases hqk : q = k
    · subst q
      have hdk : d.castSucc ≠ k := by simp [d, k, Fin.ext_iff]
      simp [lastFaceBase, d, k, hdk]
    · by_cases hqd : q = d.castSucc
      · subst q
        have hdk : d.castSucc ≠ k := by simp [d, k, Fin.ext_iff]
        have hinsert : insertZeroCoords k a d.castSucc = a d := by
          rw [← Fin.succAbove_last_apply d,
            insertZeroCoords_apply_succAbove]
        simp only [lastFaceBase, Pi.sub_apply, Pi.add_apply,
          Pi.single_apply]
        rw [hinsert]
        change 0 < a d at hlast
        simpa [d, k] using (show 0 ≤ a d - 1 by omega)
      · have hnonneg := hins.1 q
        simp [lastFaceBase, d, k, hqk, hqd]
        exact hnonneg
  · have hsum := hins.2
    simp only [lastFaceBase, Pi.sub_apply, Pi.add_apply]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum]
    simp

/-- Embedding at the last coordinate commutes with every lower transfer. -/
theorem step_castSucc_insertZeroCoords_last {n : ℕ}
    (i : Fin n) (a : Fin (n + 1) → ℤ) :
    step i.castSucc (insertZeroCoords (Fin.last (n + 1)) a) =
      insertZeroCoords (Fin.last (n + 1)) (step i a) := by
  funext q
  by_cases hq : q = Fin.last (n + 1)
  · subst q
    have ht : (Fin.last (n + 1)) ≠ i.castSucc.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have hs : (Fin.last (n + 1)) ≠ i.castSucc.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp [step_apply, ht, hs]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq
    rw [← hj, Fin.succAbove_last_apply, step_apply,
      show insertZeroCoords (Fin.last (n + 1)) a j.castSucc = a j by
        rw [← Fin.succAbove_last_apply j,
          insertZeroCoords_apply_succAbove],
      show insertZeroCoords (Fin.last (n + 1)) (step i a) j.castSucc =
          step i a j by
        rw [← Fin.succAbove_last_apply j,
          insertZeroCoords_apply_succAbove],
      step_apply]
    simp [Fin.ext_iff]

/-- Transfer sequences commute with last-coordinate insertion after mapping
all lower transfer indices by `castSucc`. -/
theorem stepSequence_map_castSucc_insertZeroCoords_last {n : ℕ}
    (a : Fin (n + 1) → ℤ) (l : List (Fin n)) :
    stepSequence (insertZeroCoords (Fin.last (n + 1)) a)
        (l.map Fin.castSucc) =
      (stepSequence a l).map
        (insertZeroCoords (Fin.last (n + 1))) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, stepSequence]
      rw [step_castSucc_insertZeroCoords_last, ih]

/-- The last-face lift first performs the missing last transfer and then
follows the embedded lower permutation. -/
def lastFaceLiftList {n : ℕ} (omega : Equiv.Perm (Fin n)) :
    List (Fin (n + 1)) :=
  Fin.last n :: (permutationList omega).map Fin.castSucc

theorem lastFaceLiftList_nodup {n : ℕ} (omega : Equiv.Perm (Fin n)) :
    (lastFaceLiftList omega).Nodup := by
  rw [lastFaceLiftList, List.nodup_cons]
  constructor
  · simp
  · exact (nodup_permutationList omega).map (Fin.castSucc_injective n)

@[simp]
theorem lastFaceLiftList_length {n : ℕ} (omega : Equiv.Perm (Fin n)) :
    (lastFaceLiftList omega).length = n + 1 := by
  simp [lastFaceLiftList]

theorem exists_lastFaceLiftPermutation {n : ℕ}
    (omega : Equiv.Perm (Fin n)) :
    ∃ Omega : Equiv.Perm (Fin (n + 1)),
      permutationList Omega = lastFaceLiftList omega :=
  exists_permutationList_eq_of_nodup_length _
    (lastFaceLiftList_nodup omega) (lastFaceLiftList_length omega)

/-- Exact decomposition of the last-face lifted path into its initial
off-face vertex and the embedded lower path. -/
theorem stepSequence_lastFaceLiftList {n : ℕ}
    (a : Fin (n + 1) → ℤ) (omega : Equiv.Perm (Fin n)) :
    stepSequence (lastFaceBase a) (lastFaceLiftList omega) =
      lastFaceBase a ::
        (stepSequence a (permutationList omega)).map
          (insertZeroCoords (Fin.last (n + 1))) := by
  rw [lastFaceLiftList, stepSequence, step_lastFaceBase,
    stepSequence_map_castSucc_insertZeroCoords_last]

/-- The last coordinate is decreased precisely when the last transfer index
occurs.  No transfer can increase that coordinate. -/
theorem stepEndpoint_apply_last {m : ℕ}
    (a : Fin (m + 2) → ℤ) (l : List (Fin (m + 1))) :
    stepEndpoint a l (Fin.last (m + 1)) =
      a (Fin.last (m + 1)) - l.count (Fin.last m) := by
  induction l generalizing a with
  | nil => simp [stepEndpoint]
  | cons i l ih =>
      rw [stepEndpoint, ih, step_apply]
      have ht : (Fin.last (m + 1)) ≠ i.castSucc := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      by_cases hi : i = Fin.last m
      · subst i
        simp [ht]
        ring
      · have hs : (Fin.last (m + 1)) ≠ i.succ := by
          intro h
          apply hi
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp at hv ⊢
          omega
        simp [hi, ht, hs]

/-- A valid full lower permutation path at positive scale necessarily starts
with positive last coordinate.  In positive dimension the path must perform
the unique transfer that decreases it; in dimension zero this follows from
the coordinate sum. -/
theorem last_coordinate_pos_of_permutation_stepSequence_isPoint
    {N n : ℕ} (hN : 0 < N)
    (a : Fin (n + 1) → ℤ) (omega : Equiv.Perm (Fin n))
    (hpoint : ∀ x ∈ stepSequence a (permutationList omega),
      IsPoint (N : ℤ) x) :
    0 < a (Fin.last n) := by
  cases n with
  | zero =>
      have ha := hpoint a (base_mem_stepSequence _ _)
      have hsum := ha.2
      have ha0 : a (0 : Fin 1) = (N : ℤ) := by simpa using hsum
      simpa using (show 0 < a (0 : Fin 1) by omega)
  | succ m =>
      let endpoint := stepEndpoint a (permutationList omega)
      have hendpoint : IsPoint (N : ℤ) endpoint :=
        hpoint endpoint (stepEndpoint_mem_stepSequence _ _)
      have hnonneg := hendpoint.1 (Fin.last (m + 1))
      change 0 ≤ stepEndpoint a (permutationList omega)
        (Fin.last (m + 1)) at hnonneg
      rw [stepEndpoint_apply_last] at hnonneg
      have hmem : Fin.last m ∈ permutationList omega := by
        rw [permutationList, List.mem_ofFn']
        exact omega.surjective (Fin.last m)
      rw [List.count_eq_one_of_mem (nodup_permutationList omega) hmem]
        at hnonneg
      omega

/-- At the first coordinate face, every lower transfer becomes the
corresponding successor-indexed high-dimensional transfer. -/
theorem step_succ_insertZeroCoords_zero {n : ℕ}
    (i : Fin n) (a : Fin (n + 1) → ℤ) :
    step i.succ (insertZeroCoords (0 : Fin (n + 2)) a) =
      insertZeroCoords 0 (step i a) := by
  funext j
  induction j using Fin.cases with
  | zero =>
      have hhi : (0 : Fin (n + 2)) ≠ i.succ.succ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      have hmid : (0 : Fin (n + 2)) ≠ i.castSucc.succ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [step_apply, hhi, hmid]
  | succ j =>
      have hj : j.succ = (0 : Fin (n + 2)).succAbove j := rfl
      rw [hj, step_apply, insertZeroCoords_apply_succAbove,
        insertZeroCoords_apply_succAbove]
      simp [step_apply, Fin.ext_iff]

/-- Transfer sequences on the face `x_0 = 0` are obtained by shifting all
transfer indices by one. -/
theorem stepSequence_map_succ_insertZeroCoords_zero {n : ℕ}
    (a : Fin (n + 1) → ℤ) (l : List (Fin n)) :
    stepSequence (insertZeroCoords (0 : Fin (n + 2)) a) (l.map Fin.succ) =
      (stepSequence a l).map (insertZeroCoords 0) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, stepSequence]
      rw [step_succ_insertZeroCoords_zero, ih]

/-- The high-dimensional permutation list obtained on the face `x_0 = 0`:
all lower transfers are shifted, and the missing transfer `0` is appended. -/
def zeroFaceLiftList {n : ℕ} (omega : Equiv.Perm (Fin n)) :
    List (Fin (n + 1)) :=
  (permutationList omega).map Fin.succ ++ [0]

theorem zeroFaceLiftList_nodup {n : ℕ} (omega : Equiv.Perm (Fin n)) :
    (zeroFaceLiftList omega).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(nodup_permutationList omega).map (Fin.succ_injective n),
    by simp, ?_⟩
  intro i hi hzero hzeroMem
  simp only [List.mem_singleton] at hzeroMem
  subst hzero
  intro hi0
  subst i
  simp at hi

@[simp]
theorem zeroFaceLiftList_length {n : ℕ} (omega : Equiv.Perm (Fin n)) :
    (zeroFaceLiftList omega).length = n + 1 := by
  simp [zeroFaceLiftList]

theorem exists_zeroFaceLiftPermutation {n : ℕ}
    (omega : Equiv.Perm (Fin n)) :
    ∃ Omega : Equiv.Perm (Fin (n + 1)),
      permutationList Omega = zeroFaceLiftList omega :=
  exists_permutationList_eq_of_nodup_length
    (zeroFaceLiftList omega) (zeroFaceLiftList_nodup omega)
      (zeroFaceLiftList_length omega)

/-- The lifted sequence contains precisely the embedded lower sequence and
one final off-face vertex. -/
theorem stepSequence_zeroFaceLiftList {n : ℕ}
    (a : Fin (n + 1) → ℤ) (l : List (Fin n)) :
    stepSequence (insertZeroCoords (0 : Fin (n + 2)) a)
        (l.map Fin.succ ++ [0]) =
      (stepSequence a l).map (insertZeroCoords 0) ++
        [step 0 (insertZeroCoords 0 (stepEndpoint a l))] := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, List.cons_append, stepSequence,
        stepEndpoint, List.map_cons]
      rw [step_succ_insertZeroCoords_zero, ih]

/-- Coordinate zero of an endpoint records exactly how often transfer zero
was performed. -/
theorem stepEndpoint_apply_zero {n : ℕ} [NeZero n]
    (a : Fin (n + 1) → ℤ) (l : List (Fin n)) :
    stepEndpoint a l 0 = a 0 + (l.count 0 : ℕ) := by
  induction l generalizing a with
  | nil => simp [stepEndpoint]
  | cons i l ih =>
      rw [stepEndpoint, ih, step_apply]
      have hsucc : (0 : Fin (n + 1)) ≠ i.succ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      by_cases hi : i = 0
      · subst i
        simp
        ring
      · have hcast : (0 : Fin (n + 1)) ≠ i.castSucc := by
          intro h
          apply hi
          apply Fin.ext
          simpa using congrArg Fin.val h.symm
        simp [hi, hcast, hsucc]

/-- In positive lower dimension, every permutation sequence has increased
coordinate zero once at its endpoint. -/
theorem stepEndpoint_permutationList_apply_zero {n : ℕ} (hn : 0 < n)
    (a : Fin (n + 1) → ℤ) (omega : Equiv.Perm (Fin n)) :
    stepEndpoint a (permutationList omega) 0 = a 0 + 1 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [stepEndpoint_apply_zero]
  have hzmem : (0 : Fin n) ∈ permutationList omega := by
    simpa [permutationList] using omega.surjective (0 : Fin n)
  rw [List.count_eq_one_of_mem (nodup_permutationList omega) hzmem]
  norm_num

/-- Exact finite-set form of the lifted sequence decomposition. -/
theorem stepSimplex_zeroFaceLiftList {n : ℕ}
    (a : Fin (n + 1) → ℤ) (omega : Equiv.Perm (Fin n)) :
    stepSimplex (insertZeroCoords (0 : Fin (n + 2)) a)
        (zeroFaceLiftList omega) =
      (stepSimplex a (permutationList omega)).image
          (insertZeroCoords 0) ∪
        {step 0 (insertZeroCoords 0
          (stepEndpoint a (permutationList omega)))} := by
  rw [stepSimplex, zeroFaceLiftList,
    stepSequence_zeroFaceLiftList]
  ext x
  simp [stepSimplex]

/-- Insert a zero coordinate at `k`. -/
def insertZeroPoint {N n : ℕ} (k : Fin (n + 2))
    (a : Point N n) : Point N (n + 1) := by
  refine ⟨fun i ↦ Fin.insertNth
    (α := fun _ ↦ Fin (N + 1)) k 0 (fun j ↦ a.1 j) i, ?_⟩
  change ∑ i, (Fin.insertNth (α := fun _ ↦ Fin (N + 1))
    k 0 (fun j ↦ a.1 j) i).val = N
  rw [Fin.sum_univ_succAbove (fun i ↦
    (Fin.insertNth (α := fun _ ↦ Fin (N + 1))
      k 0 (fun j ↦ a.1 j) i).val) k]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, a.2]

@[simp]
theorem insertZeroPoint_apply_self {N n : ℕ} (k : Fin (n + 2))
    (a : Point N n) : (insertZeroPoint k a).1 k = 0 := by
  apply Fin.ext
  simp [insertZeroPoint, Fin.insertNth_apply_same]

@[simp]
theorem insertZeroPoint_apply_succAbove {N n : ℕ}
    (k : Fin (n + 2)) (a : Point N n) (j : Fin (n + 1)) :
    (insertZeroPoint k a).1 (k.succAbove j) = a.1 j := by
  apply Fin.ext
  simp [insertZeroPoint, Fin.insertNth_apply_succAbove]

/-- Delete the known-zero coordinate at `k`. -/
def eraseZeroPoint {N n : ℕ} (k : Fin (n + 2))
    (b : Point N (n + 1)) (hk : (b.1 k).val = 0) : Point N n := by
  refine ⟨fun j ↦ b.1 (k.succAbove j), ?_⟩
  have hsum := b.2
  rw [Fin.sum_univ_succAbove (fun i ↦ (b.1 i).val) k] at hsum
  simpa [hk] using hsum

@[simp]
theorem eraseZeroPoint_apply {N n : ℕ} (k : Fin (n + 2))
    (b : Point N (n + 1)) (hk : (b.1 k).val = 0)
    (j : Fin (n + 1)) :
    (eraseZeroPoint k b hk).1 j = b.1 (k.succAbove j) := rfl

theorem eraseZeroPoint_insertZeroPoint {N n : ℕ} (k : Fin (n + 2))
    (a : Point N n) :
    eraseZeroPoint k (insertZeroPoint k a)
      (by simp) = a := by
  apply Subtype.ext
  funext j
  exact insertZeroPoint_apply_succAbove k a j

theorem insertZeroPoint_eraseZeroPoint {N n : ℕ} (k : Fin (n + 2))
    (b : Point N (n + 1)) (hk : (b.1 k).val = 0) :
    insertZeroPoint k (eraseZeroPoint k b hk) = b := by
  apply Subtype.ext
  funext i
  by_cases hi : i = k
  · subst i
    apply Fin.ext
    simp [hk]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
    rw [← hj]
    exact insertZeroPoint_apply_succAbove k (eraseZeroPoint k b hk) j

/-- Points on the `k`-th coordinate face. -/
abbrev ZeroFacePoint {N n : ℕ} (k : Fin (n + 2)) :=
  {b : Point N (n + 1) // (b.1 k).val = 0}

/-- The precise dimension-lowering equivalence used in the induction of
Theorem 4.8. -/
def zeroFaceEquiv {N n : ℕ} (k : Fin (n + 2)) :
    Point N n ≃ ZeroFacePoint (N := N) k where
  toFun a := ⟨insertZeroPoint k a, by simp⟩
  invFun b := eraseZeroPoint k b.1 b.2
  left_inv := eraseZeroPoint_insertZeroPoint k
  right_inv := by
    intro b
    apply Subtype.ext
    exact insertZeroPoint_eraseZeroPoint k b.1 b.2

noncomputable instance zeroFacePointNonempty (N n : ℕ)
    (k : Fin (n + 2)) : Nonempty (ZeroFacePoint (N := N) k) :=
  ⟨zeroFaceEquiv k (Classical.choice (pointNonempty N n))⟩

@[simp]
theorem zeroFaceEquiv_apply_val {N n : ℕ} (k : Fin (n + 2))
    (a : Point N n) :
    (zeroFaceEquiv k a).1 = insertZeroPoint k a := rfl

/-- On the first coordinate face, the inverse face equivalence agrees in
coordinates with `collapseZeroCoords`.  The zero-coordinate proof carried by
the subtype is essential: away from the face, plain deletion would not
preserve the coordinate sum. -/
theorem pointCoords_zeroFaceEquiv_symm_zero {N n : ℕ}
    (b : ZeroFacePoint (N := N) (0 : Fin (n + 2))) :
    pointCoords ((zeroFaceEquiv (0 : Fin (n + 2))).symm b) =
      collapseZeroCoords (pointCoords b.1) := by
  funext j
  rw [show (zeroFaceEquiv (0 : Fin (n + 2))).symm b =
      eraseZeroPoint 0 b.1 b.2 by rfl]
  simp only [pointCoords, collapseZeroCoords]
  rw [eraseZeroPoint_apply]
  simp [b.2]

/-- On a positive coordinate face, the inverse face equivalence agrees with
the mass-preserving contraction which merges the deleted coordinate into its
predecessor. -/
theorem pointCoords_zeroFaceEquiv_symm_positive {N n : ℕ}
    (k : Fin (n + 2)) (hk : k ≠ 0)
    (b : ZeroFacePoint (N := N) k) :
    pointCoords ((zeroFaceEquiv k).symm b) =
      collapsePositiveCoords k hk (pointCoords b.1) := by
  rw [show (zeroFaceEquiv k).symm b =
      eraseZeroPoint k b.1 b.2 by rfl]
  rw [collapsePositiveCoords_eq_erase_of_zero k hk]
  · funext j
    simp only [pointCoords, eraseCoords]
    rw [eraseZeroPoint_apply]
  · change (((b.1.1 k).val : ℕ) : ℤ) = 0
    omega

@[simp]
theorem pointCoords_insertZeroPoint_self {N n : ℕ}
    (k : Fin (n + 2)) (a : Point N n) :
    pointCoords (insertZeroPoint k a) k = 0 := by
  simp [pointCoords]

@[simp]
theorem pointCoords_insertZeroPoint_succAbove {N n : ℕ}
    (k : Fin (n + 2)) (a : Point N n) (j : Fin (n + 1)) :
    pointCoords (insertZeroPoint k a) (k.succAbove j) =
      pointCoords a j := by
  simp [pointCoords]

theorem pointCoords_insertZeroPoint {N n : ℕ}
    (k : Fin (n + 2)) (a : Point N n) :
    pointCoords (insertZeroPoint k a) =
      insertZeroCoords k (pointCoords a) := by
  funext i
  by_cases hi : i = k
  · subst i
    simp
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    simp

/-- The lower cyclic order and the corresponding nonzero ambient cyclic order
agree exactly under insertion of coordinate zero. -/
theorem pointOrders_insertZeroPoint_zero_le_iff {N n : ℕ}
    (i : Fin (n + 1)) (a b : Point N n) :
    ((pointOrders N (n + 1)) i.succ).le
        (insertZeroPoint (0 : Fin (n + 2)) a) (insertZeroPoint 0 b) ↔
      ((pointOrders N n) i).le a b := by
  change cyclicKey i.succ (pointCoords (insertZeroPoint 0 a)) ≤
      cyclicKey i.succ (pointCoords (insertZeroPoint 0 b)) ↔
    cyclicKey i (pointCoords a) ≤ cyclicKey i (pointCoords b)
  rw [pointCoords_insertZeroPoint, pointCoords_insertZeroPoint]
  constructor
  · intro hhigh
    apply le_of_not_gt
    intro hlow
    exact (not_lt_of_ge hhigh)
      ((cyclicKey_insertZeroCoords_zero_lt_iff i
        (pointCoords b) (pointCoords a)).2 hlow)
  · intro hlow
    apply le_of_not_gt
    intro hhigh
    exact (not_lt_of_ge hlow)
      ((cyclicKey_insertZeroCoords_zero_lt_iff i
        (pointCoords b) (pointCoords a)).1 hhigh)

/-- The lower cyclic order and the corresponding ambient order agree under
insertion of a zero at an arbitrary coordinate. -/
theorem pointOrders_insertZeroPoint_le_iff {N n : ℕ}
    (k : Fin (n + 2)) (i : Fin (n + 1)) (a b : Point N n) :
    ((pointOrders N (n + 1)) (k.succAbove i)).le
        (insertZeroPoint k a) (insertZeroPoint k b) ↔
      ((pointOrders N n) i).le a b := by
  change cyclicKey (k.succAbove i)
        (pointCoords (insertZeroPoint k a)) ≤
      cyclicKey (k.succAbove i)
        (pointCoords (insertZeroPoint k b)) ↔
    cyclicKey i (pointCoords a) ≤ cyclicKey i (pointCoords b)
  rw [pointCoords_insertZeroPoint, pointCoords_insertZeroPoint]
  constructor
  · intro hhigh
    apply le_of_not_gt
    intro hlow
    exact (not_lt_of_ge hhigh)
      ((cyclicKey_insertZeroCoords_lt_iff k i
        (pointCoords b) (pointCoords a)).2 hlow)
  · intro hlow
    apply le_of_not_gt
    intro hhigh
    exact (not_lt_of_ge hlow)
      ((cyclicKey_insertZeroCoords_lt_iff k i
        (pointCoords b) (pointCoords a)).1 hhigh)

/-- Project an arbitrary ambient point to the first coordinate face by moving
all of its zero-coordinate mass to the cyclic predecessor. -/
noncomputable def projectZeroPoint {N n : ℕ}
    (b : Point N (n + 1)) : Point N (n + 1) :=
  pointOfIsPoint
    (moveZeroMass (pointCoords b) (pointCoords b 0).toNat)
    (moveZeroMass_isPoint (pointCoords b) (pointCoords_isPoint b) _ (by
      rw [Int.toNat_of_nonneg ((pointCoords_isPoint b).1 0)]))

@[simp]
theorem pointCoords_projectZeroPoint {N n : ℕ}
    (b : Point N (n + 1)) :
    pointCoords (projectZeroPoint b) =
      moveZeroMass (pointCoords b) (pointCoords b 0).toNat := by
  apply pointCoords_pointOfIsPoint

@[simp]
theorem projectZeroPoint_coord_zero {N n : ℕ}
    (b : Point N (n + 1)) :
    pointCoords (projectZeroPoint b) 0 = 0 := by
  rw [pointCoords_projectZeroPoint, moveZeroMass_apply]
  have hp : (0 : Fin (n + 2)) ≠ (finRotate (n + 2)).symm 0 :=
    (finRotate_symm_zero_ne_zero n).symm
  rw [if_neg hp, if_pos rfl]
  rw [Int.toNat_of_nonneg ((pointCoords_isPoint b).1 0)]
  ring

/-- The projected point, bundled with its certified face equation. -/
noncomputable def projectZeroFacePoint {N n : ℕ}
    (b : Point N (n + 1)) :
    ZeroFacePoint (N := N) (0 : Fin (n + 2)) :=
  ⟨projectZeroPoint b, by
    have hz := projectZeroPoint_coord_zero b
    change (((projectZeroPoint b).1 0).val : ℤ) = 0 at hz
    omega⟩

/-- Every nonzero ambient cyclic order weakly increases under projection to
the first coordinate face. -/
theorem pointOrders_le_projectZeroPoint {N n : ℕ}
    (b : Point N (n + 1)) (j : Fin (n + 2)) (hj : j ≠ 0) :
    ((pointOrders N (n + 1)) j).le b (projectZeroPoint b) := by
  change cyclicKey j (pointCoords b) ≤
    cyclicKey j (pointCoords (projectZeroPoint b))
  rw [pointCoords_projectZeroPoint]
  exact cyclicKey_le_moveZeroMass j hj (pointCoords b)
    (pointCoords b 0).toNat

/-- Pull the nonzero ambient cyclic orders back to the certified first
coordinate face. -/
noncomputable def zeroFacePointOrders (N n : ℕ) :
    IndexedLinearOrders (Fin (n + 1))
      (ZeroFacePoint (N := N) (0 : Fin (n + 2))) where
  order i := @LinearOrder.lift'
    (ZeroFacePoint (N := N) (0 : Fin (n + 2)))
    (Point N (n + 1)) ((pointOrders N (n + 1)) i.succ)
    Subtype.val Subtype.val_injective

theorem zeroFacePointOrders_zeroFaceEquiv_le_iff {N n : ℕ}
    (i : Fin (n + 1)) (a b : Point N n) :
    ((zeroFacePointOrders N n) i).le
        (zeroFaceEquiv (0 : Fin (n + 2)) a)
        (zeroFaceEquiv 0 b) ↔
      ((pointOrders N n) i).le a b := by
  change ((pointOrders N (n + 1)) i.succ).le
      (insertZeroPoint 0 a) (insertZeroPoint 0 b) ↔ _
  exact pointOrders_insertZeroPoint_zero_le_iff i a b

/-- Dominance on the certified first face is equivalent to ambient dominance
with respect to every nonzero coordinate order.  The reverse implication uses
`projectZeroFacePoint`; it does not silently restrict the universal ambient
quantifier to the face. -/
theorem isDominant_zeroFace_iff_ambient {N n : ℕ}
    (sigma : Finset (ZeroFacePoint (N := N) (0 : Fin (n + 2)))) :
    (pointOrders N (n + 1)).IsDominant (sigma.image Subtype.val)
        ((Finset.univ : Finset (Fin (n + 2))).erase 0) ↔
      (zeroFacePointOrders N n).IsDominant sigma Finset.univ := by
  constructor
  · intro hambient
    refine ⟨Finset.univ_nonempty, ?_⟩
    intro y
    obtain ⟨q, hqC, hqy⟩ := hambient.2 y.1
    have hq0 : q ≠ 0 := (Finset.mem_erase.mp hqC).1
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hq0
    refine ⟨i, Finset.mem_univ _, ?_⟩
    intro x hx
    have hxy := hqy x.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    change ((pointOrders N (n + 1)) i.succ).le y.1 x.1
    rw [show i.succ = q by simpa using hi]
    exact hxy
  · intro hface
    have hCne :
        ((Finset.univ : Finset (Fin (n + 2))).erase 0).Nonempty := by
      refine ⟨(0 : Fin (n + 1)).succ, ?_⟩
      simp
    refine ⟨hCne, ?_⟩
    intro y
    obtain ⟨i, _, hiy⟩ := hface.2 (projectZeroFacePoint y)
    refine ⟨i.succ, by simp, ?_⟩
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hfirst := pointOrders_le_projectZeroPoint y i.succ
      (Fin.succ_ne_zero i)
    have hproject := hiy x hx
    let : LinearOrder (Point N (n + 1)) :=
      (pointOrders N (n + 1)) i.succ
    exact le_trans hfirst hproject

/-- Consequently, full cells on the first face are exactly ambient
`I \ {0}`-cells after forgetting the face proofs. -/
theorem isCell_zeroFace_iff_ambient {N n : ℕ}
    (sigma : Finset (ZeroFacePoint (N := N) (0 : Fin (n + 2)))) :
    (pointOrders N (n + 1)).IsCell (sigma.image Subtype.val)
        ((Finset.univ : Finset (Fin (n + 2))).erase 0) ↔
      (zeroFacePointOrders N n).IsCell sigma Finset.univ := by
  rw [IndexedLinearOrders.IsCell, IndexedLinearOrders.IsCell,
    isDominant_zeroFace_iff_ambient]
  rw [Finset.card_image_of_injective _ Subtype.val_injective]
  simp

/-- Project an arbitrary ambient point to the face `x_k = 0` by moving all
mass in coordinate `k` to its cyclic predecessor. -/
noncomputable def projectCoordinatePoint {N n : ℕ}
    (k : Fin (n + 2)) (b : Point N (n + 1)) : Point N (n + 1) :=
  pointOfIsPoint
    (moveCoordinateMass k (pointCoords b) (pointCoords b k).toNat)
    (moveCoordinateMass_isPoint k (pointCoords b)
      (pointCoords_isPoint b) _ (by
        rw [Int.toNat_of_nonneg ((pointCoords_isPoint b).1 k)]))

@[simp]
theorem pointCoords_projectCoordinatePoint {N n : ℕ}
    (k : Fin (n + 2)) (b : Point N (n + 1)) :
    pointCoords (projectCoordinatePoint k b) =
      moveCoordinateMass k (pointCoords b) (pointCoords b k).toNat := by
  apply pointCoords_pointOfIsPoint

@[simp]
theorem projectCoordinatePoint_coord_self {N n : ℕ}
    (k : Fin (n + 2)) (b : Point N (n + 1)) :
    pointCoords (projectCoordinatePoint k b) k = 0 := by
  rw [pointCoords_projectCoordinatePoint, moveCoordinateMass_apply]
  have hp : k ≠ (finRotate (n + 2)).symm k :=
    (finRotate_symm_ne_self_face k).symm
  rw [if_neg hp, if_pos rfl]
  rw [Int.toNat_of_nonneg ((pointCoords_isPoint b).1 k)]
  ring

/-- The arbitrary-coordinate projection bundled with its face equation. -/
noncomputable def projectCoordinateFacePoint {N n : ℕ}
    (k : Fin (n + 2)) (b : Point N (n + 1)) :
    ZeroFacePoint (N := N) k :=
  ⟨projectCoordinatePoint k b, by
    have hz := projectCoordinatePoint_coord_self k b
    change (((projectCoordinatePoint k b).1 k).val : ℤ) = 0 at hz
    omega⟩

/-- Every ambient cyclic order other than `k` weakly increases under
projection to the coordinate face `x_k = 0`. -/
theorem pointOrders_le_projectCoordinatePoint {N n : ℕ}
    (k : Fin (n + 2)) (b : Point N (n + 1))
    (j : Fin (n + 2)) (hj : j ≠ k) :
    ((pointOrders N (n + 1)) j).le b (projectCoordinatePoint k b) := by
  change cyclicKey j (pointCoords b) ≤
    cyclicKey j (pointCoords (projectCoordinatePoint k b))
  rw [pointCoords_projectCoordinatePoint]
  exact cyclicKey_le_moveCoordinateMass k j hj (pointCoords b)
    (pointCoords b k).toNat

/-- Pull all ambient cyclic orders indexed away from `k` back to the
certified coordinate face. -/
noncomputable def facePointOrders (N n : ℕ) (k : Fin (n + 2)) :
    IndexedLinearOrders (Fin (n + 1)) (ZeroFacePoint (N := N) k) where
  order i := @LinearOrder.lift'
    (ZeroFacePoint (N := N) k) (Point N (n + 1))
    ((pointOrders N (n + 1)) (k.succAbove i))
    Subtype.val Subtype.val_injective

/-- `zeroFaceEquiv k` is an order isomorphism simultaneously for every
lower index and its ambient image away from `k`. -/
theorem facePointOrders_zeroFaceEquiv_le_iff {N n : ℕ}
    (k : Fin (n + 2)) (i : Fin (n + 1)) (a b : Point N n) :
    ((facePointOrders N n k) i).le
        (zeroFaceEquiv k a) (zeroFaceEquiv k b) ↔
      ((pointOrders N n) i).le a b := by
  change ((pointOrders N (n + 1)) (k.succAbove i)).le
      (insertZeroPoint k a) (insertZeroPoint k b) ↔ _
  exact pointOrders_insertZeroPoint_le_iff k i a b

/-- Dominance on the certified coordinate face is exactly ambient dominance
with respect to all orders other than `k`.  The face-to-ambient direction
retains the universal ambient comparison point by using
`projectCoordinateFacePoint`. -/
theorem isDominant_coordinateFace_iff_ambient {N n : ℕ}
    (k : Fin (n + 2)) (sigma : Finset (ZeroFacePoint (N := N) k)) :
    (pointOrders N (n + 1)).IsDominant (sigma.image Subtype.val)
        ((Finset.univ : Finset (Fin (n + 2))).erase k) ↔
      (facePointOrders N n k).IsDominant sigma Finset.univ := by
  constructor
  · intro hambient
    refine ⟨Finset.univ_nonempty, ?_⟩
    intro y
    obtain ⟨q, hqC, hqy⟩ := hambient.2 y.1
    have hqk : q ≠ k := (Finset.mem_erase.mp hqC).1
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hqk
    refine ⟨i, Finset.mem_univ _, ?_⟩
    intro x hx
    have hxy := hqy x.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    change ((pointOrders N (n + 1)) (k.succAbove i)).le y.1 x.1
    rw [hi]
    exact hxy
  · intro hface
    have hCne :
        ((Finset.univ : Finset (Fin (n + 2))).erase k).Nonempty := by
      refine ⟨k.succAbove (0 : Fin (n + 1)), ?_⟩
      simp [Fin.succAbove_ne]
    refine ⟨hCne, ?_⟩
    intro y
    obtain ⟨i, _, hiy⟩ := hface.2 (projectCoordinateFacePoint k y)
    refine ⟨k.succAbove i, by simp [Fin.succAbove_ne], ?_⟩
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hfirst := pointOrders_le_projectCoordinatePoint k y
      (k.succAbove i) (Fin.succAbove_ne k i)
    have hproject := hiy x hx
    let : LinearOrder (Point N (n + 1)) :=
      (pointOrders N (n + 1)) (k.succAbove i)
    exact le_trans hfirst hproject

/-- Full cells on an arbitrary coordinate face are exactly ambient
`I \ {k}`-cells after forgetting the face certificates. -/
theorem isCell_coordinateFace_iff_ambient {N n : ℕ}
    (k : Fin (n + 2)) (sigma : Finset (ZeroFacePoint (N := N) k)) :
    (pointOrders N (n + 1)).IsCell (sigma.image Subtype.val)
        ((Finset.univ : Finset (Fin (n + 2))).erase k) ↔
      (facePointOrders N n k).IsCell sigma Finset.univ := by
  rw [IndexedLinearOrders.IsCell, IndexedLinearOrders.IsCell,
    isDominant_coordinateFace_iff_ambient]
  rw [Finset.card_image_of_injective _ Subtype.val_injective]
  simp

/-- Dominance on a coordinate face for an arbitrary lower index set `A` is
exactly ambient dominance for the image of `A` under `k.succAbove`.  The
published codimension-one statement is the special case `A = univ`; the
projection argument does not require all remaining indices. -/
theorem isDominant_coordinateFace_image_iff_ambient {N n : ℕ}
    (k : Fin (n + 2)) (A : Finset (Fin (n + 1)))
    (sigma : Finset (ZeroFacePoint (N := N) k)) :
    (pointOrders N (n + 1)).IsDominant (sigma.image Subtype.val)
        (A.image fun i ↦ k.succAbove i) ↔
      (facePointOrders N n k).IsDominant sigma A := by
  constructor
  · intro hambient
    have hA : A.Nonempty := by
      exact (Finset.image_nonempty.mp hambient.1)
    refine ⟨hA, ?_⟩
    intro y
    obtain ⟨q, hqA, hqy⟩ := hambient.2 y.1
    obtain ⟨i, hiA, hiq⟩ := Finset.mem_image.mp hqA
    refine ⟨i, hiA, ?_⟩
    intro x hx
    have hxy := hqy x.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    change ((pointOrders N (n + 1)) (k.succAbove i)).le y.1 x.1
    rw [hiq]
    exact hxy
  · intro hface
    refine ⟨hface.1.image (fun i ↦ k.succAbove i), ?_⟩
    intro y
    obtain ⟨i, hiA, hiy⟩ := hface.2 (projectCoordinateFacePoint k y)
    refine ⟨k.succAbove i, Finset.mem_image.mpr ⟨i, hiA, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hfirst := pointOrders_le_projectCoordinatePoint k y
      (k.succAbove i) (Fin.succAbove_ne k i)
    have hproject := hiy x hx
    let : LinearOrder (Point N (n + 1)) :=
      (pointOrders N (n + 1)) (k.succAbove i)
    exact le_trans hfirst hproject

/-- Cell membership on a coordinate face for an arbitrary lower index set is
preserved and reflected by the two injective embeddings of indices and
vertices. -/
theorem isCell_coordinateFace_image_iff_ambient {N n : ℕ}
    (k : Fin (n + 2)) (A : Finset (Fin (n + 1)))
    (sigma : Finset (ZeroFacePoint (N := N) k)) :
    (pointOrders N (n + 1)).IsCell (sigma.image Subtype.val)
        (A.image fun i ↦ k.succAbove i) ↔
      (facePointOrders N n k).IsCell sigma A := by
  rw [IndexedLinearOrders.IsCell, IndexedLinearOrders.IsCell,
    isDominant_coordinateFace_image_iff_ambient]
  rw [Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_image_of_injective _ Fin.succAbove_right_injective]

/-- The complete vertex set of the `k`-th coordinate face. -/
noncomputable def zeroFaceVertices (N n : ℕ) (k : Fin (n + 2)) :
    Finset (Point N (n + 1)) :=
  Finset.univ.filter fun b ↦ (b.1 k).val = 0

theorem mem_zeroFaceVertices_iff {N n : ℕ} (k : Fin (n + 2))
    (b : Point N (n + 1)) :
    b ∈ zeroFaceVertices N n k ↔ (b.1 k).val = 0 := by
  simp [zeroFaceVertices]

/-- Inserting the zero coordinate maps the entire lower-dimensional point
set onto, not merely into, the corresponding coordinate face. -/
theorem image_univ_insertZeroPoint {N n : ℕ} (k : Fin (n + 2)) :
    (Finset.univ : Finset (Point N n)).image (insertZeroPoint k) =
      zeroFaceVertices N n k := by
  ext b
  constructor
  · intro hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    exact (mem_zeroFaceVertices_iff k _).2 (by simp)
  · intro hb
    have hk := (mem_zeroFaceVertices_iff k b).1 hb
    refine Finset.mem_image.mpr
      ⟨eraseZeroPoint k b hk, Finset.mem_univ _, ?_⟩
    exact insertZeroPoint_eraseZeroPoint k b hk

theorem insertZeroPoint_injective {N n : ℕ} (k : Fin (n + 2)) :
    Function.Injective (insertZeroPoint (N := N) k) := by
  intro a b h
  apply Subtype.ext
  funext j
  have hj := congrArg (fun x : Point N (n + 1) ↦
    x.1 (k.succAbove j)) h
  simpa using hj

/-- The actual subcomplex of the high-dimensional Freudenthal complex lying
on the coordinate face `x_k = 0`, with vertices bundled by that equation. -/
noncomputable def freudenthalCoordinateFaceComplex (N n : ℕ)
    (k : Fin (n + 2)) :
    FiniteSimplicialComplex (ZeroFacePoint (N := N) k) :=
  (freudenthalComplex N (n + 1)).inducedOn
    (fun b ↦ (b.1 k).val = 0)

theorem mem_freudenthalCoordinateFaceComplex_iff {N n : ℕ}
    (k : Fin (n + 2))
    (sigma : Finset (ZeroFacePoint (N := N) k)) :
    sigma ∈ freudenthalCoordinateFaceComplex N n k ↔
      sigma.image Subtype.val ∈ freudenthalComplex N (n + 1) := by
  exact FiniteSimplicialComplex.mem_inducedOn_iff _ _ _

/-- The lower-dimensional Freudenthal complex, transported to the coordinate
face by the explicit point equivalence.  Equality with
`freudenthalCoordinateFaceComplex` is the target-side face-identification
obligation in the induction for Theorem 4.8. -/
noncomputable def lowerFreudenthalRelabeledToFace (N n : ℕ)
    (k : Fin (n + 2)) :
    FiniteSimplicialComplex (ZeroFacePoint (N := N) k) :=
  (freudenthalComplex N n).relabel (zeroFaceEquiv k)

/-- The lower full-index Scarf complex transported to a coordinate face. -/
noncomputable def lowerScarfRelabeledToFace (N n : ℕ)
    (k : Fin (n + 2)) :
    FiniteSimplicialComplex (ZeroFacePoint (N := N) k) :=
  ((pointOrders N n).associatedComplex Finset.univ).relabel
    (zeroFaceEquiv k)

/-- Transport of the lower full-index Scarf complex to any coordinate face
is exactly the associated complex of the pulled-back ambient face orders. -/
theorem lowerScarfRelabeledToFace_eq_facePointOrders {N n : ℕ}
    (k : Fin (n + 2)) :
    lowerScarfRelabeledToFace N n k =
      (facePointOrders N n k).associatedComplex Finset.univ := by
  have h := IndexedLinearOrders.associatedComplex_relabel
    (pointOrders N n) (facePointOrders N n k)
    (Equiv.refl (Fin (n + 1))) (zeroFaceEquiv k)
    (fun i x y ↦
      (facePointOrders_zeroFaceEquiv_le_iff k i x y).symm)
    (Finset.univ : Finset (Fin (n + 1)))
  simpa [lowerScarfRelabeledToFace] using h

/-- For the first face, transport by `zeroFaceEquiv` gives exactly the
associated complex of the pulled-back face orders. -/
theorem lowerScarfRelabeledToFace_eq_zeroFaceOrders {N n : ℕ} :
    lowerScarfRelabeledToFace N n (0 : Fin (n + 2)) =
      (zeroFacePointOrders N n).associatedComplex Finset.univ := by
  have h := IndexedLinearOrders.associatedComplex_relabel
    (pointOrders N n) (zeroFacePointOrders N n)
    (Equiv.refl (Fin (n + 1))) (zeroFaceEquiv (0 : Fin (n + 2)))
    (fun i x y ↦
      (zeroFacePointOrders_zeroFaceEquiv_le_iff i x y).symm)
    (Finset.univ : Finset (Fin (n + 1)))
  simpa [lowerScarfRelabeledToFace] using h

/-- Forward facet extension at the coordinate face `x_0 = 0`.  The strict
scale hypothesis is necessary in dimension one: at `N = 0` the ambient
positive-dimensional Freudenthal facet set is empty. -/
theorem image_insertZeroPoint_zero_mem_freudenthalComplex
    {N n : ℕ} (hN : 0 < N) {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho) :
    rho.image (insertZeroPoint (0 : Fin (n + 2))) ∈
      freudenthalComplex N (n + 1) := by
  obtain ⟨a, omega, hrhoCoords⟩ := hrho
  let endpoint : Fin (n + 1) → ℤ :=
    stepEndpoint (pointCoords a) (permutationList omega)
  let highSet : Finset (Fin (n + 2) → ℤ) :=
    stepSimplex
      (insertZeroCoords (0 : Fin (n + 2)) (pointCoords a))
      (zeroFaceLiftList omega)
  have hlowPoint : ∀ x ∈
      stepSimplex (pointCoords a) (permutationList omega),
      IsPoint (N : ℤ) x := by
    intro x hx
    have hxImage : x ∈ rho.image pointCoords := by
      rw [hrhoCoords]
      exact hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hxImage
    exact pointCoords_isPoint b
  have hendpointPoint : IsPoint (N : ℤ) endpoint := by
    apply hlowPoint
    exact stepEndpoint_mem_stepSimplex _ _
  have hendpointPos : 0 < endpoint 0 := by
    by_cases hn : n = 0
    · subst n
      have hsum := hendpointPoint.2
      have heq : endpoint 0 = (N : ℤ) := by simpa using hsum
      omega
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      change 0 < stepEndpoint (pointCoords a)
        (permutationList omega) 0
      rw [stepEndpoint_permutationList_apply_zero hnpos]
      have ha0 := (pointCoords_isPoint a).1 (0 : Fin (n + 1))
      omega
  have hhighPoint : ∀ x ∈ highSet, IsPoint (N : ℤ) x := by
    intro x hx
    change x ∈ stepSimplex
      (insertZeroCoords (0 : Fin (n + 2)) (pointCoords a))
      (zeroFaceLiftList omega) at hx
    rw [stepSimplex_zeroFaceLiftList] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact insertZeroCoords_isPoint 0 (hlowPoint y hy)
    · have hxEq : x = step 0 (insertZeroCoords 0 endpoint) := by
        simpa using hx
      subst x
      apply step_isPoint 0 (insertZeroCoords 0 endpoint)
        (insertZeroCoords_isPoint 0 hendpointPoint)
      rw [show (0 : Fin (n + 1)).succ =
        (0 : Fin (n + 2)).succAbove (0 : Fin (n + 1)) by rfl,
        insertZeroCoords_apply_succAbove]
      exact hendpointPos
  let R : Finset (Point N (n + 1)) :=
    realizeCoordinateSet N (n + 1) highSet
  have hRCoords : R.image pointCoords = highSet :=
    image_pointCoords_realizeCoordinateSet highSet hhighPoint
  obtain ⟨Omega, hOmega⟩ := exists_zeroFaceLiftPermutation omega
  have hRTop : IsFreudenthalTopSimplex R := by
    refine ⟨insertZeroPoint 0 a, Omega, ?_⟩
    rw [hRCoords]
    change highSet = stepSimplex
      (pointCoords (insertZeroPoint 0 a)) (permutationList Omega)
    rw [pointCoords_insertZeroPoint, hOmega]
  apply (mem_freudenthalComplex_iff _).2
  right
  refine ⟨R, hRTop, ?_⟩
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change pointCoords (insertZeroPoint 0 c) ∈ highSet
  change pointCoords (insertZeroPoint 0 c) ∈ stepSimplex
      (insertZeroCoords 0 (pointCoords a)) (zeroFaceLiftList omega)
  rw [stepSimplex_zeroFaceLiftList, pointCoords_insertZeroPoint]
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨pointCoords c, ?_, rfl⟩
  rw [← hrhoCoords]
  exact Finset.mem_image.mpr ⟨c, hc, rfl⟩

/-- Proved inclusion in the first coordinate face: every relabelled
lower-dimensional Freudenthal simplex is an actual simplex of the induced
ambient face complex. -/
theorem lowerFreudenthalRelabeledToFace_subset_zero
    {N n : ℕ} (hN : 0 < N)
    {sigma : Finset (ZeroFacePoint (N := N) (0 : Fin (n + 2)))}
    (hsigma : sigma ∈
      lowerFreudenthalRelabeledToFace N n (0 : Fin (n + 2))) :
    sigma ∈ freudenthalCoordinateFaceComplex N n (0 : Fin (n + 2)) := by
  obtain ⟨tau, htau, htauImage⟩ :=
    (FiniteSimplicialComplex.mem_relabel_iff
      (freudenthalComplex N n) (zeroFaceEquiv 0) sigma).1 hsigma
  apply (mem_freudenthalCoordinateFaceComplex_iff 0 sigma).2
  have hsigmaAmbient : sigma.image Subtype.val =
      tau.image (insertZeroPoint 0) := by
    rw [← htauImage]
    ext b
    simp
  rw [hsigmaAmbient]
  have htauFreud := (mem_freudenthalComplex_iff tau).1 htau
  rcases htauFreud with rfl | ⟨rho, hrho, hsub⟩
  · simp
  · apply (freudenthalComplex N (n + 1)).downward_closed
      (image_insertZeroPoint_zero_mem_freudenthalComplex hN hrho)
    exact Finset.image_mono (insertZeroPoint 0) hsub

/-- A genuine lower Freudenthal facet extends across every positive
nonlast coordinate face.  The unique lower transfer crossing the deleted
coordinate is replaced by the two-transfer bridge constructed above. -/
theorem image_insertZeroPoint_interior_mem_freudenthalComplex
    {N n : ℕ} (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho) :
    rho.image (insertZeroPoint d.succ) ∈
      freudenthalComplex N (n + 1) := by
  obtain ⟨a, omega, hrhoCoords⟩ := hrho
  let highList : List (Fin (n + 1)) :=
    interiorFaceLiftList d hd (permutationList omega)
  let highSet : Finset (Fin (n + 2) → ℤ) :=
    stepSimplex (insertZeroCoords d.succ (pointCoords a)) highList
  have hlowPoint : ∀ x ∈
      stepSimplex (pointCoords a) (permutationList omega),
      IsPoint (N : ℤ) x := by
    intro x hx
    have hxImage : x ∈ rho.image pointCoords := by
      rw [hrhoCoords]
      exact hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hxImage
    exact pointCoords_isPoint b
  have hhighPoint : ∀ x ∈ highSet, IsPoint (N : ℤ) x := by
    intro x hx
    apply interiorFaceLiftList_stepSequence_isPoint d hd
      (pointCoords a) (permutationList omega)
    · intro y hy
      apply hlowPoint y
      simpa [stepSimplex] using hy
    · simpa [highSet, highList, stepSimplex] using hx
  let R : Finset (Point N (n + 1)) :=
    realizeCoordinateSet N (n + 1) highSet
  have hRCoords : R.image pointCoords = highSet :=
    image_pointCoords_realizeCoordinateSet highSet hhighPoint
  obtain ⟨Omega, hOmega⟩ :=
    exists_interiorFaceLiftPermutation d hd omega
  have hRTop : IsFreudenthalTopSimplex R := by
    refine ⟨insertZeroPoint d.succ a, Omega, ?_⟩
    rw [hRCoords]
    change highSet = stepSimplex
      (pointCoords (insertZeroPoint d.succ a))
      (permutationList Omega)
    rw [pointCoords_insertZeroPoint, hOmega]
  apply (mem_freudenthalComplex_iff _).2
  right
  refine ⟨R, hRTop, ?_⟩
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change pointCoords (insertZeroPoint d.succ c) ∈ highSet
  rw [pointCoords_insertZeroPoint]
  change insertZeroCoords d.succ (pointCoords c) ∈
    stepSimplex (insertZeroCoords d.succ (pointCoords a))
      (interiorFaceLiftList d hd (permutationList omega))
  have hcCoords : pointCoords c ∈
      stepSimplex (pointCoords a) (permutationList omega) := by
    rw [← hrhoCoords]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hcSeq : pointCoords c ∈
      stepSequence (pointCoords a) (permutationList omega) := by
    simpa [stepSimplex] using hcCoords
  have hhighSeq :=
    mem_stepSequence_interiorFaceLiftList_of_mem d hd
      (pointCoords a) (permutationList omega) hcSeq
  simpa [stepSimplex] using hhighSeq

/-- Forward inclusion for a positive nonlast coordinate face. -/
theorem lowerFreudenthalRelabeledToFace_subset_interior
    {N n : ℕ} (d : Fin (n + 1)) (hd : d ≠ Fin.last n)
    {sigma : Finset (ZeroFacePoint (N := N) d.succ)}
    (hsigma : sigma ∈ lowerFreudenthalRelabeledToFace N n d.succ) :
    sigma ∈ freudenthalCoordinateFaceComplex N n d.succ := by
  obtain ⟨tau, htau, htauImage⟩ :=
    (FiniteSimplicialComplex.mem_relabel_iff
      (freudenthalComplex N n) (zeroFaceEquiv d.succ) sigma).1 hsigma
  apply (mem_freudenthalCoordinateFaceComplex_iff d.succ sigma).2
  have hsigmaAmbient : sigma.image Subtype.val =
      tau.image (insertZeroPoint d.succ) := by
    rw [← htauImage]
    ext b
    simp
  rw [hsigmaAmbient]
  have htauFreud := (mem_freudenthalComplex_iff tau).1 htau
  rcases htauFreud with rfl | ⟨rho, hrho, hsub⟩
  · simp
  · apply (freudenthalComplex N (n + 1)).downward_closed
      (image_insertZeroPoint_interior_mem_freudenthalComplex d hd hrho)
    exact Finset.image_mono (insertZeroPoint d.succ) hsub

/-- A genuine lower facet extends across the last coordinate face at
positive scale.  The ambient facet starts at the unique off-face predecessor
`lastFaceBase` and enters the face in its first transfer. -/
theorem image_insertZeroPoint_last_mem_freudenthalComplex
    {N n : ℕ} (hN : 0 < N) {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho) :
    rho.image (insertZeroPoint (Fin.last (n + 1))) ∈
      freudenthalComplex N (n + 1) := by
  obtain ⟨a, omega, hrhoCoords⟩ := hrho
  have hlowPoint : ∀ x ∈
      stepSimplex (pointCoords a) (permutationList omega),
      IsPoint (N : ℤ) x := by
    intro x hx
    have hxImage : x ∈ rho.image pointCoords := by
      rw [hrhoCoords]
      exact hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hxImage
    exact pointCoords_isPoint b
  have hlowSequence : ∀ x ∈
      stepSequence (pointCoords a) (permutationList omega),
      IsPoint (N : ℤ) x := by
    intro x hx
    apply hlowPoint x
    simpa [stepSimplex] using hx
  have hlastPos : 0 < pointCoords a (Fin.last n) :=
    last_coordinate_pos_of_permutation_stepSequence_isPoint
      hN (pointCoords a) omega hlowSequence
  have hbasePoint : IsPoint (N : ℤ) (lastFaceBase (pointCoords a)) :=
    lastFaceBase_isPoint (pointCoords a) (pointCoords_isPoint a) hlastPos
  let highSet : Finset (Fin (n + 2) → ℤ) :=
    stepSimplex (lastFaceBase (pointCoords a)) (lastFaceLiftList omega)
  have hhighPoint : ∀ x ∈ highSet, IsPoint (N : ℤ) x := by
    intro x hx
    have hxSeq : x ∈ stepSequence (lastFaceBase (pointCoords a))
        (lastFaceLiftList omega) := by
      simpa [highSet, stepSimplex] using hx
    rw [stepSequence_lastFaceLiftList] at hxSeq
    simp only [List.mem_cons, List.mem_map] at hxSeq
    rcases hxSeq with rfl | ⟨y, hy, rfl⟩
    · exact hbasePoint
    · exact insertZeroCoords_isPoint (Fin.last (n + 1))
        (hlowSequence y hy)
  let R : Finset (Point N (n + 1)) :=
    realizeCoordinateSet N (n + 1) highSet
  have hRCoords : R.image pointCoords = highSet :=
    image_pointCoords_realizeCoordinateSet highSet hhighPoint
  obtain ⟨Omega, hOmega⟩ := exists_lastFaceLiftPermutation omega
  have hRTop : IsFreudenthalTopSimplex R := by
    refine ⟨pointOfIsPoint (lastFaceBase (pointCoords a)) hbasePoint,
      Omega, ?_⟩
    rw [hRCoords]
    change highSet = stepSimplex
      (pointCoords (pointOfIsPoint (lastFaceBase (pointCoords a)) hbasePoint))
      (permutationList Omega)
    rw [pointCoords_pointOfIsPoint, hOmega]
  apply (mem_freudenthalComplex_iff _).2
  right
  refine ⟨R, hRTop, ?_⟩
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change pointCoords (insertZeroPoint (Fin.last (n + 1)) c) ∈ highSet
  rw [pointCoords_insertZeroPoint]
  change insertZeroCoords (Fin.last (n + 1)) (pointCoords c) ∈
    stepSimplex (lastFaceBase (pointCoords a)) (lastFaceLiftList omega)
  have hcCoords : pointCoords c ∈
      stepSimplex (pointCoords a) (permutationList omega) := by
    rw [← hrhoCoords]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hcSeq : pointCoords c ∈
      stepSequence (pointCoords a) (permutationList omega) := by
    simpa [stepSimplex] using hcCoords
  rw [stepSimplex, stepSequence_lastFaceLiftList]
  simp only [List.mem_toFinset, List.mem_cons, List.mem_map]
  exact Or.inr ⟨pointCoords c, hcSeq, rfl⟩

/-- Forward inclusion at the last coordinate face. -/
theorem lowerFreudenthalRelabeledToFace_subset_last
    {N n : ℕ} (hN : 0 < N)
    {sigma : Finset
      (ZeroFacePoint (N := N) (Fin.last (n + 1)))}
    (hsigma : sigma ∈
      lowerFreudenthalRelabeledToFace N n (Fin.last (n + 1))) :
    sigma ∈ freudenthalCoordinateFaceComplex N n (Fin.last (n + 1)) := by
  obtain ⟨tau, htau, htauImage⟩ :=
    (FiniteSimplicialComplex.mem_relabel_iff
      (freudenthalComplex N n) (zeroFaceEquiv (Fin.last (n + 1)))
      sigma).1 hsigma
  apply (mem_freudenthalCoordinateFaceComplex_iff
    (Fin.last (n + 1)) sigma).2
  have hsigmaAmbient : sigma.image Subtype.val =
      tau.image (insertZeroPoint (Fin.last (n + 1))) := by
    rw [← htauImage]
    ext b
    simp
  rw [hsigmaAmbient]
  have htauFreud := (mem_freudenthalComplex_iff tau).1 htau
  rcases htauFreud with rfl | ⟨rho, hrho, hsub⟩
  · simp
  · apply (freudenthalComplex N (n + 1)).downward_closed
      (image_insertZeroPoint_last_mem_freudenthalComplex hN hrho)
    exact Finset.image_mono (insertZeroPoint (Fin.last (n + 1))) hsub

/-- Reverse inclusion at the first coordinate face.  This direction needs no
positive-scale assumption: it starts from an existing genuine ambient facet,
collapses transfer zero, and realizes the resulting lower coordinate vectors
as actual points. -/
theorem freudenthalCoordinateFaceComplex_subset_lower_zero
    {N n : ℕ}
    {sigma : Finset (ZeroFacePoint (N := N) (0 : Fin (n + 2)))}
    (hsigma : sigma ∈
      freudenthalCoordinateFaceComplex N n (0 : Fin (n + 2))) :
    sigma ∈ lowerFreudenthalRelabeledToFace N n (0 : Fin (n + 2)) := by
  have hambient :=
    (mem_freudenthalCoordinateFaceComplex_iff 0 sigma).1 hsigma
  have hsimplex := (mem_freudenthalComplex_iff
    (sigma.image Subtype.val)).1 hambient
  rcases hsimplex with hempty | ⟨R, hRTop, hsubset⟩
  · have hsigmaEmpty : sigma = ∅ :=
      Finset.image_eq_empty.mp hempty
    subst sigma
    exact (lowerFreudenthalRelabeledToFace N n 0).empty_mem
  · obtain ⟨A, Omega, hRCoords⟩ := hRTop
    let highStep : Finset (Fin (n + 2) → ℤ) :=
      stepSimplex (pointCoords A) (permutationList Omega)
    have hhighPoint : ∀ x ∈ highStep, IsPoint (N : ℤ) x := by
      intro x hx
      have hxImage : x ∈ R.image pointCoords := by
        rw [hRCoords]
        exact hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxImage
      exact pointCoords_isPoint a
    let lowStep : Finset (Fin (n + 1) → ℤ) :=
      stepSimplex (collapseZeroCoords (pointCoords A))
        (dropZeroList (permutationList Omega))
    have hcollapseImage : highStep.image collapseZeroCoords = lowStep := by
      exact image_collapseZeroCoords_stepSimplex
        (pointCoords A) (permutationList Omega)
    have hlowPoint : ∀ x ∈ lowStep, IsPoint (N : ℤ) x := by
      intro x hx
      have hxImage : x ∈ highStep.image collapseZeroCoords := by
        rw [hcollapseImage]
        exact hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxImage
      exact collapseZeroCoords_isPoint (hhighPoint y hy)
    let L : Finset (Point N n) := realizeCoordinateSet N n lowStep
    have hLCoords : L.image pointCoords = lowStep :=
      image_pointCoords_realizeCoordinateSet lowStep hlowPoint
    have hcollapseA : IsPoint (N : ℤ)
        (collapseZeroCoords (pointCoords A)) :=
      collapseZeroCoords_isPoint (pointCoords_isPoint A)
    obtain ⟨omega, homega⟩ := exists_dropZeroPermutation Omega
    have hLTop : IsFreudenthalTopSimplex L := by
      refine ⟨pointOfIsPoint _ hcollapseA, omega, ?_⟩
      rw [hLCoords, pointCoords_pointOfIsPoint, homega]
    let tau : Finset (Point N n) :=
      sigma.image (fun b ↦ (zeroFaceEquiv (0 : Fin (n + 2))).symm b)
    have htauSubset : tau ⊆ L := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      have hbAmbient : b.1 ∈ R := by
        apply hsubset
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      have hbHigh : pointCoords b.1 ∈ highStep := by
        change pointCoords b.1 ∈
          stepSimplex (pointCoords A) (permutationList Omega)
        rw [← hRCoords]
        exact Finset.mem_image.mpr ⟨b.1, hbAmbient, rfl⟩
      have hbLow : collapseZeroCoords (pointCoords b.1) ∈ lowStep := by
        rw [← hcollapseImage]
        exact Finset.mem_image.mpr ⟨pointCoords b.1, hbHigh, rfl⟩
      have hbCoords :
          pointCoords ((zeroFaceEquiv (0 : Fin (n + 2))).symm b) ∈
            L.image pointCoords := by
        rw [hLCoords, pointCoords_zeroFaceEquiv_symm_zero]
        exact hbLow
      obtain ⟨c, hc, hcoords⟩ := Finset.mem_image.mp hbCoords
      have hca : c = (zeroFaceEquiv (0 : Fin (n + 2))).symm b :=
        pointCoords_injective hcoords
      simpa [hca] using hc
    have htau : tau ∈ freudenthalComplex N n := by
      apply (mem_freudenthalComplex_iff tau).2
      exact Or.inr ⟨L, hLTop, htauSubset⟩
    apply (FiniteSimplicialComplex.mem_relabel_iff
      (freudenthalComplex N n) (zeroFaceEquiv 0) sigma).2
    refine ⟨tau, htau, ?_⟩
    ext b
    constructor
    · intro hb
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
      obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
      have hbc : b = c := by
        rw [← hab, ← hca]
        exact Equiv.apply_symm_apply (zeroFaceEquiv 0) c
      simpa [hbc] using hc
    · intro hb
      apply Finset.mem_image.mpr
      refine ⟨(zeroFaceEquiv 0).symm b, ?_,
        Equiv.apply_symm_apply (zeroFaceEquiv 0) b⟩
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

/-- Reverse face inclusion at every positive coordinate.  Contracting the
invisible predecessor transfer turns an arbitrary ambient Freudenthal facet
into a genuine lower-dimensional facet, so no positive-scale assumption is
needed. -/
theorem freudenthalCoordinateFaceComplex_subset_lower_positive
    {N n : ℕ} (k : Fin (n + 2)) (hk : k ≠ 0)
    {sigma : Finset (ZeroFacePoint (N := N) k)}
    (hsigma : sigma ∈ freudenthalCoordinateFaceComplex N n k) :
    sigma ∈ lowerFreudenthalRelabeledToFace N n k := by
  have hambient :=
    (mem_freudenthalCoordinateFaceComplex_iff k sigma).1 hsigma
  have hsimplex := (mem_freudenthalComplex_iff
    (sigma.image Subtype.val)).1 hambient
  rcases hsimplex with hempty | ⟨R, hRTop, hsubset⟩
  · have hsigmaEmpty : sigma = ∅ := Finset.image_eq_empty.mp hempty
    subst sigma
    exact (lowerFreudenthalRelabeledToFace N n k).empty_mem
  · obtain ⟨A, Omega, hRCoords⟩ := hRTop
    let highStep : Finset (Fin (n + 2) → ℤ) :=
      stepSimplex (pointCoords A) (permutationList Omega)
    have hhighPoint : ∀ x ∈ highStep, IsPoint (N : ℤ) x := by
      intro x hx
      have hxImage : x ∈ R.image pointCoords := by
        rw [hRCoords]
        exact hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxImage
      exact pointCoords_isPoint a
    let lowStep : Finset (Fin (n + 1) → ℤ) :=
      stepSimplex (collapsePositiveCoords k hk (pointCoords A))
        (dropPositiveList k hk (permutationList Omega))
    have hcollapseImage :
        highStep.image (collapsePositiveCoords k hk) = lowStep := by
      exact image_collapsePositiveCoords_stepSimplex k hk
        (pointCoords A) (permutationList Omega)
    have hlowPoint : ∀ x ∈ lowStep, IsPoint (N : ℤ) x := by
      intro x hx
      have hxImage :
          x ∈ highStep.image (collapsePositiveCoords k hk) := by
        rw [hcollapseImage]
        exact hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxImage
      exact collapsePositiveCoords_isPoint k hk (hhighPoint y hy)
    let L : Finset (Point N n) := realizeCoordinateSet N n lowStep
    have hLCoords : L.image pointCoords = lowStep :=
      image_pointCoords_realizeCoordinateSet lowStep hlowPoint
    have hcollapseA : IsPoint (N : ℤ)
        (collapsePositiveCoords k hk (pointCoords A)) :=
      collapsePositiveCoords_isPoint k hk (pointCoords_isPoint A)
    obtain ⟨omega, homega⟩ :=
      exists_dropPositivePermutation k hk Omega
    have hLTop : IsFreudenthalTopSimplex L := by
      refine ⟨pointOfIsPoint _ hcollapseA, omega, ?_⟩
      rw [hLCoords, pointCoords_pointOfIsPoint, homega]
    let tau : Finset (Point N n) :=
      sigma.image (fun b ↦ (zeroFaceEquiv k).symm b)
    have htauSubset : tau ⊆ L := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      have hbAmbient : b.1 ∈ R := by
        apply hsubset
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      have hbHigh : pointCoords b.1 ∈ highStep := by
        change pointCoords b.1 ∈
          stepSimplex (pointCoords A) (permutationList Omega)
        rw [← hRCoords]
        exact Finset.mem_image.mpr ⟨b.1, hbAmbient, rfl⟩
      have hbLow :
          collapsePositiveCoords k hk (pointCoords b.1) ∈ lowStep := by
        rw [← hcollapseImage]
        exact Finset.mem_image.mpr ⟨pointCoords b.1, hbHigh, rfl⟩
      have hbCoords :
          pointCoords ((zeroFaceEquiv k).symm b) ∈
            L.image pointCoords := by
        rw [hLCoords, pointCoords_zeroFaceEquiv_symm_positive k hk]
        exact hbLow
      obtain ⟨c, hc, hcoords⟩ := Finset.mem_image.mp hbCoords
      have hca : c = (zeroFaceEquiv k).symm b :=
        pointCoords_injective hcoords
      simpa [hca] using hc
    have htau : tau ∈ freudenthalComplex N n := by
      apply (mem_freudenthalComplex_iff tau).2
      exact Or.inr ⟨L, hLTop, htauSubset⟩
    apply (FiniteSimplicialComplex.mem_relabel_iff
      (freudenthalComplex N n) (zeroFaceEquiv k) sigma).2
    refine ⟨tau, htau, ?_⟩
    ext b
    constructor
    · intro hb
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
      obtain ⟨c, hc, hca⟩ := Finset.mem_image.mp ha
      have hbc : b = c := by
        rw [← hab, ← hca]
        exact Equiv.apply_symm_apply (zeroFaceEquiv k) c
      simpa [hbc] using hc
    · intro hb
      apply Finset.mem_image.mpr
      refine ⟨(zeroFaceEquiv k).symm b, ?_,
        Equiv.apply_symm_apply (zeroFaceEquiv k) b⟩
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

/-- Reverse Freudenthal coordinate-face inclusion for every coordinate and
every scale. -/
theorem freudenthalCoordinateFaceComplex_subset_lower
    {N n : ℕ} (k : Fin (n + 2))
    {sigma : Finset (ZeroFacePoint (N := N) k)}
    (hsigma : sigma ∈ freudenthalCoordinateFaceComplex N n k) :
    sigma ∈ lowerFreudenthalRelabeledToFace N n k := by
  by_cases hk : k = 0
  · subst k
    exact freudenthalCoordinateFaceComplex_subset_lower_zero hsigma
  · exact freudenthalCoordinateFaceComplex_subset_lower_positive k hk hsigma

/-- Forward Freudenthal coordinate-face inclusion for every coordinate at
positive scale.  The proof deliberately separates coordinate zero, interior
positive coordinates, and the last coordinate because their transfer-path
extensions are genuinely different. -/
theorem lowerFreudenthalRelabeledToFace_subset
    {N n : ℕ} (hN : 0 < N) (k : Fin (n + 2))
    {sigma : Finset (ZeroFacePoint (N := N) k)}
    (hsigma : sigma ∈ lowerFreudenthalRelabeledToFace N n k) :
    sigma ∈ freudenthalCoordinateFaceComplex N n k := by
  induction k using Fin.cases with
  | zero =>
    exact lowerFreudenthalRelabeledToFace_subset_zero hN hsigma
  | succ d =>
    by_cases hdlast : d = Fin.last n
    · subst d
      have hface : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        simp
      cases hface
      exact lowerFreudenthalRelabeledToFace_subset_last hN hsigma
    ·
      exact lowerFreudenthalRelabeledToFace_subset_interior d hdlast hsigma

/-- Exact face identification for the first coordinate.  The hypothesis
`0 < N` cannot be removed: at scale zero the positive-dimensional ambient
complex has no genuine facets. -/
theorem lowerFreudenthalRelabeledToFace_eq_coordinateFace_zero
    {N n : ℕ} (hN : 0 < N) :
    lowerFreudenthalRelabeledToFace N n (0 : Fin (n + 2)) =
      freudenthalCoordinateFaceComplex N n (0 : Fin (n + 2)) := by
  apply FiniteSimplicialComplex.ext
  ext sigma
  constructor
  · exact lowerFreudenthalRelabeledToFace_subset_zero hN
  · exact freudenthalCoordinateFaceComplex_subset_lower_zero

/-- Exact Freudenthal face identification for every coordinate at positive
scale. -/
theorem lowerFreudenthalRelabeledToFace_eq_coordinateFace
    {N n : ℕ} (hN : 0 < N) (k : Fin (n + 2)) :
    lowerFreudenthalRelabeledToFace N n k =
      freudenthalCoordinateFaceComplex N n k := by
  apply FiniteSimplicialComplex.ext
  ext sigma
  constructor
  · exact lowerFreudenthalRelabeledToFace_subset hN k
  · exact freudenthalCoordinateFaceComplex_subset_lower k

/-- The `I \ {k}` Scarf complex, viewed on the coordinate-face vertex type. -/
noncomputable def scarfCoordinateFaceComplex (N n : ℕ)
    (k : Fin (n + 2)) :
    FiniteSimplicialComplex (ZeroFacePoint (N := N) k) :=
  ((pointOrders N (n + 1)).associatedComplex
    (Finset.univ.erase k)).inducedOn (fun b ↦ (b.1 k).val = 0)

/-- Lemma 4.7 at the complex level: every vertex of every simplex in
`T(I \ {k})` really lies on `x_k = 0`. -/
theorem associatedFace_simplex_vertex_coord_zero {N n : ℕ}
    (k : Fin (n + 2)) {tau : Finset (Point N (n + 1))}
    (htau : tau ∈ (pointOrders N (n + 1)).associatedComplex
      (Finset.univ.erase k)) {a : Point N (n + 1)} (ha : a ∈ tau) :
    pointCoords a k = 0 := by
  have hCne : (Finset.univ.erase k : Finset (Fin (n + 2))) ≠ ∅ := by
    intro hempty
    have hmem : k.succAbove (0 : Fin (n + 1)) ∈
        (Finset.univ.erase k : Finset (Fin (n + 2))) := by
      simp [Fin.succAbove_ne]
    rw [hempty] at hmem
    simp at hmem
  have hassoc := (Finset.mem_filter.mp htau).2
  rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg hCne] at hassoc
  rcases hassoc with hzero | ⟨sigma, hcell, htausigma⟩
  · subst tau
    simp at ha
  · exact coord_eq_zero_of_isCell_of_not_mem hcell
      (htausigma ha) (by simp)

theorem mem_scarfCoordinateFaceComplex_iff {N n : ℕ}
    (k : Fin (n + 2))
    (sigma : Finset (ZeroFacePoint (N := N) k)) :
    sigma ∈ scarfCoordinateFaceComplex N n k ↔
      sigma.image Subtype.val ∈
        (pointOrders N (n + 1)).associatedComplex
          (Finset.univ.erase k) := by
  exact FiniteSimplicialComplex.mem_inducedOn_iff _ _ _

/-- Bundle an ambient simplex whose vertices lie on `x_k = 0` as a simplex
on the coordinate-face vertex type.  The definition is total; exact recovery
is stated separately with the necessary face-containment hypothesis. -/
noncomputable def bundleZeroFaceSimplex {N n : ℕ}
    (k : Fin (n + 2)) (tau : Finset (Point N (n + 1))) :
    Finset (ZeroFacePoint (N := N) k) :=
  Finset.univ.filter fun b ↦ b.1 ∈ tau

/-- If every ambient vertex has zero `k`-th coordinate, bundling and then
forgetting the proof recovers the ambient simplex exactly. -/
theorem image_bundleZeroFaceSimplex {N n : ℕ}
    (k : Fin (n + 2)) (tau : Finset (Point N (n + 1)))
    (hzero : ∀ a ∈ tau, (a.1 k).val = 0) :
    (bundleZeroFaceSimplex k tau).image Subtype.val = tau := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hb).2
  · intro ha
    let b : ZeroFacePoint (N := N) k := ⟨a, hzero a ha⟩
    exact Finset.mem_image.mpr
      ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩

/-- A bundled simplex is uniquely determined by its ambient vertex image.
This prevents the subtype packaging used in the induction from introducing
duplicate or spurious simplices. -/
theorem eq_bundleZeroFaceSimplex_of_image_eq {N n : ℕ}
    (k : Fin (n + 2)) (tau : Finset (Point N (n + 1)))
    (sigma : Finset (ZeroFacePoint (N := N) k))
    (himage : sigma.image Subtype.val = tau) :
    sigma = bundleZeroFaceSimplex k tau := by
  have hzero : ∀ a ∈ tau, (a.1 k).val = 0 := by
    intro a ha
    rw [← himage] at ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    rw [← hba]
    exact b.2
  apply Finset.image_injective Subtype.val_injective
  rw [himage, image_bundleZeroFaceSimplex k tau hzero]

/-- Associated-simplex membership on the coordinate face is exactly ambient
`I \ {k}` associated-simplex membership.  This includes both the empty
simplex and all subfaces of full cells. -/
theorem isAssociatedSimplex_coordinateFace_iff_ambient {N n : ℕ}
    (k : Fin (n + 2)) (sigma : Finset (ZeroFacePoint (N := N) k)) :
    (pointOrders N (n + 1)).IsAssociatedSimplex
        ((Finset.univ : Finset (Fin (n + 2))).erase k)
        (sigma.image Subtype.val) ↔
      (facePointOrders N n k).IsAssociatedSimplex Finset.univ sigma := by
  have hC : ((Finset.univ : Finset (Fin (n + 2))).erase k) ≠ ∅ := by
    intro hEmpty
    have hmem : k.succAbove (0 : Fin (n + 1)) ∈
        ((Finset.univ : Finset (Fin (n + 2))).erase k) := by
      simp [Fin.succAbove_ne]
    rw [hEmpty] at hmem
    simp at hmem
  have hUniv : (Finset.univ : Finset (Fin (n + 1))) ≠ ∅ := by
    intro hEmpty
    have hmem : (0 : Fin (n + 1)) ∈
        (Finset.univ : Finset (Fin (n + 1))) := Finset.mem_univ _
    rw [hEmpty] at hmem
    simp at hmem
  rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg hC,
    IndexedLinearOrders.IsAssociatedSimplex, if_neg hUniv]
  constructor
  · intro hambient
    rcases hambient with hEmpty | ⟨rho, hrhoCell, hsubset⟩
    · left
      exact Finset.image_eq_empty.mp hEmpty
    · right
      have hzero : ∀ a ∈ rho, (a.1 k).val = 0 := by
        intro a ha
        have hcoord := coord_eq_zero_of_isCell_of_not_mem
          (k := k) hrhoCell ha (by simp)
        change (((a.1 k).val : ℕ) : ℤ) = 0 at hcoord
        omega
      let rhoFace : Finset (ZeroFacePoint (N := N) k) :=
        bundleZeroFaceSimplex k rho
      have hrhoImage : rhoFace.image Subtype.val = rho :=
        image_bundleZeroFaceSimplex k rho hzero
      refine ⟨rhoFace, ?_, ?_⟩
      · apply (isCell_coordinateFace_iff_ambient k rhoFace).1
        simpa [hrhoImage] using hrhoCell
      · intro b hb
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply hsubset
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  · intro hface
    rcases hface with rfl | ⟨rho, hrhoCell, hsubset⟩
    · left
      simp
    · right
      refine ⟨rho.image Subtype.val, ?_, Finset.image_mono _ hsubset⟩
      exact (isCell_coordinateFace_iff_ambient k rho).2 hrhoCell

/-- Associated-simplex membership on a coordinate face for an arbitrary
lower index set `A`.  Both empty-index and empty-simplex conventions are
preserved exactly by the injective index and vertex maps. -/
theorem isAssociatedSimplex_coordinateFace_image_iff_ambient
    {N n : ℕ} (k : Fin (n + 2)) (A : Finset (Fin (n + 1)))
    (sigma : Finset (ZeroFacePoint (N := N) k)) :
    (pointOrders N (n + 1)).IsAssociatedSimplex
        (A.image fun i ↦ k.succAbove i) (sigma.image Subtype.val) ↔
      (facePointOrders N n k).IsAssociatedSimplex A sigma := by
  by_cases hA : A = ∅
  · subst A
    simp [IndexedLinearOrders.IsAssociatedSimplex]
  · have hAImage : A.image (fun i ↦ k.succAbove i) ≠ ∅ := by
      simpa using hA
    rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg hAImage,
      IndexedLinearOrders.IsAssociatedSimplex, if_neg hA]
    constructor
    · intro hambient
      rcases hambient with hEmpty | ⟨rho, hrhoCell, hsubset⟩
      · left
        exact Finset.image_eq_empty.mp hEmpty
      · right
        have hzero : ∀ a ∈ rho, (a.1 k).val = 0 := by
          intro a ha
          have hkImage : k ∉ A.image (fun i ↦ k.succAbove i) := by
            simp [Fin.succAbove_ne]
          have hcoord := coord_eq_zero_of_isCell_of_not_mem
            (k := k) hrhoCell ha hkImage
          change (((a.1 k).val : ℕ) : ℤ) = 0 at hcoord
          omega
        let rhoFace : Finset (ZeroFacePoint (N := N) k) :=
          bundleZeroFaceSimplex k rho
        have hrhoImage : rhoFace.image Subtype.val = rho :=
          image_bundleZeroFaceSimplex k rho hzero
        refine ⟨rhoFace, ?_, ?_⟩
        · apply (isCell_coordinateFace_image_iff_ambient k A rhoFace).1
          simpa [hrhoImage] using hrhoCell
        · intro b hb
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          apply hsubset
          exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    · intro hface
      rcases hface with rfl | ⟨rho, hrhoCell, hsubset⟩
      · left
        simp
      · right
        refine ⟨rho.image Subtype.val, ?_, Finset.image_mono _ hsubset⟩
        exact (isCell_coordinateFace_image_iff_ambient k A rho).2 hrhoCell

/-- The associated complex of the pulled-back orders is exactly the induced
ambient Scarf face complex for every deleted coordinate. -/
theorem facePointOrders_associatedComplex_eq_scarfCoordinateFaceComplex
    {N n : ℕ} (k : Fin (n + 2)) :
    (facePointOrders N n k).associatedComplex Finset.univ =
      scarfCoordinateFaceComplex N n k := by
  apply FiniteSimplicialComplex.ext
  ext sigma
  change sigma ∈ (facePointOrders N n k).associatedComplex Finset.univ ↔
    sigma ∈ scarfCoordinateFaceComplex N n k
  rw [mem_scarfCoordinateFaceComplex_iff]
  have hAmbient :
      sigma.image Subtype.val ∈
          (pointOrders N (n + 1)).associatedComplex
            ((Finset.univ : Finset (Fin (n + 2))).erase k) ↔
        (pointOrders N (n + 1)).IsAssociatedSimplex
          ((Finset.univ : Finset (Fin (n + 2))).erase k)
          (sigma.image Subtype.val) := by
    change sigma.image Subtype.val ∈ Finset.univ.filter _ ↔ _
    simp
  rw [hAmbient]
  change sigma ∈ Finset.univ.filter
      ((facePointOrders N n k).IsAssociatedSimplex Finset.univ) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (isAssociatedSimplex_coordinateFace_iff_ambient k sigma).symm

/-- Complete Scarf coordinate-face identification in every coordinate and
at every scale.  No positive-scale hypothesis is needed because this is an
order-theoretic complex equality, not a Freudenthal facet-extension claim. -/
theorem lowerScarfRelabeledToFace_eq_coordinateFace {N n : ℕ}
    (k : Fin (n + 2)) :
    lowerScarfRelabeledToFace N n k =
      scarfCoordinateFaceComplex N n k := by
  rw [lowerScarfRelabeledToFace_eq_facePointOrders,
    facePointOrders_associatedComplex_eq_scarfCoordinateFaceComplex]

/-- Associated-simplex membership on the first face is exactly ambient
`I \ {0}` associated-simplex membership.  This is stronger than Lemma 4.7's
vertex containment and supplies the missing converse used by the induction. -/
theorem isAssociatedSimplex_zeroFace_iff_ambient {N n : ℕ}
    (sigma : Finset (ZeroFacePoint (N := N) (0 : Fin (n + 2)))) :
    (pointOrders N (n + 1)).IsAssociatedSimplex
        ((Finset.univ : Finset (Fin (n + 2))).erase 0)
        (sigma.image Subtype.val) ↔
      (zeroFacePointOrders N n).IsAssociatedSimplex Finset.univ sigma := by
  have hC : ((Finset.univ : Finset (Fin (n + 2))).erase 0) ≠ ∅ := by
    intro hEmpty
    have hmem : (0 : Fin (n + 1)).succ ∈
        ((Finset.univ : Finset (Fin (n + 2))).erase 0) := by simp
    rw [hEmpty] at hmem
    simp at hmem
  have hUniv : (Finset.univ : Finset (Fin (n + 1))) ≠ ∅ := by
    intro hEmpty
    have hmem : (0 : Fin (n + 1)) ∈ (Finset.univ : Finset (Fin (n + 1))) :=
      Finset.mem_univ _
    rw [hEmpty] at hmem
    simp at hmem
  rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg hC,
    IndexedLinearOrders.IsAssociatedSimplex, if_neg hUniv]
  constructor
  · intro hambient
    rcases hambient with hEmpty | ⟨rho, hrhoCell, hsubset⟩
    · left
      exact Finset.image_eq_empty.mp hEmpty
    · right
      have hzero : ∀ a ∈ rho, (a.1 (0 : Fin (n + 2))).val = 0 := by
        intro a ha
        have hcoord := coord_eq_zero_of_isCell_of_not_mem
          (k := (0 : Fin (n + 2))) hrhoCell ha (by simp)
        change (((a.1 (0 : Fin (n + 2))).val : ℕ) : ℤ) = 0 at hcoord
        omega
      let rhoFace : Finset (ZeroFacePoint (N := N) (0 : Fin (n + 2))) :=
        bundleZeroFaceSimplex 0 rho
      have hrhoImage : rhoFace.image Subtype.val = rho :=
        image_bundleZeroFaceSimplex 0 rho hzero
      refine ⟨rhoFace, ?_, ?_⟩
      · apply (isCell_zeroFace_iff_ambient rhoFace).1
        simpa [hrhoImage] using hrhoCell
      · intro b hb
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply hsubset
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  · intro hface
    rcases hface with rfl | ⟨rho, hrhoCell, hsubset⟩
    · left
      simp
    · right
      refine ⟨rho.image Subtype.val, ?_, Finset.image_mono _ hsubset⟩
      exact (isCell_zeroFace_iff_ambient rho).2 hrhoCell

/-- Exact equality between the associated complex of the pulled-back face
orders and the induced ambient Scarf face complex. -/
theorem zeroFaceOrders_associatedComplex_eq_scarfCoordinateFaceComplex
    {N n : ℕ} :
    (zeroFacePointOrders N n).associatedComplex Finset.univ =
      scarfCoordinateFaceComplex N n (0 : Fin (n + 2)) := by
  apply FiniteSimplicialComplex.ext
  ext sigma
  change sigma ∈ (zeroFacePointOrders N n).associatedComplex Finset.univ ↔
    sigma ∈ scarfCoordinateFaceComplex N n (0 : Fin (n + 2))
  rw [mem_scarfCoordinateFaceComplex_iff]
  have hAmbient :
      sigma.image Subtype.val ∈
          (pointOrders N (n + 1)).associatedComplex
            ((Finset.univ : Finset (Fin (n + 2))).erase 0) ↔
        (pointOrders N (n + 1)).IsAssociatedSimplex
          ((Finset.univ : Finset (Fin (n + 2))).erase 0)
          (sigma.image Subtype.val) := by
    change sigma.image Subtype.val ∈ Finset.univ.filter _ ↔ _
    simp
  rw [hAmbient]
  change sigma ∈ Finset.univ.filter
      ((zeroFacePointOrders N n).IsAssociatedSimplex Finset.univ) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (isAssociatedSimplex_zeroFace_iff_ambient sigma).symm

/-- The complete Scarf face identification at the first coordinate.  Unlike
the Freudenthal facet-extension direction, this order-theoretic equality does
not require a positive-scale hypothesis. -/
theorem lowerScarfRelabeledToFace_eq_coordinateFace_zero {N n : ℕ} :
    lowerScarfRelabeledToFace N n (0 : Fin (n + 2)) =
      scarfCoordinateFaceComplex N n (0 : Fin (n + 2)) := by
  rw [lowerScarfRelabeledToFace_eq_zeroFaceOrders,
    zeroFaceOrders_associatedComplex_eq_scarfCoordinateFaceComplex]

/-- Exact bundled form of Lemma 4.7 for `T(I \ {k})`: every ambient
simplex has a unique representative in the coordinate-face complex. -/
theorem associatedFace_existsUnique_bundledSimplex {N n : ℕ}
    (k : Fin (n + 2)) {tau : Finset (Point N (n + 1))}
    (htau : tau ∈ (pointOrders N (n + 1)).associatedComplex
      (Finset.univ.erase k)) :
    ∃! sigma : Finset (ZeroFacePoint (N := N) k),
      sigma ∈ scarfCoordinateFaceComplex N n k ∧
        sigma.image Subtype.val = tau := by
  have hzero : ∀ a ∈ tau, (a.1 k).val = 0 := by
    intro a ha
    have hcoord := associatedFace_simplex_vertex_coord_zero k htau ha
    simpa [pointCoords] using hcoord
  refine ⟨bundleZeroFaceSimplex k tau, ?_, ?_⟩
  · have himage := image_bundleZeroFaceSimplex k tau hzero
    have hmem : bundleZeroFaceSimplex k tau ∈
        scarfCoordinateFaceComplex N n k :=
      (mem_scarfCoordinateFaceComplex_iff k _).2 (by
        rw [himage]
        exact htau)
    exact ⟨hmem, himage⟩
  · intro sigma hsigma
    exact eq_bundleZeroFaceSimplex_of_image_eq k tau sigma hsigma.2

/-- Every simplex generated by a `C`-cell is a simplex of the ambient
Freudenthal triangulation at positive scale, for an arbitrary index subset
`C`.  The proof inductively deletes a coordinate outside `C`, transports the
simplex through the exact arbitrary-index coordinate-face equivalence, and
uses the already proved one-coordinate Freudenthal facet extension. -/
theorem associatedComplex_subset_freudenthalComplex_of_pos
    {N : ℕ} (hN : 0 < N) :
    ∀ (n : ℕ) (C : Finset (Fin (n + 1)))
      {tau : Finset (Point N n)},
      tau ∈ (pointOrders N n).associatedComplex C →
        tau ∈ freudenthalComplex N n := by
  intro n
  induction n with
  | zero =>
      intro C tau htau
      by_cases hC : C = Finset.univ
      · subst C
        exact associatedComplex_subset_freudenthalComplex htau
      · have hCempty : C = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hCnonempty
          obtain ⟨i, hi⟩ := hCnonempty
          apply hC
          apply Finset.eq_univ_of_forall
          intro j
          have hji : j = i := by
            apply Fin.ext
            omega
          exact hji ▸ hi
        subst C
        have hassoc :
            (pointOrders N 0).IsAssociatedSimplex
              (∅ : Finset (Fin 1)) tau :=
          (Finset.mem_filter.mp htau).2
        rw [IndexedLinearOrders.IsAssociatedSimplex, if_pos rfl] at hassoc
        subst tau
        exact (freudenthalComplex N 0).empty_mem
  | succ n ih =>
      intro C tau htau
      by_cases hC : C = Finset.univ
      · subst C
        exact associatedComplex_subset_freudenthalComplex htau
      · obtain ⟨k, hkC⟩ : ∃ k : Fin (n + 2), k ∉ C := by
          by_contra h
          have hAll : ∀ k : Fin (n + 2), k ∈ C := by
            simpa only [not_exists, not_not] using h
          exact hC (Finset.eq_univ_of_forall hAll)
        let A : Finset (Fin (n + 1)) :=
          Finset.univ.filter fun i ↦ k.succAbove i ∈ C
        have hAImage : A.image (fun i ↦ k.succAbove i) = C := by
          ext j
          constructor
          · intro hj
            obtain ⟨i, hiA, hij⟩ := Finset.mem_image.mp hj
            have hiC : k.succAbove i ∈ C :=
              (Finset.mem_filter.mp hiA).2
            simpa [hij] using hiC
          · intro hjC
            have hjk : j ≠ k := fun h ↦ hkC (h ▸ hjC)
            obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hjk
            apply Finset.mem_image.mpr
            refine ⟨i, ?_, hi⟩
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ _, hi ▸ hjC⟩
        have hzero : ∀ a ∈ tau, (a.1 k).val = 0 := by
          intro a ha
          have hcoord := coord_eq_zero_of_mem_associatedComplex_of_not_mem
            htau ha hkC
          change (((a.1 k).val : ℕ) : ℤ) = 0 at hcoord
          omega
        let sigma : Finset (ZeroFacePoint (N := N) k) :=
          bundleZeroFaceSimplex k tau
        have hsigmaImage : sigma.image Subtype.val = tau :=
          image_bundleZeroFaceSimplex k tau hzero
        have htauAssoc :
            (pointOrders N (n + 1)).IsAssociatedSimplex C tau :=
          (Finset.mem_filter.mp htau).2
        have hsigmaFaceAssoc :
            (facePointOrders N n k).IsAssociatedSimplex A sigma := by
          apply (isAssociatedSimplex_coordinateFace_image_iff_ambient
            k A sigma).1
          simpa [hAImage, hsigmaImage] using htauAssoc
        have hsigmaFace :
            sigma ∈ (facePointOrders N n k).associatedComplex A := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, hsigmaFaceAssoc⟩
        have hrelabeled :
            ((pointOrders N n).associatedComplex A).relabel
                (zeroFaceEquiv k) =
              (facePointOrders N n k).associatedComplex A := by
          simpa using IndexedLinearOrders.associatedComplex_relabel
            (pointOrders N n) (facePointOrders N n k)
            (Equiv.refl (Fin (n + 1))) (zeroFaceEquiv k)
            (fun i x y ↦
              (facePointOrders_zeroFaceEquiv_le_iff k i x y).symm) A
        have hsigmaRelabeled :
            sigma ∈ ((pointOrders N n).associatedComplex A).relabel
              (zeroFaceEquiv k) := by
          rw [hrelabeled]
          exact hsigmaFace
        obtain ⟨eta, heta, hetaImage⟩ :=
          (FiniteSimplicialComplex.mem_relabel_iff
            ((pointOrders N n).associatedComplex A)
            (zeroFaceEquiv k) sigma).1 hsigmaRelabeled
        have hetaFreudenthal : eta ∈ freudenthalComplex N n :=
          ih A heta
        have hsigmaLower :
            sigma ∈ lowerFreudenthalRelabeledToFace N n k := by
          apply (FiniteSimplicialComplex.mem_relabel_iff
            (freudenthalComplex N n) (zeroFaceEquiv k) sigma).2
          exact ⟨eta, hetaFreudenthal, hetaImage⟩
        have hsigmaAmbient :=
          lowerFreudenthalRelabeledToFace_subset hN k hsigmaLower
        have himageAmbient :=
          (mem_freudenthalCoordinateFaceComplex_iff k sigma).1
            hsigmaAmbient
        simpa [hsigmaImage] using himageAmbient

end IntegerSimplex

end BeyondSperner
