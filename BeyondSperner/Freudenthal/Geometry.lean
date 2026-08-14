import BeyondSperner.Freudenthal.Faces

/-!
# Local geometry of the finite Freudenthal complex

This file develops the concrete local combinatorics used in Theorem 4.8.
The first invariant is the sum of cumulative coordinates.  Along a
Freudenthal permutation path it increases by exactly one at every step.
Consequently a top simplex has one vertex in each of `n+1` consecutive
integer ranks.  This rank is intrinsic to a vertex and will be used to
classify codimension-one cofaces rather than assuming nonbranching as an
interface.
-/

namespace BeyondSperner

open Classical

namespace IntegerSimplex

/-- Sum of cumulative coordinates.  It is the intrinsic rank used to order
vertices of a Freudenthal simplex. -/
def cumulativeWeight {n : ℕ} (u : Fin n → ℤ) : ℤ :=
  ∑ i, u i

/-- A block of `n+1` consecutive intrinsic ranks. -/
def consecutiveRanks (z : ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.range (n + 1)).image (fun r : ℕ ↦ z + r)

theorem mem_consecutiveRanks_iff {z x : ℤ} {n : ℕ} :
    x ∈ consecutiveRanks z n ↔
      ∃ r : ℕ, r < n + 1 ∧ x = z + r := by
  simp [consecutiveRanks, eq_comm]

theorem bounds_of_mem_consecutiveRanks {z x : ℤ} {n : ℕ}
    (hx : x ∈ consecutiveRanks z n) :
    z ≤ x ∧ x ≤ z + n := by
  obtain ⟨r, hr, rfl⟩ := mem_consecutiveRanks_iff.mp hx
  omega

/-- Consecutive ranks are exactly the integer interval from `z` through
`z+n`.  The converse is useful when classifying the one rank omitted by a
codimension-one face. -/
theorem mem_consecutiveRanks_iff_bounds {z x : ℤ} {n : ℕ} :
    x ∈ consecutiveRanks z n ↔ z ≤ x ∧ x ≤ z + n := by
  constructor
  · exact bounds_of_mem_consecutiveRanks
  · rintro ⟨hzx, hxn⟩
    let r : ℕ := (x - z).toNat
    have hsub : 0 ≤ x - z := sub_nonneg.mpr hzx
    have hrCast : (r : ℤ) = x - z := by
      exact Int.toNat_of_nonneg hsub
    apply mem_consecutiveRanks_iff.mpr
    refine ⟨r, ?_, ?_⟩
    · have : (r : ℤ) ≤ n := by omega
      have hrle : r ≤ n := by exact_mod_cast this
      omega
    ·
      omega

@[simp]
theorem card_consecutiveRanks (z : ℤ) (n : ℕ) :
    (consecutiveRanks z n).card = n + 1 := by
  rw [consecutiveRanks, Finset.card_image_of_injective]
  · simp
  · intro r s h
    have h' : (r : ℤ) = (s : ℤ) := add_left_cancel h
    exact_mod_cast h'

/-- `n` common ranks in two blocks of `n+1` consecutive integers force the
two initial ranks to differ by at most one. -/
theorem consecutiveRanks_bases_close {n : ℕ} (hn : 0 < n)
    {R : Finset ℤ} {z w : ℤ}
    (hcard : R.card = n)
    (hRz : R ⊆ consecutiveRanks z n)
    (hRw : R ⊆ consecutiveRanks w n) :
    z ≤ w + 1 ∧ w ≤ z + 1 := by
  let rankIndices (base : ℤ) : Finset ℕ :=
    (Finset.range (n + 1)).filter fun r ↦ base + r ∈ R
  have image_rankIndices (base : ℤ)
      (hR : R ⊆ consecutiveRanks base n) :
      (rankIndices base).image (fun r : ℕ ↦ base + r) = R := by
    ext x
    constructor
    · intro hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hr).2
    · intro hx
      obtain ⟨r, hr, hxr⟩ := mem_consecutiveRanks_iff.mp (hR hx)
      apply Finset.mem_image.mpr
      refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, ?_⟩, ?_⟩
      · exact hxr ▸ hx
      · exact hxr.symm
  have card_rankIndices (base : ℤ)
      (hR : R ⊆ consecutiveRanks base n) :
      (rankIndices base).card = n := by
    calc
      (rankIndices base).card =
          ((rankIndices base).image (fun r : ℕ ↦ base + r)).card := by
        symm
        apply Finset.card_image_of_injOn
        intro r _ s _ h
        have h' : (r : ℤ) = (s : ℤ) := add_left_cancel h
        exact_mod_cast h'
      _ = R.card := congrArg Finset.card (image_rankIndices base hR)
      _ = n := hcard
  have upper : w ≤ z + 1 := by
    by_contra hnot
    have hzw : z + 2 ≤ w := by omega
    have hsub : rankIndices z ⊆ Finset.Ico 2 (n + 1) := by
      intro r hr
      have hrData := Finset.mem_filter.mp hr
      have hxBounds := bounds_of_mem_consecutiveRanks (hRw hrData.2)
      simp only [Finset.mem_Ico]
      constructor
      ·
        omega
      · exact Finset.mem_range.mp hrData.1
    have hle := Finset.card_le_card hsub
    rw [card_rankIndices z hRz] at hle
    simp at hle
    omega
  have lower : z ≤ w + 1 := by
    by_contra hnot
    have hwz : w + 2 ≤ z := by omega
    have hsub : rankIndices w ⊆ Finset.Ico 2 (n + 1) := by
      intro r hr
      have hrData := Finset.mem_filter.mp hr
      have hxBounds := bounds_of_mem_consecutiveRanks (hRz hrData.2)
      simp only [Finset.mem_Ico]
      constructor
      ·
        omega
      · exact Finset.mem_range.mp hrData.1
    have hle := Finset.card_le_card hsub
    rw [card_rankIndices w hRw] at hle
    simp at hle
    omega
  exact ⟨lower, upper⟩

/-- A cardinality-`n` subset of an `(n+1)`-rank block is obtained by erasing
one actual rank. -/
theorem exists_erased_rank_of_subset_consecutiveRanks {n : ℕ}
    {R : Finset ℤ} {z : ℤ}
    (hcard : R.card = n)
    (hsub : R ⊆ consecutiveRanks z n) :
    ∃ m ∈ consecutiveRanks z n,
      R = (consecutiveRanks z n).erase m := by
  have hmissing : ∃ m ∈ consecutiveRanks z n, m ∉ R := by
    by_contra hnot
    push Not at hnot
    have hreverse : consecutiveRanks z n ⊆ R := fun m hm ↦ hnot m hm
    have heq : R = consecutiveRanks z n :=
      Finset.Subset.antisymm hsub hreverse
    have := congrArg Finset.card heq
    simp [hcard] at this
  obtain ⟨m, hmBlock, hmR⟩ := hmissing
  refine ⟨m, hmBlock, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_erase]
    exact ⟨fun hxm ↦ hmR (hxm ▸ hx), hsub hx⟩
  · rw [Finset.card_erase_of_mem hmBlock,
      card_consecutiveRanks, hcard]
    omega

/-- Exact rank alternatives for a second top simplex containing the same
codimension-one rank set.  Besides the erased rank itself, a new rank can
occur only across an endpoint, and then it is the next rank just outside the
original block. -/
theorem completion_rank_cases {n : ℕ} (hn : 0 < n)
    {R : Finset ℤ} {z m w x : ℤ}
    (hcard : R.card = n)
    (_hmBlock : m ∈ consecutiveRanks z n)
    (hRerase : R = (consecutiveRanks z n).erase m)
    (hRw : R ⊆ consecutiveRanks w n)
    (hxw : x ∈ consecutiveRanks w n) (hxR : x ∉ R) :
    x = m ∨
      (m = z ∧ x = z + n + 1) ∨
      (m = z + n ∧ x = z - 1) := by
  have hRz : R ⊆ consecutiveRanks z n := by
    rw [hRerase]
    exact Finset.erase_subset _ _
  have hclose := consecutiveRanks_bases_close hn hcard hRz hRw
  have hwCases : w = z - 1 ∨ w = z ∨ w = z + 1 := by omega
  rcases hwCases with hw | hw | hw
  · right
    right
    have hmLast : m = z + n := by
      by_contra hm
      have hzLastBlock : z + n ∈ consecutiveRanks z n := by
        apply mem_consecutiveRanks_iff_bounds.mpr
        constructor <;> omega
      have hzLastR : z + n ∈ R := by
        rw [hRerase]
        exact Finset.mem_erase.mpr ⟨Ne.symm hm, hzLastBlock⟩
      have hzLastW := bounds_of_mem_consecutiveRanks (hRw hzLastR)
      omega
    refine ⟨hmLast, ?_⟩
    have hxBounds := bounds_of_mem_consecutiveRanks hxw
    by_contra hx
    have hxLower : z ≤ x := by omega
    have hxInOld : x ∈ consecutiveRanks z n :=
      mem_consecutiveRanks_iff_bounds.mpr ⟨hxLower, by omega⟩
    have hxm : x ≠ m := by omega
    exact hxR (by rw [hRerase]; exact Finset.mem_erase.mpr ⟨hxm, hxInOld⟩)
  · left
    by_contra hxm
    apply hxR
    rw [hRerase]
    apply Finset.mem_erase.mpr
    refine ⟨hxm, ?_⟩
    rw [hw] at hxw
    exact hxw
  · right
    left
    have hmFirst : m = z := by
      by_contra hm
      have hzBlock : z ∈ consecutiveRanks z n := by
        apply mem_consecutiveRanks_iff_bounds.mpr
        constructor <;> omega
      have hzR : z ∈ R := by
        rw [hRerase]
        exact Finset.mem_erase.mpr ⟨Ne.symm hm, hzBlock⟩
      have hzW := bounds_of_mem_consecutiveRanks (hRw hzR)
      omega
    refine ⟨hmFirst, ?_⟩
    have hxBounds := bounds_of_mem_consecutiveRanks hxw
    by_contra hx
    have hxUpper : x ≤ z + n := by omega
    have hxInOld : x ∈ consecutiveRanks z n :=
      mem_consecutiveRanks_iff_bounds.mpr ⟨by omega, hxUpper⟩
    have hxm : x ≠ m := by omega
    exact hxR (by rw [hRerase]; exact Finset.mem_erase.mpr ⟨hxm, hxInOld⟩)

@[simp]
theorem cumulativeWeight_add_single {n : ℕ}
    (u : Fin n → ℤ) (i : Fin n) :
    cumulativeWeight (u + Pi.single i 1) = cumulativeWeight u + 1 := by
  simp [cumulativeWeight, Finset.sum_add_distrib]

/-- Every vertex of a Freudenthal path has a rank between zero and the
length of the transfer list. -/
theorem exists_rank_of_mem_freudenthalSequence {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n))
    {v : Fin n → ℤ} (hv : v ∈ freudenthalSequence u l) :
    ∃ r : ℕ, r ≤ l.length ∧
      cumulativeWeight v = cumulativeWeight u + r := by
  induction l generalizing u v with
  | nil =>
      simp only [freudenthalSequence, List.mem_singleton] at hv
      subst v
      exact ⟨0, by simp, by simp⟩
  | cons i l ih =>
      simp only [freudenthalSequence, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨r, hr, hweight⟩ := ih
          (u := u + Pi.single i 1) hv
        refine ⟨r + 1, by simpa using Nat.succ_le_succ hr, ?_⟩
        rw [hweight, cumulativeWeight_add_single]
        push_cast
        ring

/-- Cumulative weight is injective on a single Freudenthal path.  This does
not require the transfer list to be duplicate-free: weight strictly records
the number of performed steps. -/
theorem cumulativeWeight_injective_on_freudenthalSequence {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n)) :
    Set.InjOn cumulativeWeight {v | v ∈ freudenthalSequence u l} := by
  revert u
  induction l with
  | nil =>
      intro u x hx y hy _
      simp only [Set.mem_ofPred_eq, freudenthalSequence,
        List.mem_singleton] at hx hy
      simp [hx, hy]
  | cons i l ih =>
      intro u x hx y hy hweight
      simp only [Set.mem_ofPred_eq, freudenthalSequence,
        List.mem_cons] at hx hy
      rcases hx with hxu | hx <;> rcases hy with hyu | hy
      · exact hxu.trans hyu.symm
      · rw [hxu] at hweight
        obtain ⟨r, _, hr⟩ := exists_rank_of_mem_freudenthalSequence
          (u + Pi.single i 1) l hy
        rw [cumulativeWeight_add_single] at hr
        rw [hr] at hweight
        omega
      · rw [hyu] at hweight
        obtain ⟨r, _, hr⟩ := exists_rank_of_mem_freudenthalSequence
          (u + Pi.single i 1) l hx
        rw [cumulativeWeight_add_single] at hr
        rw [hr] at hweight
        omega
      · exact ih (u + Pi.single i 1) hx hy hweight

/-- Exact weight set of a Freudenthal simplex: `length l + 1` consecutive
integers beginning at the weight of its base vertex. -/
theorem image_cumulativeWeight_freudenthalSimplex {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n)) :
    (freudenthalSimplex u l).image cumulativeWeight =
      (Finset.range (l.length + 1)).image
        (fun r : ℕ ↦ cumulativeWeight u + r) := by
  induction l generalizing u with
  | nil => simp [freudenthalSimplex, freudenthalSequence]
  | cons i l ih =>
      rw [freudenthalSimplex]
      simp only [freudenthalSequence, List.toFinset_cons,
        Finset.image_insert]
      change insert (cumulativeWeight u)
          ((freudenthalSimplex (u + Pi.single i 1) l).image
            cumulativeWeight) = _
      rw [ih, cumulativeWeight_add_single]
      simp only [List.length_cons]
      ext z
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | ⟨r, hr, rfl⟩)
        · exact ⟨0, by omega, by simp⟩
        · refine ⟨r + 1, by omega, ?_⟩
          push_cast
          ring
      · rintro ⟨r, hr, hzr⟩
        cases r with
        | zero =>
            left
            simpa using hzr.symm
        | succ r =>
            right
            refine ⟨r, by omega, ?_⟩
            rw [← hzr]
            push_cast
            ring

/-- The base vertex is coordinatewise below every later vertex of a
Freudenthal path. -/
theorem freudenthalSequence_base_le_of_mem {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n))
    {v : Fin n → ℤ} (hv : v ∈ freudenthalSequence u l) :
    u ≤ v := by
  induction l generalizing u v with
  | nil =>
      simp only [freudenthalSequence, List.mem_singleton] at hv
      subst v
      exact le_rfl
  | cons i l ih =>
      simp only [freudenthalSequence, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact le_rfl
      · apply le_trans (b := u + Pi.single i 1)
        · intro q
          simp only [Pi.add_apply, Pi.single_apply]
          split <;> omega
        · exact ih (u + Pi.single i 1) hv

/-- Any two vertices on one Freudenthal path are comparable in the product
order on cumulative coordinates. -/
theorem comparable_of_mem_freudenthalSequence {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n))
    {x y : Fin n → ℤ}
    (hx : x ∈ freudenthalSequence u l)
    (hy : y ∈ freudenthalSequence u l) :
    x ≤ y ∨ y ≤ x := by
  induction l generalizing u x y with
  | nil =>
      simp only [freudenthalSequence, List.mem_singleton] at hx hy
      subst x
      subst y
      exact Or.inl le_rfl
  | cons i l ih =>
      simp only [freudenthalSequence, List.mem_cons] at hx hy
      rcases hx with hxu | hx <;> rcases hy with hyu | hy
      · rw [hxu, hyu]
        exact Or.inl le_rfl
      · rw [hxu]
        left
        apply le_trans (b := u + Pi.single i 1)
        · intro q
          simp only [Pi.add_apply, Pi.single_apply]
          split <;> omega
        · exact freudenthalSequence_base_le_of_mem _ _ hy
      · rw [hyu]
        right
        apply le_trans (b := u + Pi.single i 1)
        · intro q
          simp only [Pi.add_apply, Pi.single_apply]
          split <;> omega
        · exact freudenthalSequence_base_le_of_mem _ _ hx
      · exact ih (u + Pi.single i 1) hx hy

theorem cumulativeWeight_mono {n : ℕ} {u v : Fin n → ℤ}
    (huv : u ≤ v) : cumulativeWeight u ≤ cumulativeWeight v := by
  exact Finset.sum_le_sum fun i _ ↦ huv i

/-- For finite integer tuples, coordinatewise comparison plus equality of
coordinate sums forces equality. -/
theorem eq_of_le_of_cumulativeWeight_eq {n : ℕ}
    {u v : Fin n → ℤ} (huv : u ≤ v)
    (hweight : cumulativeWeight u = cumulativeWeight v) :
    u = v := by
  funext q
  apply le_antisymm (huv q)
  by_contra hnot
  have hstrict : u q < v q := lt_of_not_ge hnot
  have hsumlt : cumulativeWeight u < cumulativeWeight v := by
    rw [cumulativeWeight, cumulativeWeight]
    apply Finset.sum_lt_sum
    · intro i _
      exact huv i
    · exact ⟨q, Finset.mem_univ q, hstrict⟩
  exact (ne_of_lt hsumlt) hweight

/-- Coordinates on which an upper cumulative vector is strictly larger. -/
def positiveCoords {n : ℕ} (u v : Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ u i < v i

/-- The number of strictly increased coordinates is bounded by the total
increase in cumulative weight. -/
theorem card_positiveCoords_le {n d : ℕ} {u v : Fin n → ℤ}
    (huv : u ≤ v)
    (hweight : cumulativeWeight v = cumulativeWeight u + d) :
    (positiveCoords u v).card ≤ d := by
  have hcardInt : ((positiveCoords u v).card : ℤ) ≤ d := by
    calc
      ((positiveCoords u v).card : ℤ) =
          ∑ i ∈ positiveCoords u v, (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ positiveCoords u v, (v i - u i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hlt := (Finset.mem_filter.mp hi).2
        omega
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), (v i - u i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro i _ _
          exact sub_nonneg.mpr (huv i)
      _ = cumulativeWeight v - cumulativeWeight u := by
        simp [cumulativeWeight, Finset.sum_sub_distrib]
      _ = d := by rw [hweight]; ring
  exact_mod_cast hcardInt

/-- One coordinate difference is no larger than the total weight increase. -/
theorem coordinate_sub_le_weight_sub {n : ℕ} {u v : Fin n → ℤ}
    (huv : u ≤ v) (i : Fin n) :
    v i - u i ≤ cumulativeWeight v - cumulativeWeight u := by
  calc
    v i - u i = ∑ j ∈ ({i} : Finset (Fin n)), (v j - u j) := by simp
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)), (v j - u j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simp
      · intro j _ _
        exact sub_nonneg.mpr (huv j)
    _ = cumulativeWeight v - cumulativeWeight u := by
      simp [cumulativeWeight, Finset.sum_sub_distrib]

/-- A coordinatewise step of total weight one changes exactly one coordinate
by one. -/
theorem eq_add_single_of_le_of_weight_add_one {n : ℕ}
    {u v : Fin n → ℤ} (huv : u ≤ v)
    (hweight : cumulativeWeight v = cumulativeWeight u + 1)
    {i : Fin n} (hi : u i < v i) :
    v = u + Pi.single i 1 := by
  have hcard : (positiveCoords u v).card ≤ 1 :=
    card_positiveCoords_le huv hweight
  have hiMem : i ∈ positiveCoords u v := by
    simp [positiveCoords, hi]
  funext j
  by_cases hji : j = i
  · subst j
    rw [Pi.add_apply, Pi.single_eq_same]
    have hle := coordinate_sub_le_weight_sub huv i
    rw [hweight] at hle
    omega
  · have hjEq : v j = u j := by
      apply le_antisymm
      · by_contra hnot
        have hjlt : u j < v j := lt_of_not_ge hnot
        have hjMem : j ∈ positiveCoords u v := by
          simp [positiveCoords, hjlt]
        have hpair : ({i, j} : Finset (Fin n)) ⊆ positiveCoords u v := by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hiMem
          · exact hjMem
        have := Finset.card_le_card hpair
        have hij : i ≠ j := fun h ↦ hji h.symm
        have hpairCard : ({i, j} : Finset (Fin n)).card = 2 := by
          simp [hij]
        rw [hpairCard] at this
        omega
      · exact huv j
    rw [Pi.add_apply, Pi.single_apply, if_neg hji]
    simpa using hjEq

/-- The finite set of simplex points whose cumulative vector can fill one
rank between two comparable cumulative vectors. -/
noncomputable def betweenNextPoints (N n : ℕ)
    (u v : Fin n → ℤ) : Finset (Point N n) :=
  Finset.univ.filter fun a ↦
    u ≤ pointPrefix a ∧ pointPrefix a ≤ v ∧
      cumulativeWeight (pointPrefix a) = cumulativeWeight u + 1

/-- A total increase of one has at least one strictly increased coordinate. -/
theorem positiveCoords_nonempty_of_le_of_weight_add_one {n : ℕ}
    {u v : Fin n → ℤ} (huv : u ≤ v)
    (hweight : cumulativeWeight v = cumulativeWeight u + 1) :
    (positiveCoords u v).Nonempty := by
  by_contra hnot
  have hEq : u = v := by
    funext i
    apply le_antisymm (huv i)
    have hi : i ∉ positiveCoords u v := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hnot]
    simp [positiveCoords] at hi
    exact hi
  rw [hEq] at hweight
  omega

/-- A deterministic choice of the coordinate changed by a unit cumulative
step.  It returns `none` only when no coordinate increases. -/
noncomputable def firstPositiveIndex {n : ℕ}
    (u v : Fin n → ℤ) : Option (Fin n) :=
  if h : (positiveCoords u v).Nonempty then
    some ((positiveCoords u v).min' h)
  else none

theorem firstPositiveIndex_eq_some_of_nonempty {n : ℕ}
    {u v : Fin n → ℤ} (h : (positiveCoords u v).Nonempty) :
    ∃ i : Fin n, firstPositiveIndex u v = some i ∧
      i ∈ positiveCoords u v := by
  refine ⟨(positiveCoords u v).min' h, ?_,
    Finset.min'_mem _ _⟩
  simp [firstPositiveIndex, h]

theorem mem_positiveCoords_of_firstPositiveIndex_eq_some {n : ℕ}
    {u v : Fin n → ℤ} {i : Fin n}
    (h : firstPositiveIndex u v = some i) :
    i ∈ positiveCoords u v := by
  unfold firstPositiveIndex at h
  split at h
  next hpos =>
    have hEq : (positiveCoords u v).min' hpos = i :=
      Option.some.inj h
    rw [← hEq]
    exact Finset.min'_mem _ _
  next => simp at h

/-- At weight distance two there are at most two intermediate simplex
points of the next weight.  This is the local two-completion bound at an
interior missing rank. -/
theorem betweenNextPoints_card_le_two {N n : ℕ}
    {u v : Fin n → ℤ} (huv : u ≤ v)
    (hweight : cumulativeWeight v = cumulativeWeight u + 2) :
    (betweenNextPoints N n u v).card ≤ 2 := by
  let f : Point N n → Option (Fin n) := fun a ↦
    firstPositiveIndex u (pointPrefix a)
  let target : Finset (Option (Fin n)) :=
    (positiveCoords u v).image some
  have hmaps : Set.MapsTo f
      (betweenNextPoints N n u v : Set (Point N n)) target := by
    intro a ha
    have haData := (Finset.mem_filter.mp ha).2
    have hnonempty := positiveCoords_nonempty_of_le_of_weight_add_one
      haData.1 haData.2.2
    obtain ⟨i, hiEq, hiMem⟩ :=
      firstPositiveIndex_eq_some_of_nonempty hnonempty
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hiEq.symm⟩
    have hiLt : u i < pointPrefix a i :=
      (Finset.mem_filter.mp hiMem).2
    have hiLe : pointPrefix a i ≤ v i := haData.2.1 i
    simp [positiveCoords]
    exact lt_of_lt_of_le hiLt hiLe
  have hinj : Set.InjOn f
      (betweenNextPoints N n u v : Set (Point N n)) := by
    intro a ha b hb hab
    have haData := (Finset.mem_filter.mp ha).2
    have hbData := (Finset.mem_filter.mp hb).2
    have hnonemptyA := positiveCoords_nonempty_of_le_of_weight_add_one
      haData.1 haData.2.2
    obtain ⟨i, hiEq, hiMem⟩ :=
      firstPositiveIndex_eq_some_of_nonempty hnonemptyA
    have hiEqB : firstPositiveIndex u (pointPrefix b) = some i := by
      change f b = some i
      rw [← hiEq]
      exact hab.symm
    have hiMemB := mem_positiveCoords_of_firstPositiveIndex_eq_some hiEqB
    apply pointPrefix_injective
    rw [eq_add_single_of_le_of_weight_add_one haData.1 haData.2.2
      (Finset.mem_filter.mp hiMem).2]
    rw [eq_add_single_of_le_of_weight_add_one hbData.1 hbData.2.2
      (Finset.mem_filter.mp hiMemB).2]
  have hcardMap := Finset.card_le_card_of_injOn f hmaps hinj
  change (betweenNextPoints N n u v).card ≤ target.card at hcardMap
  calc
    (betweenNextPoints N n u v).card ≤ target.card := hcardMap
    _ = (positiveCoords u v).card := by
      change ((positiveCoords u v).image some).card =
        (positiveCoords u v).card
      rw [Finset.card_image_of_injective]
      exact Option.some_injective _
    _ ≤ 2 := card_positiveCoords_le huv hweight

/-- Along a duplicate-free Freudenthal path, each coordinate is either still
at its initial value or has increased exactly once.  This is the fact that
prevents an endpoint face from having several different unused directions. -/
theorem freudenthalSequence_coordinate_eq_or_eq_add_one {n : ℕ}
    (u : Fin n → ℤ) {l : List (Fin n)} (hl : l.Nodup)
    {v : Fin n → ℤ} (hv : v ∈ freudenthalSequence u l)
    (i : Fin n) : v i = u i ∨ v i = u i + 1 := by
  induction l generalizing u v with
  | nil =>
      simp only [freudenthalSequence, List.mem_singleton] at hv
      subst v
      exact Or.inl rfl
  | cons j l ih =>
      have hnodup := List.nodup_cons.mp hl
      simp only [freudenthalSequence, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact Or.inl rfl
      · by_cases hij : i = j
        · subst j
          right
          have hpreserve := freudenthalSequence_coordinate_eq_of_not_mem
            (u + Pi.single i 1) l hnodup.1 hv
          simpa [Pi.single_apply] using hpreserve
        · have hcases := ih (u := u + Pi.single j 1)
            hnodup.2 hv
          simpa [Pi.single_apply, hij] using hcases

/-- Comparable vertices of one duplicate-free Freudenthal path differ by
zero or one in every cumulative coordinate. -/
theorem coordinate_sub_eq_zero_or_one_of_mem_freudenthalSequence
    {n : ℕ} (u : Fin n → ℤ) {l : List (Fin n)} (hl : l.Nodup)
    {x y : Fin n → ℤ}
    (hx : x ∈ freudenthalSequence u l)
    (hy : y ∈ freudenthalSequence u l)
    (hxy : x ≤ y) (i : Fin n) :
    y i - x i = 0 ∨ y i - x i = 1 := by
  have hxyi : x i ≤ y i := hxy i
  rcases freudenthalSequence_coordinate_eq_or_eq_add_one
      u hl hx i with hxu | hxu <;>
    rcases freudenthalSequence_coordinate_eq_or_eq_add_one
      u hl hy i with hyu | hyu <;> omega

/-- On a duplicate-free Freudenthal path, the total rank distance between
two comparable vertices is exactly the number of changed coordinates. -/
theorem card_positiveCoords_eq_of_mem_freudenthalSequence
    {n d : ℕ} (u : Fin n → ℤ) {l : List (Fin n)} (hl : l.Nodup)
    {x y : Fin n → ℤ}
    (hx : x ∈ freudenthalSequence u l)
    (hy : y ∈ freudenthalSequence u l)
    (hxy : x ≤ y)
    (hweight : cumulativeWeight y = cumulativeWeight x + d) :
    (positiveCoords x y).card = d := by
  have hcardInt : ((positiveCoords x y).card : ℤ) = d := by
    calc
      ((positiveCoords x y).card : ℤ) =
          ∑ i ∈ positiveCoords x y, (1 : ℤ) := by simp
      _ = ∑ i : Fin n, if x i < y i then (1 : ℤ) else 0 := by
        simp [positiveCoords]
      _ = ∑ i : Fin n, (y i - x i) := by
        apply Finset.sum_congr rfl
        intro i _
        rcases coordinate_sub_eq_zero_or_one_of_mem_freudenthalSequence
            u hl hx hy hxy i with hi | hi <;>
          split <;> omega
      _ = cumulativeWeight y - cumulativeWeight x := by
        simp [cumulativeWeight, Finset.sum_sub_distrib]
      _ = d := by rw [hweight]; ring
  exact_mod_cast hcardInt

/-- In particular, the weight map is injective on the finite vertex set of
a Freudenthal simplex. -/
theorem cumulativeWeight_injective_on_freudenthalSimplex {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n)) :
    Set.InjOn cumulativeWeight (freudenthalSimplex u l : Set (Fin n → ℤ)) := by
  intro x hx y hy hxy
  apply cumulativeWeight_injective_on_freudenthalSequence u l
  · simpa [freudenthalSimplex] using hx
  · simpa [freudenthalSimplex] using hy
  · exact hxy

/-- On a Freudenthal simplex, intrinsic weight order agrees with the product
order. -/
theorem le_of_mem_freudenthalSimplex_of_weight_le {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n))
    {x y : Fin n → ℤ}
    (hx : x ∈ freudenthalSimplex u l)
    (hy : y ∈ freudenthalSimplex u l)
    (hweight : cumulativeWeight x ≤ cumulativeWeight y) :
    x ≤ y := by
  have hxSeq : x ∈ freudenthalSequence u l := by
    simpa [freudenthalSimplex] using hx
  have hySeq : y ∈ freudenthalSequence u l := by
    simpa [freudenthalSimplex] using hy
  rcases comparable_of_mem_freudenthalSequence u l hxSeq hySeq with
    hxy | hyx
  · exact hxy
  · have hrev := cumulativeWeight_mono hyx
    have heqWeight : cumulativeWeight x = cumulativeWeight y :=
      le_antisymm hweight hrev
    exact (eq_of_le_of_cumulativeWeight_eq hyx heqWeight.symm).symm.le

/-- A genuine `n`-dimensional Freudenthal facet has exactly the consecutive
cumulative weights determined by any of its cumulative presentations. -/
theorem IsFreudenthalTopSimplex.image_cumulativeWeight_pointPrefix
    {N n : ℕ} {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho) :
    ∃ u : Fin n → ℤ,
      (rho.image (fun a ↦ cumulativeWeight (pointPrefix a))) =
        consecutiveRanks (cumulativeWeight u) n := by
  obtain ⟨u, omega, hprefix⟩ :=
    (isFreudenthalTopSimplex_iff_cumulative rho).1 hrho
  refine ⟨u, ?_⟩
  calc
    rho.image (fun a ↦ cumulativeWeight (pointPrefix a)) =
        (rho.image pointPrefix).image cumulativeWeight := by
      ext z
      simp
    _ = (freudenthalSimplex u (permutationList omega)).image
        cumulativeWeight := by rw [hprefix]
    _ = consecutiveRanks (cumulativeWeight u) n := by
      simpa [consecutiveRanks] using image_cumulativeWeight_freudenthalSimplex
        u (permutationList omega)

/-- The cumulative-coordinate vertices of a genuine facet form a chain. -/
theorem IsFreudenthalTopSimplex.pointPrefix_comparable
    {N n : ℕ} {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho)
    {a b : Point N n} (ha : a ∈ rho) (hb : b ∈ rho) :
    pointPrefix a ≤ pointPrefix b ∨ pointPrefix b ≤ pointPrefix a := by
  obtain ⟨u, omega, hprefix⟩ :=
    (isFreudenthalTopSimplex_iff_cumulative rho).1 hrho
  have ha' : pointPrefix a ∈
      freudenthalSimplex u (permutationList omega) := by
    rw [← hprefix]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hb' : pointPrefix b ∈
      freudenthalSimplex u (permutationList omega) := by
    rw [← hprefix]
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  apply comparable_of_mem_freudenthalSequence u (permutationList omega)
  · simpa [freudenthalSimplex] using ha'
  · simpa [freudenthalSimplex] using hb'

/-- Cumulative weight is injective on the vertices of a genuine facet. -/
theorem IsFreudenthalTopSimplex.cumulativeWeight_pointPrefix_injective
    {N n : ℕ} {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho) :
    Set.InjOn (fun a ↦ cumulativeWeight (pointPrefix a))
      (rho : Set (Point N n)) := by
  obtain ⟨u, omega, hprefix⟩ :=
    (isFreudenthalTopSimplex_iff_cumulative rho).1 hrho
  intro a ha b hb hweight
  apply pointPrefix_injective
  apply cumulativeWeight_injective_on_freudenthalSimplex
    u (permutationList omega)
  · rw [← hprefix]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · rw [← hprefix]
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  · exact hweight

/-- Intrinsic rank order on a genuine facet agrees with product order in
cumulative coordinates. -/
theorem IsFreudenthalTopSimplex.pointPrefix_le_of_weight_le
    {N n : ℕ} {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho)
    {a b : Point N n} (ha : a ∈ rho) (hb : b ∈ rho)
    (hweight : cumulativeWeight (pointPrefix a) ≤
      cumulativeWeight (pointPrefix b)) :
    pointPrefix a ≤ pointPrefix b := by
  obtain ⟨u, omega, hprefix⟩ :=
    (isFreudenthalTopSimplex_iff_cumulative rho).1 hrho
  apply le_of_mem_freudenthalSimplex_of_weight_le
      u (permutationList omega)
  · rw [← hprefix]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · rw [← hprefix]
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  · exact hweight

/-- Comparable vertices of a genuine facet differ by at most one in every
cumulative coordinate. -/
theorem IsFreudenthalTopSimplex.coordinate_sub_eq_zero_or_one
    {N n : ℕ} {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho)
    {a b : Point N n} (ha : a ∈ rho) (hb : b ∈ rho)
    (hab : pointPrefix a ≤ pointPrefix b) (i : Fin n) :
    pointPrefix b i - pointPrefix a i = 0 ∨
      pointPrefix b i - pointPrefix a i = 1 := by
  obtain ⟨u, omega, hprefix⟩ :=
    (isFreudenthalTopSimplex_iff_cumulative rho).1 hrho
  apply coordinate_sub_eq_zero_or_one_of_mem_freudenthalSequence
      u (nodup_permutationList omega)
  · simpa [freudenthalSimplex] using
      (show pointPrefix a ∈
        freudenthalSimplex u (permutationList omega) by
        rw [← hprefix]
        exact Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  · simpa [freudenthalSimplex] using
      (show pointPrefix b ∈
        freudenthalSimplex u (permutationList omega) by
        rw [← hprefix]
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  · exact hab

/-- Exact changed-coordinate count for two ranked vertices of a genuine
facet. -/
theorem IsFreudenthalTopSimplex.card_positiveCoords_eq
    {N n d : ℕ} {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho)
    {a b : Point N n} (ha : a ∈ rho) (hb : b ∈ rho)
    (hab : pointPrefix a ≤ pointPrefix b)
    (hweight : cumulativeWeight (pointPrefix b) =
      cumulativeWeight (pointPrefix a) + d) :
    (positiveCoords (pointPrefix a) (pointPrefix b)).card = d := by
  obtain ⟨u, omega, hprefix⟩ :=
    (isFreudenthalTopSimplex_iff_cumulative rho).1 hrho
  apply card_positiveCoords_eq_of_mem_freudenthalSequence
      u (nodup_permutationList omega)
  · simpa [freudenthalSimplex] using
      (show pointPrefix a ∈
        freudenthalSimplex u (permutationList omega) by
        rw [← hprefix]
        exact Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  · simpa [freudenthalSimplex] using
      (show pointPrefix b ∈
        freudenthalSimplex u (permutationList omega) by
        rw [← hprefix]
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  · exact hab
  · exact hweight

/-- If two genuine facets contain the same codimension-one face, then the
initial weights in any two cumulative presentations differ by at most one.
This is the first half of the concrete coface classification. -/
theorem baseWeights_close_of_common_codimFace
    {N n : ℕ} (hn : 0 < n)
    {rho sigma tau : Finset (Point N n)}
    (hrho : rho.card = n)
    (hsigma : IsFreudenthalTopSimplex sigma)
    (_htau : IsFreudenthalTopSimplex tau)
    (hrhoSigma : rho ⊆ sigma) (hrhoTau : rho ⊆ tau)
    {z w : ℤ}
    (hz : sigma.image (fun a ↦ cumulativeWeight (pointPrefix a)) =
      consecutiveRanks z n)
    (hw : tau.image (fun a ↦ cumulativeWeight (pointPrefix a)) =
      consecutiveRanks w n) :
    z ≤ w + 1 ∧ w ≤ z + 1 := by
  let R : Finset ℤ :=
    rho.image (fun a ↦ cumulativeWeight (pointPrefix a))
  have hcardR : R.card = n := by
    change (rho.image
      (fun a ↦ cumulativeWeight (pointPrefix a))).card = n
    rw [Finset.card_image_of_injOn]
    · exact hrho
    · intro a ha b hb hab
      exact hsigma.cumulativeWeight_pointPrefix_injective
        (hrhoSigma ha) (hrhoSigma hb) hab
  have hRz : R ⊆ consecutiveRanks z n := by
    rw [← hz]
    exact Finset.image_mono _ hrhoSigma
  have hRw : R ⊆ consecutiveRanks w n := by
    rw [← hw]
    exact Finset.image_mono _ hrhoTau
  exact consecutiveRanks_bases_close hn hcardR hRz hRw

/-- Removing a codimension-one face from a genuine facet leaves exactly one
vertex. -/
theorem card_sdiff_codimFace_of_topSimplex
    {N n : ℕ} {rho tau : Finset (Point N n)}
    (hrho : rho.card = n) (htau : IsFreudenthalTopSimplex tau)
    (hsub : rho ⊆ tau) :
    (tau \ rho).card = 1 := by
  rw [Finset.card_sdiff_of_subset hsub, htau.card, hrho]
  omega

/-- A facet containing `rho` is determined by its singleton difference from
`rho`.  This elementary injection is kept explicit because it is the bridge
from local point classifications to the `FacetChain.Nonbranching` cardinal
statement. -/
theorem sdiff_injective_on_cofacets
    {N n : ℕ} {rho : Finset (Point N n)} :
    Set.InjOn (fun tau : Finset (Point N n) ↦ tau \ rho)
      ((freudenthalFacets N n).filter (fun tau ↦ rho ⊆ tau) :
        Set (Finset (Point N n))) := by
  intro tau htau sigma hsigma heq
  have htauSub := (Finset.mem_filter.mp htau).2
  have hsigmaSub := (Finset.mem_filter.mp hsigma).2
  calc
    tau = (tau \ rho) ∪ rho :=
      (Finset.sdiff_union_of_subset htauSub).symm
    _ = (sigma \ rho) ∪ rho := congrArg (fun s ↦ s ∪ rho) heq
    _ = sigma := Finset.sdiff_union_of_subset hsigmaSub

/-- If the common chain from `x` to `y` leaves exactly one cumulative
coordinate unused, a one-rank predecessor of `x` in any containing
Freudenthal facet is unique. -/
theorem lower_completion_point_unique
    {N n : ℕ} {rho tau sigma : Finset (Point N n)}
    (htau : IsFreudenthalTopSimplex tau)
    (hsigma : IsFreudenthalTopSimplex sigma)
    (hrhoTau : rho ⊆ tau) (hrhoSigma : rho ⊆ sigma)
    {x y a b : Point N n} (hxRho : x ∈ rho) (hyRho : y ∈ rho)
    (haTau : a ∈ tau) (hbSigma : b ∈ sigma)
    (hxy : pointPrefix x ≤ pointPrefix y)
    (haWeight : cumulativeWeight (pointPrefix x) =
      cumulativeWeight (pointPrefix a) + 1)
    (hbWeight : cumulativeWeight (pointPrefix x) =
      cumulativeWeight (pointPrefix b) + 1)
    (hunused :
      ((Finset.univ : Finset (Fin n)) \
        positiveCoords (pointPrefix x) (pointPrefix y)).card = 1) :
    a = b := by
  have haX : pointPrefix a ≤ pointPrefix x :=
    htau.pointPrefix_le_of_weight_le haTau (hrhoTau hxRho) (by omega)
  have hbX : pointPrefix b ≤ pointPrefix x :=
    hsigma.pointPrefix_le_of_weight_le hbSigma (hrhoSigma hxRho) (by omega)
  have haPos := positiveCoords_nonempty_of_le_of_weight_add_one haX haWeight
  have hbPos := positiveCoords_nonempty_of_le_of_weight_add_one hbX hbWeight
  obtain ⟨i, hi⟩ := haPos
  obtain ⟨j, hj⟩ := hbPos
  have hxA := eq_add_single_of_le_of_weight_add_one haX haWeight
    (Finset.mem_filter.mp hi).2
  have hxB := eq_add_single_of_le_of_weight_add_one hbX hbWeight
    (Finset.mem_filter.mp hj).2
  have hiUnused : i ∈
      (Finset.univ : Finset (Fin n)) \
        positiveCoords (pointPrefix x) (pointPrefix y) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hiUsed
    have hiLt := (Finset.mem_filter.mp hiUsed).2
    have haY : pointPrefix a ≤ pointPrefix y := haX.trans hxy
    have hiStep := htau.coordinate_sub_eq_zero_or_one
      haTau (hrhoTau hyRho) haY i
    have hxi : pointPrefix x i = pointPrefix a i + 1 := by
      rw [hxA]
      simp
    rcases hiStep with hiStep | hiStep <;> omega
  have hjUnused : j ∈
      (Finset.univ : Finset (Fin n)) \
        positiveCoords (pointPrefix x) (pointPrefix y) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hjUsed
    have hjLt := (Finset.mem_filter.mp hjUsed).2
    have hbY : pointPrefix b ≤ pointPrefix y := hbX.trans hxy
    have hjStep := hsigma.coordinate_sub_eq_zero_or_one
      hbSigma (hrhoSigma hyRho) hbY j
    have hxj : pointPrefix x j = pointPrefix b j + 1 := by
      rw [hxB]
      simp
    rcases hjStep with hjStep | hjStep <;> omega
  have hij : i = j := by
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hunused
    rw [hq] at hiUnused hjUnused
    simp only [Finset.mem_singleton] at hiUnused hjUnused
    exact hiUnused.trans hjUnused.symm
  apply pointPrefix_injective
  have hadd : pointPrefix a + Pi.single i 1 =
      pointPrefix b + Pi.single i 1 := by
    rw [← hxA, hij, ← hxB]
  exact add_right_cancel hadd

/-- The analogous uniqueness statement for a one-rank successor of `y`. -/
theorem upper_completion_point_unique
    {N n : ℕ} {rho tau sigma : Finset (Point N n)}
    (htau : IsFreudenthalTopSimplex tau)
    (hsigma : IsFreudenthalTopSimplex sigma)
    (hrhoTau : rho ⊆ tau) (hrhoSigma : rho ⊆ sigma)
    {x y a b : Point N n} (hxRho : x ∈ rho) (hyRho : y ∈ rho)
    (haTau : a ∈ tau) (hbSigma : b ∈ sigma)
    (hxy : pointPrefix x ≤ pointPrefix y)
    (haWeight : cumulativeWeight (pointPrefix a) =
      cumulativeWeight (pointPrefix y) + 1)
    (hbWeight : cumulativeWeight (pointPrefix b) =
      cumulativeWeight (pointPrefix y) + 1)
    (hunused :
      ((Finset.univ : Finset (Fin n)) \
        positiveCoords (pointPrefix x) (pointPrefix y)).card = 1) :
    a = b := by
  have hYa : pointPrefix y ≤ pointPrefix a :=
    htau.pointPrefix_le_of_weight_le (hrhoTau hyRho) haTau (by omega)
  have hYb : pointPrefix y ≤ pointPrefix b :=
    hsigma.pointPrefix_le_of_weight_le (hrhoSigma hyRho) hbSigma (by omega)
  have haPos := positiveCoords_nonempty_of_le_of_weight_add_one hYa haWeight
  have hbPos := positiveCoords_nonempty_of_le_of_weight_add_one hYb hbWeight
  obtain ⟨i, hi⟩ := haPos
  obtain ⟨j, hj⟩ := hbPos
  have haY := eq_add_single_of_le_of_weight_add_one hYa haWeight
    (Finset.mem_filter.mp hi).2
  have hbY := eq_add_single_of_le_of_weight_add_one hYb hbWeight
    (Finset.mem_filter.mp hj).2
  have hiUnused : i ∈
      (Finset.univ : Finset (Fin n)) \
        positiveCoords (pointPrefix x) (pointPrefix y) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hiUsed
    have hiLt := (Finset.mem_filter.mp hiUsed).2
    have hXa : pointPrefix x ≤ pointPrefix a := hxy.trans hYa
    have hiStep := htau.coordinate_sub_eq_zero_or_one
      (hrhoTau hxRho) haTau hXa i
    have hai : pointPrefix a i = pointPrefix y i + 1 := by
      rw [haY]
      simp
    rcases hiStep with hiStep | hiStep <;> omega
  have hjUnused : j ∈
      (Finset.univ : Finset (Fin n)) \
        positiveCoords (pointPrefix x) (pointPrefix y) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hjUsed
    have hjLt := (Finset.mem_filter.mp hjUsed).2
    have hXb : pointPrefix x ≤ pointPrefix b := hxy.trans hYb
    have hjStep := hsigma.coordinate_sub_eq_zero_or_one
      (hrhoSigma hxRho) hbSigma hXb j
    have hbj : pointPrefix b j = pointPrefix y j + 1 := by
      rw [hbY]
      simp
    rcases hjStep with hjStep | hjStep <;> omega
  have hij : i = j := by
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hunused
    rw [hq] at hiUnused hjUnused
    simp only [Finset.mem_singleton] at hiUnused hjUnused
    exact hiUnused.trans hjUnused.symm
  apply pointPrefix_injective
  rw [haY, hbY, hij]

/-- Nonbranching at the first endpoint rank.  The common face uses `n-1`
distinct cumulative directions, so its unique unused direction determines at
most one predecessor and at most one successor cofacet. -/
theorem cofacets_card_le_two_of_first_erased_rank
    {N n : ℕ} (hn : 0 < n)
    {rho baseFacet : Finset (Point N n)}
    (hrho : rho.card = n)
    (hbase : IsFreudenthalTopSimplex baseFacet)
    (hrhoBase : rho ⊆ baseFacet)
    {z : ℤ}
    (hRerase :
      rho.image (fun a ↦ cumulativeWeight (pointPrefix a)) =
        (consecutiveRanks z n).erase z) :
    ((freudenthalFacets N n).filter (fun tau ↦ rho ⊆ tau)).card ≤ 2 := by
  let weight : Point N n → ℤ :=
    fun a ↦ cumulativeWeight (pointPrefix a)
  change rho.image weight = (consecutiveRanks z n).erase z at hRerase
  have hcardR : (rho.image weight).card = n := by
    rw [Finset.card_image_of_injOn]
    · exact hrho
    · intro a ha b hb hab
      exact hbase.cumulativeWeight_pointPrefix_injective
        (hrhoBase ha) (hrhoBase hb) hab
  have hxRank : z + 1 ∈ rho.image weight := by
    rw [hRerase]
    apply Finset.mem_erase.mpr
    refine ⟨by omega, mem_consecutiveRanks_iff_bounds.mpr ?_⟩
    constructor <;> omega
  have hyRank : z + n ∈ rho.image weight := by
    rw [hRerase]
    apply Finset.mem_erase.mpr
    refine ⟨by omega, mem_consecutiveRanks_iff_bounds.mpr ?_⟩
    constructor <;> omega
  obtain ⟨x, hxRho, hxWeight⟩ := Finset.mem_image.mp hxRank
  obtain ⟨y, hyRho, hyWeight⟩ := Finset.mem_image.mp hyRank
  have hxy : pointPrefix x ≤ pointPrefix y :=
    hbase.pointPrefix_le_of_weight_le (hrhoBase hxRho)
      (hrhoBase hyRho) (by change weight x ≤ weight y; omega)
  have hxyWeight : cumulativeWeight (pointPrefix y) =
      cumulativeWeight (pointPrefix x) + (n - 1 : ℕ) := by
    change weight y = weight x + (n - 1 : ℕ)
    omega
  have husedCard :
      (positiveCoords (pointPrefix x) (pointPrefix y)).card = n - 1 :=
    hbase.card_positiveCoords_eq (hrhoBase hxRho) (hrhoBase hyRho)
      hxy hxyWeight
  have hunused :
      ((Finset.univ : Finset (Fin n)) \
        positiveCoords (pointPrefix x) (pointPrefix y)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, husedCard]
    omega
  let C := (freudenthalFacets N n).filter (fun tau ↦ rho ⊆ tau)
  let lower := C.filter fun tau ↦ z ∈ tau.image weight
  let upper := C.filter fun tau ↦ z + n + 1 ∈ tau.image weight
  have hpartition : C ⊆ lower ∪ upper := by
    intro tau htauC
    have htauData := Finset.mem_filter.mp htauC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hdiffCard := card_sdiff_codimFace_of_topSimplex
      hrho htauTop htauData.2
    obtain ⟨a, haDiffEq⟩ := Finset.card_eq_one.mp hdiffCard
    have haDiff : a ∈ tau \ rho := by rw [haDiffEq]; simp
    have haTau := (Finset.mem_sdiff.mp haDiff).1
    have haNotRho := (Finset.mem_sdiff.mp haDiff).2
    obtain ⟨w, hwRanks⟩ := htauTop.image_cumulativeWeight_pointPrefix
    have hRw : rho.image weight ⊆
        consecutiveRanks (cumulativeWeight w) n := by
      rw [← hwRanks]
      exact Finset.image_mono _ htauData.2
    have haW : weight a ∈
        consecutiveRanks (cumulativeWeight w) n := by
      rw [← hwRanks]
      exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
    have haNotImage : weight a ∉ rho.image weight := by
      intro haImage
      obtain ⟨b, hbRho, hbWeight⟩ := Finset.mem_image.mp haImage
      have hab : a = b := htauTop.cumulativeWeight_pointPrefix_injective
        haTau (htauData.2 hbRho) hbWeight.symm
      exact haNotRho (hab ▸ hbRho)
    have hzBlock : z ∈ consecutiveRanks z n :=
      mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)
    have haCases := completion_rank_cases hn hcardR hzBlock hRerase
      hRw haW haNotImage
    rcases haCases with haLower | haUpper | haImpossible
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨htauC, ?_⟩
      rw [← haLower]
      exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨htauC, ?_⟩
      rw [← haUpper.2]
      exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
    · omega
  have hlower : lower.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro tau sigma htauLower hsigmaLower
    have htauLowerData := Finset.mem_filter.mp htauLower
    have hsigmaLowerData := Finset.mem_filter.mp hsigmaLower
    have htauC := htauLowerData.1
    have hsigmaC := hsigmaLowerData.1
    have htauData := Finset.mem_filter.mp htauC
    have hsigmaData := Finset.mem_filter.mp hsigmaC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hsigmaTop := (mem_freudenthalFacets_iff sigma).1 hsigmaData.1
    obtain ⟨a, haTau, haWeight⟩ :=
      Finset.mem_image.mp htauLowerData.2
    obtain ⟨b, hbSigma, hbWeight⟩ :=
      Finset.mem_image.mp hsigmaLowerData.2
    have haNotRho : a ∉ rho := by
      intro haRho
      have haImage : weight a ∈ rho.image weight :=
        Finset.mem_image.mpr ⟨a, haRho, rfl⟩
      rw [hRerase] at haImage
      simp [haWeight] at haImage
    have hbNotRho : b ∉ rho := by
      intro hbRho
      have hbImage : weight b ∈ rho.image weight :=
        Finset.mem_image.mpr ⟨b, hbRho, rfl⟩
      rw [hRerase] at hbImage
      simp [hbWeight] at hbImage
    have hdiffTau : tau \ rho = {a} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      have haDiff : a ∈ tau \ rho :=
        Finset.mem_sdiff.mpr ⟨haTau, haNotRho⟩
      refine ⟨haDiff, ?_⟩
      intro q hq
      have hcard := card_sdiff_codimFace_of_topSimplex
        hrho htauTop htauData.2
      exact Finset.card_le_one_iff.mp (by omega) hq haDiff
    have hdiffSigma : sigma \ rho = {b} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      have hbDiff : b ∈ sigma \ rho :=
        Finset.mem_sdiff.mpr ⟨hbSigma, hbNotRho⟩
      refine ⟨hbDiff, ?_⟩
      intro q hq
      have hcard := card_sdiff_codimFace_of_topSimplex
        hrho hsigmaTop hsigmaData.2
      exact Finset.card_le_one_iff.mp (by omega) hq hbDiff
    have hab : a = b := lower_completion_point_unique
      htauTop hsigmaTop htauData.2 hsigmaData.2 hxRho hyRho
      haTau hbSigma hxy (by change weight x = weight a + 1; omega)
      (by change weight x = weight b + 1; omega) hunused
    exact sdiff_injective_on_cofacets htauC hsigmaC (by
      change tau \ rho = sigma \ rho
      rw [hdiffTau, hdiffSigma, hab])
  have hupper : upper.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro tau sigma htauUpper hsigmaUpper
    have htauUpperData := Finset.mem_filter.mp htauUpper
    have hsigmaUpperData := Finset.mem_filter.mp hsigmaUpper
    have htauC := htauUpperData.1
    have hsigmaC := hsigmaUpperData.1
    have htauData := Finset.mem_filter.mp htauC
    have hsigmaData := Finset.mem_filter.mp hsigmaC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hsigmaTop := (mem_freudenthalFacets_iff sigma).1 hsigmaData.1
    obtain ⟨a, haTau, haWeight⟩ :=
      Finset.mem_image.mp htauUpperData.2
    obtain ⟨b, hbSigma, hbWeight⟩ :=
      Finset.mem_image.mp hsigmaUpperData.2
    have haNotRho : a ∉ rho := by
      intro haRho
      have haImage : weight a ∈ rho.image weight :=
        Finset.mem_image.mpr ⟨a, haRho, rfl⟩
      rw [hRerase] at haImage
      have haBounds := bounds_of_mem_consecutiveRanks
        (Finset.mem_erase.mp haImage).2
      omega
    have hbNotRho : b ∉ rho := by
      intro hbRho
      have hbImage : weight b ∈ rho.image weight :=
        Finset.mem_image.mpr ⟨b, hbRho, rfl⟩
      rw [hRerase] at hbImage
      have hbBounds := bounds_of_mem_consecutiveRanks
        (Finset.mem_erase.mp hbImage).2
      omega
    have hdiffTau : tau \ rho = {a} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      have haDiff : a ∈ tau \ rho :=
        Finset.mem_sdiff.mpr ⟨haTau, haNotRho⟩
      refine ⟨haDiff, ?_⟩
      intro q hq
      have hcard := card_sdiff_codimFace_of_topSimplex
        hrho htauTop htauData.2
      exact Finset.card_le_one_iff.mp (by omega) hq haDiff
    have hdiffSigma : sigma \ rho = {b} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      have hbDiff : b ∈ sigma \ rho :=
        Finset.mem_sdiff.mpr ⟨hbSigma, hbNotRho⟩
      refine ⟨hbDiff, ?_⟩
      intro q hq
      have hcard := card_sdiff_codimFace_of_topSimplex
        hrho hsigmaTop hsigmaData.2
      exact Finset.card_le_one_iff.mp (by omega) hq hbDiff
    have hab : a = b := upper_completion_point_unique
      htauTop hsigmaTop htauData.2 hsigmaData.2 hxRho hyRho
      haTau hbSigma hxy (by change weight a = weight y + 1; omega)
      (by change weight b = weight y + 1; omega) hunused
    exact sdiff_injective_on_cofacets htauC hsigmaC (by
      change tau \ rho = sigma \ rho
      rw [hdiffTau, hdiffSigma, hab])
  have hCunion := Finset.card_le_card hpartition
  have hunion := Finset.card_union_le lower upper
  change C.card ≤ 2
  omega

/-- Nonbranching at the last endpoint rank.  This is not obtained by an
unproved symmetry of the bounded simplex: the predecessor and successor
classes are checked directly against the same unique unused cumulative
direction. -/
theorem cofacets_card_le_two_of_last_erased_rank
    {N n : ℕ} (hn : 0 < n)
    {rho baseFacet : Finset (Point N n)}
    (hrho : rho.card = n)
    (hbase : IsFreudenthalTopSimplex baseFacet)
    (hrhoBase : rho ⊆ baseFacet)
    {z : ℤ}
    (hRerase :
      rho.image (fun a ↦ cumulativeWeight (pointPrefix a)) =
        (consecutiveRanks z n).erase (z + n)) :
    ((freudenthalFacets N n).filter (fun tau ↦ rho ⊆ tau)).card ≤ 2 := by
  let weight : Point N n → ℤ :=
    fun a ↦ cumulativeWeight (pointPrefix a)
  change rho.image weight =
    (consecutiveRanks z n).erase (z + n) at hRerase
  have hcardR : (rho.image weight).card = n := by
    rw [Finset.card_image_of_injOn]
    · exact hrho
    · intro a ha b hb hab
      exact hbase.cumulativeWeight_pointPrefix_injective
        (hrhoBase ha) (hrhoBase hb) hab
  have hxRank : z ∈ rho.image weight := by
    rw [hRerase]
    apply Finset.mem_erase.mpr
    refine ⟨by omega, mem_consecutiveRanks_iff_bounds.mpr ?_⟩
    constructor <;> omega
  have hyRank : z + n - 1 ∈ rho.image weight := by
    rw [hRerase]
    apply Finset.mem_erase.mpr
    refine ⟨by omega, mem_consecutiveRanks_iff_bounds.mpr ?_⟩
    constructor <;> omega
  obtain ⟨x, hxRho, hxWeight⟩ := Finset.mem_image.mp hxRank
  obtain ⟨y, hyRho, hyWeight⟩ := Finset.mem_image.mp hyRank
  have hxy : pointPrefix x ≤ pointPrefix y :=
    hbase.pointPrefix_le_of_weight_le (hrhoBase hxRho)
      (hrhoBase hyRho) (by change weight x ≤ weight y; omega)
  have hxyWeight : cumulativeWeight (pointPrefix y) =
      cumulativeWeight (pointPrefix x) + (n - 1 : ℕ) := by
    change weight y = weight x + (n - 1 : ℕ)
    omega
  have husedCard :
      (positiveCoords (pointPrefix x) (pointPrefix y)).card = n - 1 :=
    hbase.card_positiveCoords_eq (hrhoBase hxRho) (hrhoBase hyRho)
      hxy hxyWeight
  have hunused :
      ((Finset.univ : Finset (Fin n)) \
        positiveCoords (pointPrefix x) (pointPrefix y)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, husedCard]
    omega
  let C := (freudenthalFacets N n).filter (fun tau ↦ rho ⊆ tau)
  let lower := C.filter fun tau ↦ z - 1 ∈ tau.image weight
  let upper := C.filter fun tau ↦ z + n ∈ tau.image weight
  have hpartition : C ⊆ lower ∪ upper := by
    intro tau htauC
    have htauData := Finset.mem_filter.mp htauC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hdiffCard := card_sdiff_codimFace_of_topSimplex
      hrho htauTop htauData.2
    obtain ⟨a, haDiffEq⟩ := Finset.card_eq_one.mp hdiffCard
    have haDiff : a ∈ tau \ rho := by rw [haDiffEq]; simp
    have haTau := (Finset.mem_sdiff.mp haDiff).1
    have haNotRho := (Finset.mem_sdiff.mp haDiff).2
    obtain ⟨w, hwRanks⟩ := htauTop.image_cumulativeWeight_pointPrefix
    have hRw : rho.image weight ⊆
        consecutiveRanks (cumulativeWeight w) n := by
      rw [← hwRanks]
      exact Finset.image_mono _ htauData.2
    have haW : weight a ∈
        consecutiveRanks (cumulativeWeight w) n := by
      rw [← hwRanks]
      exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
    have haNotImage : weight a ∉ rho.image weight := by
      intro haImage
      obtain ⟨b, hbRho, hbWeight⟩ := Finset.mem_image.mp haImage
      have hab : a = b := htauTop.cumulativeWeight_pointPrefix_injective
        haTau (htauData.2 hbRho) hbWeight.symm
      exact haNotRho (hab ▸ hbRho)
    have hmBlock : z + n ∈ consecutiveRanks z n :=
      mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)
    have haCases := completion_rank_cases hn hcardR hmBlock hRerase
      hRw haW haNotImage
    rcases haCases with haUpper | haImpossible | haLower
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨htauC, ?_⟩
      rw [← haUpper]
      exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
    · omega
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨htauC, ?_⟩
      rw [← haLower.2]
      exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
  have hlower : lower.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro tau sigma htauLower hsigmaLower
    have htauLowerData := Finset.mem_filter.mp htauLower
    have hsigmaLowerData := Finset.mem_filter.mp hsigmaLower
    have htauC := htauLowerData.1
    have hsigmaC := hsigmaLowerData.1
    have htauData := Finset.mem_filter.mp htauC
    have hsigmaData := Finset.mem_filter.mp hsigmaC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hsigmaTop := (mem_freudenthalFacets_iff sigma).1 hsigmaData.1
    obtain ⟨a, haTau, haWeight⟩ :=
      Finset.mem_image.mp htauLowerData.2
    obtain ⟨b, hbSigma, hbWeight⟩ :=
      Finset.mem_image.mp hsigmaLowerData.2
    have haNotRho : a ∉ rho := by
      intro haRho
      have haImage : weight a ∈ rho.image weight :=
        Finset.mem_image.mpr ⟨a, haRho, rfl⟩
      rw [hRerase] at haImage
      have haBounds := bounds_of_mem_consecutiveRanks
        (Finset.mem_erase.mp haImage).2
      omega
    have hbNotRho : b ∉ rho := by
      intro hbRho
      have hbImage : weight b ∈ rho.image weight :=
        Finset.mem_image.mpr ⟨b, hbRho, rfl⟩
      rw [hRerase] at hbImage
      have hbBounds := bounds_of_mem_consecutiveRanks
        (Finset.mem_erase.mp hbImage).2
      omega
    have hdiffTau : tau \ rho = {a} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      have haDiff : a ∈ tau \ rho :=
        Finset.mem_sdiff.mpr ⟨haTau, haNotRho⟩
      refine ⟨haDiff, ?_⟩
      intro q hq
      have hcard := card_sdiff_codimFace_of_topSimplex
        hrho htauTop htauData.2
      exact Finset.card_le_one_iff.mp (by omega) hq haDiff
    have hdiffSigma : sigma \ rho = {b} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      have hbDiff : b ∈ sigma \ rho :=
        Finset.mem_sdiff.mpr ⟨hbSigma, hbNotRho⟩
      refine ⟨hbDiff, ?_⟩
      intro q hq
      have hcard := card_sdiff_codimFace_of_topSimplex
        hrho hsigmaTop hsigmaData.2
      exact Finset.card_le_one_iff.mp (by omega) hq hbDiff
    have hab : a = b := lower_completion_point_unique
      htauTop hsigmaTop htauData.2 hsigmaData.2 hxRho hyRho
      haTau hbSigma hxy (by change weight x = weight a + 1; omega)
      (by change weight x = weight b + 1; omega) hunused
    exact sdiff_injective_on_cofacets htauC hsigmaC (by
      change tau \ rho = sigma \ rho
      rw [hdiffTau, hdiffSigma, hab])
  have hupper : upper.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro tau sigma htauUpper hsigmaUpper
    have htauUpperData := Finset.mem_filter.mp htauUpper
    have hsigmaUpperData := Finset.mem_filter.mp hsigmaUpper
    have htauC := htauUpperData.1
    have hsigmaC := hsigmaUpperData.1
    have htauData := Finset.mem_filter.mp htauC
    have hsigmaData := Finset.mem_filter.mp hsigmaC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hsigmaTop := (mem_freudenthalFacets_iff sigma).1 hsigmaData.1
    obtain ⟨a, haTau, haWeight⟩ :=
      Finset.mem_image.mp htauUpperData.2
    obtain ⟨b, hbSigma, hbWeight⟩ :=
      Finset.mem_image.mp hsigmaUpperData.2
    have haNotRho : a ∉ rho := by
      intro haRho
      have haImage : weight a ∈ rho.image weight :=
        Finset.mem_image.mpr ⟨a, haRho, rfl⟩
      rw [hRerase] at haImage
      simp [haWeight] at haImage
    have hbNotRho : b ∉ rho := by
      intro hbRho
      have hbImage : weight b ∈ rho.image weight :=
        Finset.mem_image.mpr ⟨b, hbRho, rfl⟩
      rw [hRerase] at hbImage
      simp [hbWeight] at hbImage
    have hdiffTau : tau \ rho = {a} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      have haDiff : a ∈ tau \ rho :=
        Finset.mem_sdiff.mpr ⟨haTau, haNotRho⟩
      refine ⟨haDiff, ?_⟩
      intro q hq
      have hcard := card_sdiff_codimFace_of_topSimplex
        hrho htauTop htauData.2
      exact Finset.card_le_one_iff.mp (by omega) hq haDiff
    have hdiffSigma : sigma \ rho = {b} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      have hbDiff : b ∈ sigma \ rho :=
        Finset.mem_sdiff.mpr ⟨hbSigma, hbNotRho⟩
      refine ⟨hbDiff, ?_⟩
      intro q hq
      have hcard := card_sdiff_codimFace_of_topSimplex
        hrho hsigmaTop hsigmaData.2
      exact Finset.card_le_one_iff.mp (by omega) hq hbDiff
    have hab : a = b := upper_completion_point_unique
      htauTop hsigmaTop htauData.2 hsigmaData.2 hxRho hyRho
      haTau hbSigma hxy (by change weight a = weight y + 1; omega)
      (by change weight b = weight y + 1; omega) hunused
    exact sdiff_injective_on_cofacets htauC hsigmaC (by
      change tau \ rho = sigma \ rho
      rw [hdiffTau, hdiffSigma, hab])
  have hCunion := Finset.card_le_card hpartition
  have hunion := Finset.card_union_le lower upper
  change C.card ≤ 2
  omega

/-- Interior codimension-one faces already satisfy the full nonbranching
bound.  If the erased intrinsic rank lies strictly inside the rank block,
every cofacet must insert a point between the two neighboring common
vertices, and `betweenNextPoints_card_le_two` gives the sharp bound. -/
theorem cofacets_card_le_two_of_interior_erased_rank
    {N n : ℕ} (hn : 0 < n)
    {rho sigma : Finset (Point N n)}
    (hrho : rho.card = n)
    (hsigma : IsFreudenthalTopSimplex sigma)
    (hrhoSigma : rho ⊆ sigma)
    {z m : ℤ}
    (hRerase :
      rho.image (fun a ↦ cumulativeWeight (pointPrefix a)) =
        (consecutiveRanks z n).erase m)
    (hmLower : z < m) (hmUpper : m < z + n) :
    ((freudenthalFacets N n).filter (fun tau ↦ rho ⊆ tau)).card ≤ 2 := by
  let weight : Point N n → ℤ :=
    fun a ↦ cumulativeWeight (pointPrefix a)
  have hcardR : (rho.image weight).card = n := by
    rw [Finset.card_image_of_injOn]
    · exact hrho
    · intro a ha b hb hab
      exact hsigma.cumulativeWeight_pointPrefix_injective
        (hrhoSigma ha) (hrhoSigma hb) hab
  have hmPredBlock : m - 1 ∈ consecutiveRanks z n := by
    apply mem_consecutiveRanks_iff_bounds.mpr
    constructor <;> omega
  have hmSuccBlock : m + 1 ∈ consecutiveRanks z n := by
    apply mem_consecutiveRanks_iff_bounds.mpr
    constructor <;> omega
  have hmPredR : m - 1 ∈ rho.image weight := by
    rw [hRerase]
    exact Finset.mem_erase.mpr ⟨by omega, hmPredBlock⟩
  have hmSuccR : m + 1 ∈ rho.image weight := by
    rw [hRerase]
    exact Finset.mem_erase.mpr ⟨by omega, hmSuccBlock⟩
  obtain ⟨x, hxRho, hxWeight⟩ := Finset.mem_image.mp hmPredR
  obtain ⟨y, hyRho, hyWeight⟩ := Finset.mem_image.mp hmSuccR
  let C := (freudenthalFacets N n).filter (fun tau ↦ rho ⊆ tau)
  let candidates := betweenNextPoints N n (pointPrefix x) (pointPrefix y)
  let singletonImage : Finset (Finset (Point N n)) :=
    candidates.image fun a ↦ ({a} : Finset (Point N n))
  have hxy : pointPrefix x ≤ pointPrefix y := by
    obtain ⟨u, omega, hprefix⟩ :=
      (isFreudenthalTopSimplex_iff_cumulative sigma).1 hsigma
    apply le_of_mem_freudenthalSimplex_of_weight_le
        u (permutationList omega)
    · rw [← hprefix]
      exact Finset.mem_image.mpr ⟨x, hrhoSigma hxRho, rfl⟩
    · rw [← hprefix]
      exact Finset.mem_image.mpr ⟨y, hrhoSigma hyRho, rfl⟩
    · change weight x ≤ weight y
      omega
  have hxyWeight :
      cumulativeWeight (pointPrefix y) =
        cumulativeWeight (pointPrefix x) + 2 := by
    change weight y = weight x + 2
    omega
  have hmaps : Set.MapsTo
      (fun tau : Finset (Point N n) ↦ tau \ rho)
      (C : Set (Finset (Point N n))) singletonImage := by
    intro tau htauC
    have htauData := Finset.mem_filter.mp htauC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hdiffCard := card_sdiff_codimFace_of_topSimplex
      hrho htauTop htauData.2
    obtain ⟨a, haDiff⟩ := Finset.card_eq_one.mp hdiffCard
    have haTau : a ∈ tau := by
      have : a ∈ tau \ rho := by rw [haDiff]; simp
      exact (Finset.mem_sdiff.mp this).1
    have haNotRho : a ∉ rho := by
      have : a ∈ tau \ rho := by rw [haDiff]; simp
      exact (Finset.mem_sdiff.mp this).2
    obtain ⟨w, hwRanks⟩ :=
      htauTop.image_cumulativeWeight_pointPrefix
    have hRw : rho.image weight ⊆
        consecutiveRanks (cumulativeWeight w) n := by
      rw [← hwRanks]
      exact Finset.image_mono _ htauData.2
    have haW : weight a ∈
        consecutiveRanks (cumulativeWeight w) n := by
      rw [← hwRanks]
      exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
    have haNotImage : weight a ∉ rho.image weight := by
      intro haImage
      obtain ⟨b, hbRho, hbWeight⟩ := Finset.mem_image.mp haImage
      have hab : a = b := by
        exact htauTop.cumulativeWeight_pointPrefix_injective
          haTau (htauData.2 hbRho) hbWeight.symm
      exact haNotRho (hab ▸ hbRho)
    have hmBlock : m ∈ consecutiveRanks z n := by
      apply mem_consecutiveRanks_iff_bounds.mpr
      constructor <;> omega
    have haCases := completion_rank_cases hn hcardR hmBlock hRerase
      hRw haW haNotImage
    have haWeight : weight a = m := by
      rcases haCases with ha | ha | ha
      · exact ha
      · omega
      · omega
    obtain ⟨v, omega, hprefix⟩ :=
      (isFreudenthalTopSimplex_iff_cumulative tau).1 htauTop
    have hxa : pointPrefix x ≤ pointPrefix a := by
      apply le_of_mem_freudenthalSimplex_of_weight_le
          v (permutationList omega)
      · rw [← hprefix]
        exact Finset.mem_image.mpr ⟨x, htauData.2 hxRho, rfl⟩
      · rw [← hprefix]
        exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
      · change weight x ≤ weight a
        omega
    have hay : pointPrefix a ≤ pointPrefix y := by
      apply le_of_mem_freudenthalSimplex_of_weight_le
          v (permutationList omega)
      · rw [← hprefix]
        exact Finset.mem_image.mpr ⟨a, haTau, rfl⟩
      · rw [← hprefix]
        exact Finset.mem_image.mpr ⟨y, htauData.2 hyRho, rfl⟩
      · change weight a ≤ weight y
        omega
    have haCandidate : a ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hxa, hay, ?_⟩
      change weight a = weight x + 1
      omega
    change tau \ rho ∈ singletonImage
    rw [haDiff]
    apply Finset.mem_image.mpr
    exact ⟨a, haCandidate, rfl⟩
  have hinj : Set.InjOn
      (fun tau : Finset (Point N n) ↦ tau \ rho)
      (C : Set (Finset (Point N n))) := by
    exact sdiff_injective_on_cofacets
  have hcard := Finset.card_le_card_of_injOn
    (fun tau : Finset (Point N n) ↦ tau \ rho) hmaps hinj
  change C.card ≤ singletonImage.card at hcard
  calc
    C.card ≤ singletonImage.card := hcard
    _ = candidates.card := by
      change (candidates.image fun a ↦ ({a} : Finset (Point N n))).card =
        candidates.card
      rw [Finset.card_image_of_injective]
      intro a b hab
      simpa using hab
    _ ≤ 2 := betweenNextPoints_card_le_two hxy hxyWeight

/-- The concrete Freudenthal facet set is nonbranching in every positive
dimension.  The proof classifies the unique missing intrinsic rank of an
arbitrary codimension-one face and invokes the separately proved interior,
first-endpoint, and last-endpoint completion bounds. -/
theorem freudenthalFacets_nonbranching {N n : ℕ} (hn : 0 < n) :
    FacetChain.Nonbranching (freudenthalFacets N n) n := by
  intro rho hrho
  let C := (freudenthalFacets N n).filter (fun tau ↦ rho ⊆ tau)
  by_cases hC : C.Nonempty
  · obtain ⟨sigma, hsigmaC⟩ := hC
    have hsigmaData := Finset.mem_filter.mp hsigmaC
    have hsigma := (mem_freudenthalFacets_iff sigma).1 hsigmaData.1
    obtain ⟨u, huRanks⟩ :=
      hsigma.image_cumulativeWeight_pointPrefix
    let z := cumulativeWeight u
    let R := rho.image (fun a ↦ cumulativeWeight (pointPrefix a))
    have hcardR : R.card = n := by
      change (rho.image
        (fun a ↦ cumulativeWeight (pointPrefix a))).card = n
      rw [Finset.card_image_of_injOn]
      · exact hrho
      · intro a ha b hb hab
        exact hsigma.cumulativeWeight_pointPrefix_injective
          (hsigmaData.2 ha) (hsigmaData.2 hb) hab
    have hRsub : R ⊆ consecutiveRanks z n := by
      change rho.image (fun a ↦ cumulativeWeight (pointPrefix a)) ⊆ _
      rw [← huRanks]
      exact Finset.image_mono _ hsigmaData.2
    obtain ⟨m, hmBlock, hRerase⟩ :=
      exists_erased_rank_of_subset_consecutiveRanks hcardR hRsub
    have hmBounds := bounds_of_mem_consecutiveRanks hmBlock
    have hmCases : m = z ∨ m = z + n ∨ (z < m ∧ m < z + n) := by
      omega
    rcases hmCases with hmFirst | hmLast | hmInterior
    · subst m
      exact cofacets_card_le_two_of_first_erased_rank hn hrho
        hsigma hsigmaData.2 hRerase
    · subst m
      exact cofacets_card_le_two_of_last_erased_rank hn hrho
        hsigma hsigmaData.2 hRerase
    · exact cofacets_card_le_two_of_interior_erased_rank hn hrho
        hsigma hsigmaData.2 hRerase hmInterior.1 hmInterior.2
  · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    change C.card ≤ 2
    simp [hCempty]

/-- Inserting a zero as the last original coordinate preserves every old
cumulative coordinate. -/
@[simp]
theorem pointPrefix_insertZeroPoint_last_castSucc {N n : ℕ}
    (a : Point N n) (q : Fin n) :
    pointPrefix (insertZeroPoint (Fin.last (n + 1)) a) q.castSucc =
      pointPrefix a q := by
  unfold pointPrefix prefixMap
  rw [pointCoords_insertZeroPoint]
  symm
  apply Finset.sum_bij (fun k _ ↦ k.castSucc)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk
  · intro k₁ _ k₂ _ h
    apply Fin.ext
    exact congrArg (fun x : Fin (n + 2) ↦ x.val) h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hkLast : k ≠ Fin.last (n + 1) := by
      intro h
      subst k
      simp at hk
      have hq := q.isLt
      omega
    obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hkLast
    refine ⟨j, ?_, hj⟩
    simpa [← hj] using hk
  · intro k hk
    rw [← Fin.succAbove_last_apply k,
      insertZeroCoords_apply_succAbove]

/-- On the last coordinate face, the new final cumulative coordinate is the
total mass `N`. -/
@[simp]
theorem pointPrefix_insertZeroPoint_last_last {N n : ℕ}
    (a : Point N n) :
    pointPrefix (insertZeroPoint (Fin.last (n + 1)) a) (Fin.last n) = N := by
  unfold pointPrefix prefixMap
  rw [pointCoords_insertZeroPoint]
  have hfilter :
      (Finset.univ.filter fun k : Fin (n + 2) ↦
        k.val ≤ (Fin.last n).val) =
      (Finset.univ : Finset (Fin (n + 2))).erase (Fin.last (n + 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · intro hk
      constructor
      · intro hlast
        subst k
        simp at hk
      · trivial
    · rintro ⟨hk, _⟩
      have hle := Fin.le_last k
      have hneVal : k.val ≠ n + 1 := by
        intro hval
        apply hk
        apply Fin.ext
        simpa using hval
      simp only [Fin.val_last] at hle ⊢
      omega
  rw [hfilter, Finset.sum_erase]
  · exact (insertZeroCoords_isPoint
      (Fin.last (n + 1)) (pointCoords_isPoint a)).2
  · exact insertZeroCoords_apply_self _ _

/-- Last-face insertion shifts intrinsic cumulative rank by the constant
total mass `N`. -/
theorem cumulativeWeight_pointPrefix_insertZeroPoint_last {N n : ℕ}
    (a : Point N n) :
    cumulativeWeight
        (pointPrefix (insertZeroPoint (Fin.last (n + 1)) a)) =
      cumulativeWeight (pointPrefix a) + N := by
  rw [cumulativeWeight, Fin.sum_univ_castSucc]
  simp [cumulativeWeight]

/-- Translating an `(n+1)`-term consecutive block by `c` gives the first
endpoint face of the next-dimensional consecutive block. -/
theorem image_add_consecutiveRanks_eq_erase_first
    (z c : ℤ) (n : ℕ) :
    (consecutiveRanks z n).image (fun x ↦ x + c) =
      (consecutiveRanks (z + c - 1) (n + 1)).erase (z + c - 1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r, hr, hyr⟩ := mem_consecutiveRanks_iff.mp hy
    apply Finset.mem_erase.mpr
    constructor
    · rw [hyr]
      omega
    · apply mem_consecutiveRanks_iff.mpr
      refine ⟨r + 1, by omega, ?_⟩
      rw [hyr]
      push_cast
      ring
  · intro hx
    have hxData := Finset.mem_erase.mp hx
    obtain ⟨r, hr, hxr⟩ := mem_consecutiveRanks_iff.mp hxData.2
    have hrPos : 0 < r := by
      by_contra hzero
      have : r = 0 := by omega
      subst r
      simp at hxr
      exact hxData.1 hxr
    apply Finset.mem_image.mpr
    refine ⟨z + (r - 1 : ℕ), ?_, ?_⟩
    · apply mem_consecutiveRanks_iff.mpr
      refine ⟨r - 1, by omega, rfl⟩
    · rw [hxr]
      omega

/-- At positive scale there is a genuine Freudenthal top simplex in every
dimension.  The construction is inductive: the zero-dimensional facet is
explicit, and the last-coordinate face lift supplies a containing facet in
the next dimension. -/
theorem exists_freudenthalTopSimplex_of_pos {N n : ℕ} (hN : 0 < N) :
    ∃ rho : Finset (Point N n), IsFreudenthalTopSimplex rho := by
  induction n with
  | zero =>
      exact ⟨{zeroDimPoint N}, zeroDimPoint_isFreudenthalTopSimplex⟩
  | succ n ih =>
      obtain ⟨rho, hrho⟩ := ih
      let face : Finset (Point N (n + 1)) :=
        rho.image (insertZeroPoint (Fin.last (n + 1)))
      have hfaceMem : face ∈ freudenthalComplex N (n + 1) :=
        image_insertZeroPoint_last_mem_freudenthalComplex hN hrho
      have hfaceSimplex := (mem_freudenthalComplex_iff face).1 hfaceMem
      rcases hfaceSimplex with hzero | ⟨sigma, hsigma, _⟩
      · have hrhoNonempty : rho.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hrhoEmpty
          have hcard := hrho.card
          rw [hrhoEmpty] at hcard
          simp at hcard
        have hfaceNonempty : face.Nonempty :=
          hrhoNonempty.image _
        exact (hfaceNonempty.ne_empty hzero).elim
      · exact ⟨sigma, hsigma⟩

/-- At positive scale the Freudenthal complex is pure: every simplex is a
face of a top simplex with exactly `n + 1` vertices.  The empty simplex uses
the separately constructed top simplex; every nonempty generated face
already carries a top-simplex witness in `IsFreudenthalSimplex`. -/
theorem freudenthalComplex_isPureOfCardinality_of_pos
    {N n : ℕ} (hN : 0 < N) :
    (freudenthalComplex N n).IsPureOfCardinality (n + 1) := by
  intro tau htau
  rcases (mem_freudenthalComplex_iff tau).1 htau with hEmpty | ⟨rho, hrho, htauSub⟩
  · subst tau
    obtain ⟨rho, hrho⟩ := exists_freudenthalTopSimplex_of_pos (N := N) (n := n) hN
    exact ⟨rho, hrho.mem_complex, Finset.empty_subset rho, hrho.card⟩
  · exact ⟨rho, hrho.mem_complex, htauSub, hrho.card⟩

/-- The image of a lower facet in the last coordinate face has precisely the
rank set obtained by deleting the first rank of an ambient consecutive
block. -/
theorem image_cumulativeWeight_lastFace_eq_erase_first
    {N n : ℕ} {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho) :
    ∃ z : ℤ,
      (rho.image (insertZeroPoint (Fin.last (n + 1)))).image
          (fun a ↦ cumulativeWeight (pointPrefix a)) =
        (consecutiveRanks z (n + 1)).erase z := by
  obtain ⟨u, hu⟩ := hrho.image_cumulativeWeight_pointPrefix
  let base := cumulativeWeight u
  refine ⟨base + N - 1, ?_⟩
  calc
    (rho.image (insertZeroPoint (Fin.last (n + 1)))).image
        (fun a ↦ cumulativeWeight (pointPrefix a)) =
      rho.image (fun a ↦ cumulativeWeight (pointPrefix a) + N) := by
        ext x
        simp [cumulativeWeight_pointPrefix_insertZeroPoint_last]
    _ = (rho.image (fun a ↦ cumulativeWeight (pointPrefix a))).image
        (fun x : ℤ ↦ x + N) := by
          rw [Finset.image_image]
          rfl
    _ = (consecutiveRanks base n).image
        (fun x : ℤ ↦ x + N) := by
      rw [hu]
    _ = (consecutiveRanks (base + N - 1) (n + 1)).erase
        (base + N - 1) := image_add_consecutiveRanks_eq_erase_first
          base (N : ℤ) n

/-- A lifted last-coordinate facet is a genuine boundary face: it belongs to
exactly one ambient Freudenthal top simplex.  The possible second completion
would increase the new final cumulative coordinate from `N` to `N+1`, which
is impossible for a point of `Point N (n+1)`. -/
theorem lastFace_cofacets_card_eq_one
    {N n : ℕ} (hN : 0 < N)
    {rho : Finset (Point N n)} (hrho : IsFreudenthalTopSimplex rho) :
    ((freudenthalFacets N (n + 1)).filter fun tau ↦
      rho.image (insertZeroPoint (Fin.last (n + 1))) ⊆ tau).card = 1 := by
  let face : Finset (Point N (n + 1)) :=
    rho.image (insertZeroPoint (Fin.last (n + 1)))
  let weight : Point N (n + 1) → ℤ :=
    fun a ↦ cumulativeWeight (pointPrefix a)
  let C := (freudenthalFacets N (n + 1)).filter fun tau ↦ face ⊆ tau
  have hfaceCard : face.card = n + 1 := by
    change (rho.image (insertZeroPoint (Fin.last (n + 1)))).card = n + 1
    rw [Finset.card_image_of_injective]
    · exact hrho.card
    · exact insertZeroPoint_injective _
  have hfaceMem : face ∈ freudenthalComplex N (n + 1) :=
    image_insertZeroPoint_last_mem_freudenthalComplex hN hrho
  have hfaceSimplex := (mem_freudenthalComplex_iff face).1 hfaceMem
  obtain ⟨sigma₀, hsigma₀, hfaceSigma₀⟩ :
      ∃ sigma₀, IsFreudenthalTopSimplex sigma₀ ∧ face ⊆ sigma₀ := by
    rcases hfaceSimplex with hzero | htop
    · exfalso
      have : face.card = 0 := by rw [hzero]; simp
      omega
    · exact htop
  have hsigma₀C : sigma₀ ∈ C := by
    apply Finset.mem_filter.mpr
    exact ⟨(mem_freudenthalFacets_iff sigma₀).2 hsigma₀,
      hfaceSigma₀⟩
  obtain ⟨z, hRerase⟩ :=
    image_cumulativeWeight_lastFace_eq_erase_first hrho
  change face.image weight = (consecutiveRanks z (n + 1)).erase z at hRerase
  have hcardR : (face.image weight).card = n + 1 := by
    rw [Finset.card_image_of_injOn]
    · exact hfaceCard
    · intro a ha b hb hab
      exact hsigma₀.cumulativeWeight_pointPrefix_injective
        (hfaceSigma₀ ha) (hfaceSigma₀ hb) hab
  have hxRank : z + 1 ∈ face.image weight := by
    rw [hRerase]
    apply Finset.mem_erase.mpr
    refine ⟨by omega, mem_consecutiveRanks_iff_bounds.mpr ?_⟩
    constructor <;> omega
  have hyRank : z + (n + 1) ∈ face.image weight := by
    rw [hRerase]
    apply Finset.mem_erase.mpr
    refine ⟨by omega, mem_consecutiveRanks_iff_bounds.mpr ?_⟩
    constructor <;> omega
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
  have hxLast : pointPrefix x (Fin.last n) = N := by
    obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.mp hxFace
    exact pointPrefix_insertZeroPoint_last_last x₀
  have hyLast : pointPrefix y (Fin.last n) = N := by
    obtain ⟨y₀, _, rfl⟩ := Finset.mem_image.mp hyFace
    exact pointPrefix_insertZeroPoint_last_last y₀
  have hlastUnused : Fin.last n ∈
      (Finset.univ : Finset (Fin (n + 1))) \
        positiveCoords (pointPrefix x) (pointPrefix y) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [positiveCoords, hxLast, hyLast]
  have hunusedEq :
      (Finset.univ : Finset (Fin (n + 1))) \
          positiveCoords (pointPrefix x) (pointPrefix y) =
        {Fin.last n} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hlastUnused, ?_⟩
    intro i hi
    exact Finset.card_le_one_iff.mp (by omega) hi hlastUnused
  have offVertexLower : ∀ tau, tau ∈ C →
      ∃ a : Point N (n + 1),
        tau \ face = {a} ∧ a ∈ tau ∧ weight a = z := by
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
    have hzBlock : z ∈ consecutiveRanks z (n + 1) :=
      mem_consecutiveRanks_iff_bounds.mpr (by constructor <;> omega)
    have haCases := completion_rank_cases (Nat.succ_pos n) hcardR
      hzBlock hRerase hRw haW haNotImage
    have haWeight : weight a = z := by
      rcases haCases with haLower | haUpper | haImpossible
      · exact haLower
      · have haWeightUpper : weight a = z + (n + 1) + 1 := haUpper.2
        have hYa : pointPrefix y ≤ pointPrefix a :=
          htauTop.pointPrefix_le_of_weight_le
            (htauData.2 hyFace) haTau (by
              change weight y ≤ weight a
              omega)
        have hstepWeight : cumulativeWeight (pointPrefix a) =
            cumulativeWeight (pointPrefix y) + 1 := by
          change weight a = weight y + 1
          omega
        have hpos := positiveCoords_nonempty_of_le_of_weight_add_one
          hYa hstepWeight
        obtain ⟨i, hiPos⟩ := hpos
        have haEq := eq_add_single_of_le_of_weight_add_one
          hYa hstepWeight (Finset.mem_filter.mp hiPos).2
        have hiUnused : i ∈
            (Finset.univ : Finset (Fin (n + 1))) \
              positiveCoords (pointPrefix x) (pointPrefix y) := by
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hiUsed
          have hiLt := (Finset.mem_filter.mp hiUsed).2
          have hXa : pointPrefix x ≤ pointPrefix a := hxy.trans hYa
          have hiStep := htauTop.coordinate_sub_eq_zero_or_one
            (htauData.2 hxFace) haTau hXa i
          have hai : pointPrefix a i = pointPrefix y i + 1 := by
            rw [haEq]
            simp
          rcases hiStep with hiStep | hiStep <;> omega
        have hiLast : i = Fin.last n := by
          rw [hunusedEq] at hiUnused
          simpa using hiUnused
        have haLast : pointPrefix a (Fin.last n) = N + 1 := by
          subst i
          rw [haEq]
          simp [hyLast]
        have haUpperBound := (pointPrefix_isGammaPoint a).2.2 (Fin.last n)
        omega
      · omega
    exact ⟨a, haDiff, haTau, haWeight⟩
  have hCsubsingleton : C.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro tau sigma htauC hsigmaC
    obtain ⟨a, hdiffTau, haTau, haWeight⟩ := offVertexLower tau htauC
    obtain ⟨b, hdiffSigma, hbSigma, hbWeight⟩ :=
      offVertexLower sigma hsigmaC
    have htauData := Finset.mem_filter.mp htauC
    have hsigmaData := Finset.mem_filter.mp hsigmaC
    have htauTop := (mem_freudenthalFacets_iff tau).1 htauData.1
    have hsigmaTop := (mem_freudenthalFacets_iff sigma).1 hsigmaData.1
    have hab : a = b := lower_completion_point_unique
      htauTop hsigmaTop htauData.2 hsigmaData.2 hxFace hyFace
      haTau hbSigma hxy
      (by change weight x = weight a + 1; omega)
      (by change weight x = weight b + 1; omega)
      hunusedCard
    exact sdiff_injective_on_cofacets htauC hsigmaC (by
      change tau \ face = sigma \ face
      rw [hdiffTau, hdiffSigma, hab])
  have hCnonempty : C.Nonempty := ⟨sigma₀, hsigma₀C⟩
  change C.card = 1
  exact Nat.le_antisymm hCsubsingleton (Finset.one_le_card.mpr hCnonempty)

/-- Positive-scale Freudenthal facets have a nonempty simplicial boundary in
every positive dimension. -/
theorem freudenthalFacets_hasNonemptyBoundary_of_pos
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    FacetChain.HasNonemptyBoundary (freudenthalFacets N n) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨rho, hrho⟩ := exists_freudenthalTopSimplex_of_pos
    (N := N) (n := m) hN
  refine ⟨rho.image (insertZeroPoint (Fin.last (m + 1))), ?_, ?_⟩
  · rw [Finset.card_image_of_injective]
    · exact hrho.card
    · exact insertZeroPoint_injective _
  · exact lastFace_cofacets_card_eq_one hN hrho

end IntegerSimplex

end BeyondSperner
