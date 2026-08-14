import BeyondSperner.Freudenthal.Geometry

/-!
# Connectivity geometry for the Freudenthal complex

This file proves strong facet-connectivity.  Its first task closes a genuine
representation gap: cumulative coordinates were
previously proved injective on `Point N n`, but the converse realization of
every integral point of the monotone simplex `Gamma` had not been packaged.
The consecutive differences below give the explicit inverse.
-/

namespace BeyondSperner

open Classical

namespace IntegerSimplex

/-! ## Unit increments inside `Gamma` -/

/-- Exact criterion for a unit coordinate increment to remain in the
monotone integer simplex `Gamma`.  Besides the upper bound, the incremented
coordinate must be strictly below every coordinate to its right. -/
theorem isGammaPoint_add_single_iff {N : ℤ} {n : ℕ}
    {y : Fin n → ℤ} (hy : IsGammaPoint N y) (i : Fin n) :
    IsGammaPoint N (y + Pi.single i 1) ↔
      y i < N ∧ ∀ j, i < j → y i < y j := by
  constructor
  · intro h
    constructor
    · have hiUpper := h.2.2 i
      simp only [Pi.add_apply, Pi.single_eq_same] at hiUpper
      omega
    · intro j hij
      have hijNe : j ≠ i := hij.ne'
      have hmono := h.2.1 i j hij.le
      simp only [Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hijNe] at hmono
      omega
  · rintro ⟨hiUpper, hiRight⟩
    constructor
    · intro j
      have hjNonneg := hy.1 j
      simp only [Pi.add_apply, Pi.single_apply]
      split <;> omega
    constructor
    · intro a b hab
      simp only [Pi.add_apply, Pi.single_apply]
      by_cases hai : a = i
      · subst a
        by_cases hbi : b = i
        · subst b
          simp
        · have hib : i < b := lt_of_le_of_ne hab (Ne.symm hbi)
          rw [if_pos rfl, if_neg hbi]
          have := hiRight b hib
          omega
      · rw [if_neg hai]
        by_cases hbi : b = i
        · subst b
          rw [if_pos rfl]
          have := hy.2.1 a i hab
          omega
        · rw [if_neg hbi]
          simpa using hy.2.1 a b hab
    · intro j
      simp only [Pi.add_apply, Pi.single_apply]
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl]
        omega
      · rw [if_neg hji]
        simpa using hy.2.2 j

/-- Local diamond lemma for Freudenthal paths.  If incrementing `i` and then
`j` reaches a point of `Gamma`, then the two increments may be swapped unless
the only potentially repaired inequality, from `j` to `i`, was an equality.
The explicit strictness hypothesis rules out exactly that case. -/
theorem isGammaPoint_add_single_swap {N : ℤ} {n : ℕ}
    {y : Fin n → ℤ} (hy : IsGammaPoint N y)
    {i j : Fin n} (hij : i ≠ j)
    (hfinal : IsGammaPoint N
      (y + Pi.single i 1 + Pi.single j 1))
    (hstrict : j < i → y j < y i) :
    IsGammaPoint N (y + Pi.single j 1) := by
  rw [isGammaPoint_add_single_iff hy j]
  constructor
  · have hjUpper := hfinal.2.2 j
    simp [hij.symm] at hjUpper
    omega
  · intro k hjk
    by_cases hki : k = i
    · subst k
      exact hstrict hjk
    · have hkj : k ≠ j := hjk.ne'
      have hmono := hfinal.2.1 j k hjk.le
      simp [hij.symm, hki, hkj] at hmono
      omega

/-! ## Exact list geometry for adjacent swaps -/

/-- Endpoint after applying all unit increments in a coordinate list. -/
def freudenthalEndpoint {n : ℕ} (u : Fin n → ℤ)
    (l : List (Fin n)) : Fin n → ℤ :=
  l.foldl (fun y i ↦ y + Pi.single i 1) u

@[simp]
theorem freudenthalEndpoint_nil {n : ℕ} (u : Fin n → ℤ) :
    freudenthalEndpoint u [] = u := rfl

@[simp]
theorem freudenthalEndpoint_cons {n : ℕ} (u : Fin n → ℤ)
    (i : Fin n) (l : List (Fin n)) :
    freudenthalEndpoint u (i :: l) =
      freudenthalEndpoint (u + Pi.single i 1) l := rfl

/-- The recursive Freudenthal sequence is the usual left scan. -/
theorem freudenthalSequence_eq_scanl {n : ℕ} (u : Fin n → ℤ)
    (l : List (Fin n)) :
    freudenthalSequence u l =
      l.scanl (fun y i ↦ y + Pi.single i 1) u := by
  induction l generalizing u with
  | nil => rfl
  | cons i l ih =>
      simp only [freudenthalSequence, List.scanl_cons]
      rw [ih]

/-- Appending a transfer list appends the new scan after deleting its
duplicated initial endpoint. -/
theorem freudenthalSequence_append {n : ℕ} (u : Fin n → ℤ)
    (p q : List (Fin n)) :
    freudenthalSequence u (p ++ q) =
      freudenthalSequence u p ++
        (freudenthalSequence (freudenthalEndpoint u p) q).tail := by
  simp only [freudenthalSequence_eq_scanl, freudenthalEndpoint]
  exact List.scanl_append

/-- Two consecutive increments have the same endpoint in either order. -/
theorem add_single_add_single_comm {n : ℕ} (u : Fin n → ℤ)
    (i j : Fin n) :
    u + Pi.single i 1 + Pi.single j 1 =
      u + Pi.single j 1 + Pi.single i 1 := by
  funext k
  simp only [Pi.add_apply]
  rw [add_right_comm]

/-- Decreasing and then restoring the same coordinate is the identity. -/
theorem sub_single_add_single {n : ℕ} (u : Fin n → ℤ)
    (i : Fin n) :
    u - Pi.single i 1 + Pi.single i 1 = u := by
  funext k
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- Exact vertex-set decomposition at two consecutive steps.  It isolates
the single intermediate vertex changed by an adjacent transposition. -/
theorem freudenthalSimplex_pair_decomposition {n : ℕ}
    (u : Fin n → ℤ) (p s : List (Fin n)) (i j : Fin n) :
    freudenthalSimplex u (p ++ i :: j :: s) =
      freudenthalSimplex u p ∪
        insert (freudenthalEndpoint u p + Pi.single i 1)
          (freudenthalSimplex
            (freudenthalEndpoint u p + Pi.single i 1 + Pi.single j 1) s) := by
  rw [freudenthalSimplex, freudenthalSequence_append]
  simp [freudenthalSimplex, freudenthalSequence]

/-- Decomposition when the final transfer is singled out. -/
theorem freudenthalSimplex_append_single {n : ℕ}
    (u : Fin n → ℤ) (p : List (Fin n)) (i : Fin n) :
    freudenthalSimplex u (p ++ [i]) =
      insert (freudenthalEndpoint u p + Pi.single i 1)
        (freudenthalSimplex u p) := by
  rw [freudenthalSimplex, freudenthalSequence_append]
  simp [freudenthalSimplex, freudenthalSequence]

/-- Decomposition when the first transfer is singled out. -/
theorem freudenthalSimplex_cons {n : ℕ}
    (u : Fin n → ℤ) (i : Fin n) (s : List (Fin n)) :
    freudenthalSimplex u (i :: s) =
      insert u (freudenthalSimplex (u + Pi.single i 1) s) := by
  simp [freudenthalSimplex, freudenthalSequence]

/-- The endpoint is the final member of its Freudenthal sequence. -/
theorem freudenthalEndpoint_mem_sequence {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n)) :
    freudenthalEndpoint u l ∈ freudenthalSequence u l := by
  induction l generalizing u with
  | nil => simp [freudenthalEndpoint, freudenthalSequence]
  | cons i l ih =>
      simp only [freudenthalEndpoint_cons, freudenthalSequence,
        List.mem_cons]
      exact Or.inr (ih (u + Pi.single i 1))

theorem freudenthalEndpoint_mem_simplex {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n)) :
    freudenthalEndpoint u l ∈ freudenthalSimplex u l := by
  simpa [freudenthalSimplex] using
    freudenthalEndpoint_mem_sequence u l

theorem freudenthalBase_mem_simplex {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n)) :
    u ∈ freudenthalSimplex u l := by
  cases l <;> simp [freudenthalSimplex, freudenthalSequence]

/-- A coordinate absent from the transfer list is unchanged at the
endpoint. -/
theorem freudenthalEndpoint_coordinate_eq_of_not_mem {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n)) {q : Fin n}
    (hq : q ∉ l) :
    freudenthalEndpoint u l q = u q := by
  induction l generalizing u with
  | nil => rfl
  | cons i l ih =>
      have hdata : q ≠ i ∧ q ∉ l := by simpa using hq
      rw [freudenthalEndpoint_cons, ih (u + Pi.single i 1) hdata.2]
      simp [hdata.1]

/-- Once the swapped intermediate point is known to lie in `Gamma`, every
vertex of the swapped simplex lies there: all other vertices are shared by
the original simplex. -/
theorem isGammaPoint_of_mem_freudenthalSimplex_adjacent_swap
    {N : ℤ} {n : ℕ} (u : Fin n → ℤ)
    (p s : List (Fin n)) (i j : Fin n)
    (hGamma : ∀ z ∈ freudenthalSimplex u (p ++ i :: j :: s),
      IsGammaPoint N z)
    (hnew : IsGammaPoint N
      (freudenthalEndpoint u p + Pi.single j 1)) :
    ∀ z ∈ freudenthalSimplex u (p ++ j :: i :: s),
      IsGammaPoint N z := by
  intro z hz
  rw [freudenthalSimplex_pair_decomposition] at hz
  rcases Finset.mem_union.mp hz with hzPrefix | hz
  · apply hGamma z
    rw [freudenthalSimplex_pair_decomposition]
    exact Finset.mem_union_left _ hzPrefix
  · rcases Finset.mem_insert.mp hz with rfl | hzSuffix
    · exact hnew
    · apply hGamma z
      rw [freudenthalSimplex_pair_decomposition]
      apply Finset.mem_union_right
      apply Finset.mem_insert_of_mem
      simpa only [add_single_add_single_comm
        (freudenthalEndpoint u p) i j] using hzSuffix

/-- The endpoint rank is the base rank plus the number of performed unit
increments. -/
theorem cumulativeWeight_freudenthalEndpoint {n : ℕ}
    (u : Fin n → ℤ) (l : List (Fin n)) :
    cumulativeWeight (freudenthalEndpoint u l) =
      cumulativeWeight u + l.length := by
  induction l generalizing u with
  | nil => simp
  | cons i l ih =>
      rw [freudenthalEndpoint_cons, ih,
        cumulativeWeight_add_single]
      simp only [List.length_cons]
      push_cast
      ring

/-- A duplicate-free transfer list produces exactly one more vertex than
its length. -/
theorem card_freudenthalSimplex_of_nodup {n : ℕ}
    (u : Fin n → ℤ) {l : List (Fin n)} (hl : l.Nodup) :
    (freudenthalSimplex u l).card = l.length + 1 := by
  rw [freudenthalSimplex,
    List.toFinset_card_of_nodup (freudenthalSequence_nodup u hl),
    length_freudenthalSequence]


/-- Recover original simplex coordinates from cumulative coordinates.  The
formula is `(y₀, y₁-y₀, ..., yₙ₋₁-yₙ₋₂, N-yₙ₋₁)`, expressed
uniformly using `Fin.cons` and `Fin.snoc`; it also handles `n = 0`. -/
def gammaCoords (N : ℤ) {n : ℕ} (y : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  Fin.snoc y N - Fin.cons 0 y

@[simp]
theorem gammaCoords_zero (N : ℤ) (y : Fin 0 → ℤ) (k : Fin 1) :
    gammaCoords N y k = N := by
  have hk : k = 0 := Fin.eq_zero k
  subst k
  have hzeroLast : (0 : Fin 1) = Fin.last 0 := by rfl
  rw [gammaCoords, Pi.sub_apply, hzeroLast, Fin.snoc_last]
  simp

/-- The first recovered coordinate is the first cumulative coordinate. -/
@[simp]
theorem gammaCoords_apply_zero {N : ℤ} {n : ℕ}
    (y : Fin (n + 1) → ℤ) :
    gammaCoords N y 0 = y 0 := by
  simp [gammaCoords]

/-- Every interior recovered coordinate is the difference of consecutive
cumulative coordinates. -/
theorem gammaCoords_apply_castSucc_of_ne_zero {N : ℤ} {n : ℕ}
    (y : Fin (n + 1) → ℤ) (q : Fin (n + 1)) (hq : q ≠ 0) :
    gammaCoords N y q.castSucc =
      y q - y ⟨q.val - 1, by omega⟩ := by
  simp only [gammaCoords, Pi.sub_apply]
  rw [Fin.snoc_castSucc]
  have hqval : 0 < q.val := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hq (Fin.ext h)
  have hsucc : q.castSucc =
      (⟨q.val - 1, by omega⟩ : Fin (n + 1)).succ := by
    apply Fin.ext
    simp
    omega
  rw [hsucc, Fin.cons_succ]

/-- The final recovered coordinate is the remaining mass. -/
@[simp]
theorem gammaCoords_apply_last {N : ℤ} {n : ℕ}
    (y : Fin (n + 1) → ℤ) :
    gammaCoords N y (Fin.last (n + 1)) = N - y (Fin.last n) := by
  simp [gammaCoords]

/-- Consecutive differences telescope back to the supplied cumulative
coordinates. -/
theorem prefixMap_gammaCoords {N : ℤ} {n : ℕ} (y : Fin n → ℤ) :
    prefixMap (gammaCoords N y) = y := by
  cases n with
  | zero =>
      funext q
      exact Fin.elim0 q
  | succ n =>
      funext q
      induction q using Fin.induction with
      | zero =>
          rw [prefixMap_eq_of_val_zero]
          · exact gammaCoords_apply_zero y
          · rfl
      | succ q ih =>
          rw [prefixMap_eq_prev_add]
          · have hprevIndex :
                (⟨q.succ.val - 1, by omega⟩ : Fin (n + 1)) =
                  q.castSucc := by
                apply Fin.ext
                simp
            rw [hprevIndex, ih,
              gammaCoords_apply_castSucc_of_ne_zero]
            · rw [hprevIndex]
              ring
            · simp
          · simp

/-- The recovered coordinates have total mass `N`. -/
theorem sum_gammaCoords {N : ℤ} {n : ℕ} (y : Fin n → ℤ) :
    ∑ k, gammaCoords N y k = N := by
  simp [gammaCoords, Finset.sum_sub_distrib]

/-- Monotonicity and endpoint bounds are exactly the nonnegativity
conditions for the recovered difference coordinates. -/
theorem gammaCoords_isPoint {N n : ℕ} {y : Fin n → ℤ}
    (hy : IsGammaPoint (N : ℤ) y) :
    IsPoint (N : ℤ) (gammaCoords (N : ℤ) y) := by
  constructor
  · cases n with
    | zero =>
        intro k
        rw [gammaCoords_zero]
        exact Int.natCast_nonneg N
    | succ n =>
        intro k
        by_cases hkZero : k = 0
        · subst k
          simpa using hy.1 0
        have hkPos : 0 < k := Fin.pos_iff_ne_zero.mpr hkZero
        rcases Fin.eq_castSucc_or_eq_last k with ⟨q, rfl⟩ | rfl
        · rw [gammaCoords_apply_castSucc_of_ne_zero]
          · exact sub_nonneg.mpr (hy.2.1 _ _ (by
              apply Fin.le_iff_val_le_val.mpr
              simp))
          · exact Fin.ne_of_val_ne (by simpa using hkPos.ne')
        · rw [gammaCoords_apply_last]
          exact sub_nonneg.mpr (hy.2.2 (Fin.last n))
  · exact sum_gammaCoords y

/-- Bundle a monotone cumulative integer vector as an actual integer-simplex
point. -/
def pointOfGamma {N n : ℕ} (y : Fin n → ℤ)
    (hy : IsGammaPoint (N : ℤ) y) : Point N n :=
  pointOfIsPoint (gammaCoords (N : ℤ) y) (gammaCoords_isPoint hy)

@[simp]
theorem pointPrefix_pointOfGamma {N n : ℕ} (y : Fin n → ℤ)
    (hy : IsGammaPoint (N : ℤ) y) :
    pointPrefix (pointOfGamma y hy) = y := by
  rw [pointPrefix, pointOfGamma, pointCoords_pointOfIsPoint,
    prefixMap_gammaCoords]

/-- `pointPrefix` is an equivalence between integer simplex points and the
integral monotone simplex, not merely an embedding. -/
noncomputable def pointGammaEquiv (N n : ℕ) :
    Point N n ≃ {y : Fin n → ℤ // IsGammaPoint (N : ℤ) y} where
  toFun a := ⟨pointPrefix a, pointPrefix_isGammaPoint a⟩
  invFun y := pointOfGamma y.1 y.2
  left_inv _a := pointPrefix_injective (pointPrefix_pointOfGamma _ _)
  right_inv y := Subtype.ext (pointPrefix_pointOfGamma y.1 y.2)

/-- Realize a finite set of cumulative vectors by taking exactly the simplex
points whose cumulative image lies in that set. -/
noncomputable def realizeGammaSet (N n : ℕ)
    (S : Finset (Fin n → ℤ)) : Finset (Point N n) :=
  Finset.univ.filter fun a ↦ pointPrefix a ∈ S

/-- If every requested vector lies in `Gamma`, realization has exactly the
requested cumulative-coordinate image. -/
theorem image_pointPrefix_realizeGammaSet {N n : ℕ}
    (S : Finset (Fin n → ℤ))
    (hS : ∀ y ∈ S, IsGammaPoint (N : ℤ) y) :
    (realizeGammaSet N n S).image pointPrefix = S := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp ha).2
  · intro hy
    let a : Point N n := pointOfGamma y (hS y hy)
    apply Finset.mem_image.mpr
    refine ⟨a, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by
        simpa [a] using hy⟩
    · exact pointPrefix_pointOfGamma y (hS y hy)

/-- A standard Freudenthal cumulative simplex all of whose vertices lie in
`Gamma` realizes to a genuine top simplex of `Point N n`. -/
theorem isFreudenthalTopSimplex_realizeGammaSet
    {N n : ℕ} (u : Fin n → ℤ) (omega : Equiv.Perm (Fin n))
    (hGamma : ∀ y ∈ freudenthalSimplex u (permutationList omega),
      IsGammaPoint (N : ℤ) y) :
    IsFreudenthalTopSimplex
      (realizeGammaSet N n
        (freudenthalSimplex u (permutationList omega))) := by
  apply (isFreudenthalTopSimplex_iff_cumulative _).2
  exact ⟨u, omega,
    image_pointPrefix_realizeGammaSet _ hGamma⟩

/-- Cumulative-coordinate images preserve intersections because
`pointPrefix` is injective. -/
theorem image_pointPrefix_inter {N n : ℕ}
    (rho sigma : Finset (Point N n)) :
    (rho ∩ sigma).image pointPrefix =
      rho.image pointPrefix ∩ sigma.image pointPrefix := by
  exact Finset.image_inter rho sigma pointPrefix_injective

/-- Exact cumulative-image data can be used to establish concrete facet
adjacency. -/
theorem facetAdjacent_of_cumulative_images
    {N n : ℕ} {rho sigma : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho)
    (hsigma : IsFreudenthalTopSimplex sigma)
    {R S : Finset (Fin n → ℤ)}
    (hR : rho.image pointPrefix = R)
    (hS : sigma.image pointPrefix = S)
    (hne : R ≠ S) (hcard : (R ∩ S).card = n) :
    FacetChain.Adjacent (freudenthalFacets N n) n rho sigma := by
  refine ⟨(mem_freudenthalFacets_iff rho).2 hrho,
    (mem_freudenthalFacets_iff sigma).2 hsigma, ?_, ?_⟩
  · intro hrs
    apply hne
    rw [← hR, ← hS, hrs]
  · calc
      (rho ∩ sigma).card =
          ((rho ∩ sigma).image pointPrefix).card := by
        symm
        rw [Finset.card_image_of_injective]
        exact pointPrefix_injective
      _ = (R ∩ S).card := by
        rw [image_pointPrefix_inter, hR, hS]
      _ = n := hcard

/-- Package a duplicate-free full coordinate list whose whole cumulative
simplex lies in `Gamma` as a genuine Freudenthal top simplex. -/
theorem isFreudenthalTopSimplex_realizeGammaList
    {N n : ℕ} (u : Fin n → ℤ) (l : List (Fin n))
    (hl : l.Nodup) (hlen : l.length = n)
    (hGamma : ∀ y ∈ freudenthalSimplex u l,
      IsGammaPoint (N : ℤ) y) :
    IsFreudenthalTopSimplex
      (realizeGammaSet N n (freudenthalSimplex u l)) := by
  obtain ⟨omega, homega⟩ :=
    exists_permutationList_eq_of_nodup_length l hl hlen
  rw [← homega] at hGamma ⊢
  exact isFreudenthalTopSimplex_realizeGammaSet u omega hGamma

/-- Adjacent transposition of two consecutive, distinct coordinate steps
changes exactly one vertex.  If the new intermediate vertex remains in
`Gamma`, the two realized simplices are genuinely adjacent facets. -/
theorem facetAdjacent_realize_adjacent_swap
    {N n : ℕ} (u : Fin n → ℤ) (p s : List (Fin n))
    (i j : Fin n)
    (hl : (p ++ i :: j :: s).Nodup)
    (hlen : (p ++ i :: j :: s).length = n)
    (hGamma : ∀ z ∈ freudenthalSimplex u (p ++ i :: j :: s),
      IsGammaPoint (N : ℤ) z)
    (hij : i ≠ j)
    (hnew : IsGammaPoint (N : ℤ)
      (freudenthalEndpoint u p + Pi.single j 1)) :
    FacetChain.Adjacent (freudenthalFacets N n) n
      (realizeGammaSet N n
        (freudenthalSimplex u (p ++ i :: j :: s)))
      (realizeGammaSet N n
        (freudenthalSimplex u (p ++ j :: i :: s))) := by
  let e := freudenthalEndpoint u p
  let x := e + Pi.single i 1
  let y := e + Pi.single j 1
  let w := e + Pi.single i 1 + Pi.single j 1
  let A := freudenthalSimplex u p
  let B := freudenthalSimplex w s
  let C := A ∪ B
  let R := freudenthalSimplex u (p ++ i :: j :: s)
  let S := freudenthalSimplex u (p ++ j :: i :: s)
  have hwSwap : w = e + Pi.single j 1 + Pi.single i 1 :=
    add_single_add_single_comm e i j
  have hR : R = insert x C := by
    rw [show R = freudenthalSimplex u (p ++ i :: j :: s) by rfl,
      freudenthalSimplex_pair_decomposition]
    ext z
    simp [A, B, C, e, x, w]
  have hS : S = insert y C := by
    rw [show S = freudenthalSimplex u (p ++ j :: i :: s) by rfl,
      freudenthalSimplex_pair_decomposition, ← hwSwap]
    ext z
    simp [A, B, C, e, y]
  have hweightE : cumulativeWeight e =
      cumulativeWeight u + p.length :=
    cumulativeWeight_freudenthalEndpoint u p
  have hweightX : cumulativeWeight x =
      cumulativeWeight u + p.length + 1 := by
    change cumulativeWeight (e + Pi.single i 1) = _
    rw [cumulativeWeight_add_single, hweightE]
  have hweightY : cumulativeWeight y =
      cumulativeWeight u + p.length + 1 := by
    change cumulativeWeight (e + Pi.single j 1) = _
    rw [cumulativeWeight_add_single, hweightE]
  have hweightW : cumulativeWeight w =
      cumulativeWeight u + p.length + 2 := by
    change cumulativeWeight (e + Pi.single i 1 + Pi.single j 1) = _
    rw [cumulativeWeight_add_single,
      cumulativeWeight_add_single, hweightE]
    ring
  have hxA : x ∉ A := by
    intro hx
    obtain ⟨r, hr, hwr⟩ := exists_rank_of_mem_freudenthalSequence
      u p (by simpa [A, freudenthalSimplex] using hx)
    omega
  have hyA : y ∉ A := by
    intro hy
    obtain ⟨r, hr, hwr⟩ := exists_rank_of_mem_freudenthalSequence
      u p (by simpa [A, freudenthalSimplex] using hy)
    omega
  have hxB : x ∉ B := by
    intro hx
    have hle := cumulativeWeight_mono
      (freudenthalSequence_base_le_of_mem w s
        (by simpa [B, freudenthalSimplex] using hx))
    rw [hweightW, hweightX] at hle
    omega
  have hyB : y ∉ B := by
    intro hy
    have hle := cumulativeWeight_mono
      (freudenthalSequence_base_le_of_mem w s
        (by simpa [B, freudenthalSimplex] using hy))
    rw [hweightW, hweightY] at hle
    omega
  have hxC : x ∉ C := by simpa [C] using ⟨hxA, hxB⟩
  have hyC : y ∉ C := by simpa [C] using ⟨hyA, hyB⟩
  have hxy : x ≠ y := by
    intro h
    have hi := congrFun h i
    simp [x, y, e, hij] at hi
  have hperm : (p ++ i :: j :: s).Perm (p ++ j :: i :: s) :=
    List.Perm.append_left p (List.Perm.swap i j s).symm
  have hlS : (p ++ j :: i :: s).Nodup :=
    hperm.nodup_iff.mp hl
  have hlenS : (p ++ j :: i :: s).length = n :=
    hperm.length_eq.symm.trans hlen
  have hGammaS : ∀ z ∈ S, IsGammaPoint (N : ℤ) z := by
    intro z hz
    rw [hS] at hz
    rcases Finset.mem_insert.mp hz with rfl | hzC
    · simpa [y, e] using hnew
    · apply hGamma z
      rw [show freudenthalSimplex u (p ++ i :: j :: s) = R by rfl,
        hR]
      exact Finset.mem_insert_of_mem hzC
  have htopR : IsFreudenthalTopSimplex
      (realizeGammaSet N n R) := by
    apply isFreudenthalTopSimplex_realizeGammaList u
      (p ++ i :: j :: s) hl hlen
    simpa [R] using hGamma
  have htopS : IsFreudenthalTopSimplex
      (realizeGammaSet N n S) := by
    apply isFreudenthalTopSimplex_realizeGammaList u
      (p ++ j :: i :: s) hlS hlenS
    simpa [S] using hGammaS
  have hCcard : C.card = n := by
    have hRcard : R.card = n + 1 := by
      rw [show R = freudenthalSimplex u (p ++ i :: j :: s) by rfl,
        card_freudenthalSimplex_of_nodup u hl, hlen]
    rw [hR, Finset.card_insert_of_notMem hxC] at hRcard
    omega
  have hInter : (R ∩ S).card = n := by
    have hRS : R ∩ S = C := by
      rw [hR, hS]
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨(rfl | hzC), (hEq | hxMem)⟩
        · exact (hxy hEq).elim
        · exact (hxC hxMem).elim
        · exact hzC
        · exact hzC
      · intro hzC
        exact ⟨Or.inr hzC, Or.inr hzC⟩
    rw [hRS, hCcard]
  apply facetAdjacent_of_cumulative_images htopR htopS
    (image_pointPrefix_realizeGammaSet R (by
      intro z hz
      apply hGamma z
      simpa [R] using hz))
    (image_pointPrefix_realizeGammaSet S hGammaS)
  · rw [hR, hS]
    intro hrs
    have hxRight : x ∈ insert y C := by rw [← hrs]; simp
    simp [hxy, hxC] at hxRight
  · exact hInter

/-- `d` is the first coordinate at which a nonnegative cumulative vector is
strictly positive. -/
def IsFirstPositive {n : ℕ} (u : Fin n → ℤ) (d : Fin n) : Prop :=
  0 < u d ∧ ∀ j, j < d → u j = 0

/-- Decreasing the first positive coordinate preserves all defining
inequalities of `Gamma`.  At the only dangerous inequalities, whose right
endpoint is `d`, every earlier coordinate is zero. -/
theorem isGammaPoint_sub_single_of_firstPositive
    {N : ℤ} {n : ℕ} {u : Fin n → ℤ} {d : Fin n}
    (hu : IsGammaPoint N u) (hd : IsFirstPositive u d) :
    IsGammaPoint N (u - Pi.single d 1) := by
  have hdpos : 0 < u d := hd.1
  constructor
  · intro k
    simp only [Pi.sub_apply, Pi.single_apply]
    by_cases hkd : k = d
    · subst k
      rw [if_pos rfl]
      omega
    · rw [if_neg hkd]
      simpa using hu.1 k
  constructor
  · intro a b hab
    simp only [Pi.sub_apply, Pi.single_apply]
    by_cases had : a = d
    · subst a
      by_cases hbd : b = d
      · subst b
        simp
      · rw [if_pos rfl, if_neg hbd]
        have := hu.2.1 d b hab
        omega
    · rw [if_neg had]
      by_cases hbd : b = d
      · subst b
        rw [if_pos rfl]
        have hadlt : a < d := lt_of_le_of_ne hab had
        rw [hd.2 a hadlt]
        omega
      · rw [if_neg hbd]
        simpa using hu.2.1 a b hab
  · intro k
    simp only [Pi.sub_apply, Pi.single_apply]
    by_cases hkd : k = d
    · subst k
      rw [if_pos rfl]
      have := hu.2.2 d
      omega
    · rw [if_neg hkd]
      simpa using hu.2.2 k

@[simp]
theorem cumulativeWeight_sub_single {n : ℕ}
    (u : Fin n → ℤ) (d : Fin n) :
    cumulativeWeight (u - Pi.single d 1) =
      cumulativeWeight u - 1 := by
  simp [cumulativeWeight, Finset.sum_sub_distrib]

/-- Exact coordinate formula for an endpoint of a duplicate-free transfer
list: each listed coordinate has increased exactly once. -/
theorem freudenthalEndpoint_apply_of_nodup
    {n : ℕ} (u : Fin n → ℤ) {l : List (Fin n)}
    (hl : l.Nodup) (q : Fin n) :
    freudenthalEndpoint u l q =
      u q + if q ∈ l then 1 else 0 := by
  induction l generalizing u with
  | nil => simp
  | cons i l ih =>
      have hdata := List.nodup_cons.mp hl
      rw [freudenthalEndpoint_cons,
        ih (u := u + Pi.single i 1) hdata.2]
      simp only [Pi.add_apply, Pi.single_apply, List.mem_cons]
      by_cases hqi : q = i
      · subst q
        simp [hdata.1]
      · simp [hqi]

/-- Moving a full permutation of coordinates adds the all-ones vector. -/
theorem freudenthalEndpoint_eq_add_one_of_nodup_length
    {n : ℕ} (u : Fin n → ℤ) (l : List (Fin n))
    (hl : l.Nodup) (hlen : l.length = n) :
    freudenthalEndpoint u l = u + 1 := by
  funext q
  have hqmem : q ∈ l := by
    have hcard : l.toFinset.card = Fintype.card (Fin n) := by
      rw [List.toFinset_card_of_nodup hl, hlen]
      simp
    have huniv : l.toFinset = Finset.univ :=
      Finset.eq_univ_of_card l.toFinset hcard
    simp [← List.mem_toFinset, huniv]
  rw [freudenthalEndpoint_apply_of_nodup u hl q]
  simp [hqmem]

/-- If all still-unused coordinates start at the same height, Gamma
monotonicity forces their transfer order to be strictly decreasing. -/
theorem pairwise_gt_of_constant_on_valid_freudenthalSimplex
    {N c : ℤ} {n : ℕ} (u : Fin n → ℤ) (l : List (Fin n))
    (hl : l.Nodup)
    (hGamma : ∀ z ∈ freudenthalSimplex u l,
      IsGammaPoint N z)
    (hconst : ∀ q ∈ l, u q = c) :
    l.Pairwise (fun i j ↦ j < i) := by
  induction l generalizing u with
  | nil => exact List.Pairwise.nil
  | cons i l ih =>
      have hdata := List.nodup_cons.mp hl
      rw [List.pairwise_cons]
      constructor
      · intro j hj
        have hij : i ≠ j := by
          intro h
          subst j
          exact hdata.1 hj
        have hstepGamma : IsGammaPoint N
            (u + Pi.single i 1) := by
          apply hGamma (u + Pi.single i 1)
          rw [freudenthalSimplex_cons]
          exact Finset.mem_insert_of_mem
            (freudenthalBase_mem_simplex (u + Pi.single i 1) l)
        rcases lt_or_gt_of_ne hij with hijlt | hjilt
        · have hmono := hstepGamma.2.1 i j hijlt.le
          have hiConst := hconst i (by simp)
          have hjConst := hconst j (by simp [hj])
          simp [hij, hiConst, hjConst] at hmono
        · exact hjilt
      · apply ih (u := u + Pi.single i 1) hdata.2
        · intro z hz
          apply hGamma z
          rw [freudenthalSimplex_cons]
          exact Finset.mem_insert_of_mem hz
        · intro q hq
          have hqi : q ≠ i := by
            intro h
            subst q
            exact hdata.1 hq
          simp [hqi, hconst q (by simp [hq])]

/-- At cumulative base zero there is only one valid full permutation list.
This is the rigorous uniqueness of the lower-corner Freudenthal facet. -/
theorem valid_zero_base_lists_eq
    {N : ℤ} {n : ℕ} (l₁ l₂ : List (Fin n))
    (h₁nodup : l₁.Nodup) (h₂nodup : l₂.Nodup)
    (h₁len : l₁.length = n) (h₂len : l₂.length = n)
    (h₁Gamma : ∀ z ∈ freudenthalSimplex 0 l₁,
      IsGammaPoint N z)
    (h₂Gamma : ∀ z ∈ freudenthalSimplex 0 l₂,
      IsGammaPoint N z) :
    l₁ = l₂ := by
  have hmem₁ : ∀ q : Fin n, q ∈ l₁ := by
    intro q
    have hcard : l₁.toFinset.card = Fintype.card (Fin n) := by
      rw [List.toFinset_card_of_nodup h₁nodup, h₁len]
      simp
    have huniv : l₁.toFinset = Finset.univ :=
      Finset.eq_univ_of_card l₁.toFinset hcard
    simp [← List.mem_toFinset, huniv]
  have hmem₂ : ∀ q : Fin n, q ∈ l₂ := by
    intro q
    have hcard : l₂.toFinset.card = Fintype.card (Fin n) := by
      rw [List.toFinset_card_of_nodup h₂nodup, h₂len]
      simp
    have huniv : l₂.toFinset = Finset.univ :=
      Finset.eq_univ_of_card l₂.toFinset hcard
    simp [← List.mem_toFinset, huniv]
  have hperm : l₁.Perm l₂ := by
    rw [List.perm_iff_count]
    intro q
    rw [h₁nodup.count, h₂nodup.count]
    simp [hmem₁ q, hmem₂ q]
  apply List.Perm.eq_of_pairwise
    (le := fun i j : Fin n ↦ j < i) _
    (pairwise_gt_of_constant_on_valid_freudenthalSimplex
      (c := 0) 0 l₁ h₁nodup h₁Gamma (by simp))
    (pairwise_gt_of_constant_on_valid_freudenthalSimplex
      (c := 0) 0 l₂ h₂nodup h₂Gamma (by simp)) hperm
  intro a b _ _ hab hba
  exact (hab.asymm hba).elim

/-- The intermediate vertex needed to move the first positive coordinate
one position to the right remains in `Gamma`.  The proof uses duplicate
freeness to know that neither swapped coordinate has already moved, and the
first-positive property supplies the strict inequality in the local diamond. -/
theorem isGammaPoint_swapped_intermediate_of_firstPositive
    {N : ℤ} {n : ℕ} (u : Fin n → ℤ)
    (p s : List (Fin n)) (d j : Fin n)
    (hl : (p ++ d :: j :: s).Nodup)
    (hGamma : ∀ z ∈ freudenthalSimplex u (p ++ d :: j :: s),
      IsGammaPoint N z)
    (hd : IsFirstPositive u d) :
    IsGammaPoint N (freudenthalEndpoint u p + Pi.single j 1) := by
  let e := freudenthalEndpoint u p
  let w := e + Pi.single d 1 + Pi.single j 1
  have hdata := List.nodup_append.mp hl
  have htailNodup : (d :: j :: s).Nodup := hdata.2.1
  have hdNotP : d ∉ p := by
    intro hdp
    exact hdata.2.2 d hdp d (by simp) rfl
  have hjNotP : j ∉ p := by
    intro hjp
    exact hdata.2.2 j hjp j (by simp) rfl
  have hdj : d ≠ j := by
    intro hdj
    subst j
    exact (List.nodup_cons.mp htailNodup).1 (by simp)
  have heGamma : IsGammaPoint N e := by
    apply hGamma e
    rw [freudenthalSimplex_pair_decomposition]
    exact Finset.mem_union_left _
      (freudenthalEndpoint_mem_simplex u p)
  have hwGamma : IsGammaPoint N w := by
    apply hGamma w
    rw [freudenthalSimplex_pair_decomposition]
    apply Finset.mem_union_right
    apply Finset.mem_insert_of_mem
    simpa [w] using freudenthalBase_mem_simplex w s
  apply isGammaPoint_add_single_swap heGamma hdj hwGamma
  intro hjd
  have hej := freudenthalEndpoint_coordinate_eq_of_not_mem
    u p hjNotP
  have hed := freudenthalEndpoint_coordinate_eq_of_not_mem
    u p hdNotP
  change freudenthalEndpoint u p j < freudenthalEndpoint u p d
  rw [hej, hed, hd.2 j hjd]
  exact hd.1

/-- Concrete facet adjacency for one bubble-sort step moving the first
positive coordinate to the right. -/
theorem facetAdjacent_realize_bubble_firstPositive
    {N n : ℕ} (u : Fin n → ℤ) (p s : List (Fin n))
    (d j : Fin n)
    (hl : (p ++ d :: j :: s).Nodup)
    (hlen : (p ++ d :: j :: s).length = n)
    (hGamma : ∀ z ∈ freudenthalSimplex u (p ++ d :: j :: s),
      IsGammaPoint (N : ℤ) z)
    (hd : IsFirstPositive u d) :
    FacetChain.Adjacent (freudenthalFacets N n) n
      (realizeGammaSet N n
        (freudenthalSimplex u (p ++ d :: j :: s)))
      (realizeGammaSet N n
        (freudenthalSimplex u (p ++ j :: d :: s))) := by
  have htailNodup : (d :: j :: s).Nodup :=
    (List.nodup_append.mp hl).2.1
  have hdj : d ≠ j := by
    intro h
    subst j
    exact (List.nodup_cons.mp htailNodup).1 (by simp)
  exact facetAdjacent_realize_adjacent_swap u p s d j hl hlen
    hGamma hdj
    (isGammaPoint_swapped_intermediate_of_firstPositive
      u p s d j hl hGamma hd)

/-- Repeated adjacent swaps move the first positive coordinate to the end
of a full valid transfer list, producing an actual path in the facet graph. -/
theorem reflTransGen_move_firstPositive_to_end
    {N n : ℕ} (u : Fin n → ℤ) (p s : List (Fin n))
    (d : Fin n)
    (hl : (p ++ d :: s).Nodup)
    (hlen : (p ++ d :: s).length = n)
    (hGamma : ∀ z ∈ freudenthalSimplex u (p ++ d :: s),
      IsGammaPoint (N : ℤ) z)
    (hd : IsFirstPositive u d) :
    Relation.ReflTransGen
      (FacetChain.Adjacent (freudenthalFacets N n) n)
      (realizeGammaSet N n
        (freudenthalSimplex u (p ++ d :: s)))
      (realizeGammaSet N n
        (freudenthalSimplex u (p ++ s ++ [d]))) := by
  induction s generalizing p with
  | nil =>
      simpa using (Relation.ReflTransGen.refl :
        Relation.ReflTransGen
          (FacetChain.Adjacent (freudenthalFacets N n) n)
          (realizeGammaSet N n
            (freudenthalSimplex u (p ++ d :: [])))
          (realizeGammaSet N n
            (freudenthalSimplex u (p ++ d :: []))))
  | cons j s ih =>
      have hnew :=
        isGammaPoint_swapped_intermediate_of_firstPositive
          u p s d j hl hGamma hd
      have hadj := facetAdjacent_realize_bubble_firstPositive
        u p s d j hl hlen hGamma hd
      have hGammaSwap :
          ∀ z ∈ freudenthalSimplex u (p ++ j :: d :: s),
            IsGammaPoint (N : ℤ) z :=
        isGammaPoint_of_mem_freudenthalSimplex_adjacent_swap
          u p s d j hGamma hnew
      have hperm : (p ++ d :: j :: s).Perm
          (p ++ j :: d :: s) :=
        List.Perm.append_left p (List.Perm.swap d j s).symm
      have hlSwap : (p ++ j :: d :: s).Nodup :=
        hperm.nodup_iff.mp hl
      have hlenSwap : (p ++ j :: d :: s).length = n :=
        hperm.length_eq.symm.trans hlen
      have htail := ih (p := p ++ [j])
        (by simpa [List.append_assoc] using hlSwap)
        (by simpa [List.append_assoc] using hlenSwap)
        (by simpa [List.append_assoc] using hGammaSwap)
      have hadj' : FacetChain.Adjacent (freudenthalFacets N n) n
          (realizeGammaSet N n
            (freudenthalSimplex u (p ++ d :: j :: s)))
          (realizeGammaSet N n
            (freudenthalSimplex u ((p ++ [j]) ++ d :: s))) := by
        simpa [List.append_assoc] using hadj
      have hpath := Relation.ReflTransGen.head hadj' htail
      simpa [List.append_assoc] using hpath

/-- The endpoint of the bubble path remains a wholly valid Gamma simplex.
This companion to `reflTransGen_move_firstPositive_to_end` retains the
vertexwise invariant needed by the subsequent induction step. -/
theorem isGammaPoint_move_firstPositive_to_end
    {N : ℤ} {n : ℕ} (u : Fin n → ℤ) (p s : List (Fin n))
    (d : Fin n)
    (hl : (p ++ d :: s).Nodup)
    (hGamma : ∀ z ∈ freudenthalSimplex u (p ++ d :: s),
      IsGammaPoint N z)
    (hd : IsFirstPositive u d) :
    ∀ z ∈ freudenthalSimplex u (p ++ s ++ [d]),
      IsGammaPoint N z := by
  induction s generalizing p with
  | nil => simpa using hGamma
  | cons j s ih =>
      have hnew :=
        isGammaPoint_swapped_intermediate_of_firstPositive
          u p s d j hl hGamma hd
      have hGammaSwap :
          ∀ z ∈ freudenthalSimplex u (p ++ j :: d :: s),
            IsGammaPoint N z :=
        isGammaPoint_of_mem_freudenthalSimplex_adjacent_swap
          u p s d j hGamma hnew
      have hperm : (p ++ d :: j :: s).Perm
          (p ++ j :: d :: s) :=
        List.Perm.append_left p (List.Perm.swap d j s).symm
      have hlSwap : (p ++ j :: d :: s).Nodup :=
        hperm.nodup_iff.mp hl
      have hresult := ih (p := p ++ [j])
        (by simpa [List.append_assoc] using hlSwap)
        (by simpa [List.append_assoc] using hGammaSwap)
      simpa [List.append_assoc] using hresult

/-- Vertexwise Gamma validity of the decreased-base facet. -/
theorem isGammaPoint_decrease_firstPositive
    {N : ℤ} {n : ℕ} (u : Fin n → ℤ) (p : List (Fin n))
    (d : Fin n)
    (hGamma : ∀ z ∈ freudenthalSimplex u (p ++ [d]),
      IsGammaPoint N z)
    (hd : IsFirstPositive u d) :
    ∀ z ∈ freudenthalSimplex
        (u - Pi.single d 1) (d :: p),
      IsGammaPoint N z := by
  let u' := u - Pi.single d 1
  have huGamma : IsGammaPoint N u := by
    apply hGamma u
    rw [freudenthalSimplex_append_single]
    exact Finset.mem_insert_of_mem (freudenthalBase_mem_simplex u p)
  have hu'Gamma : IsGammaPoint N u' :=
    isGammaPoint_sub_single_of_firstPositive huGamma hd
  have huRestore : u' + Pi.single d 1 = u :=
    sub_single_add_single u d
  intro z hz
  rw [freudenthalSimplex_cons, huRestore] at hz
  rcases Finset.mem_insert.mp hz with rfl | hzA
  · exact hu'Gamma
  · apply hGamma z
    rw [freudenthalSimplex_append_single]
    exact Finset.mem_insert_of_mem hzA

/-- After the first positive coordinate has reached the final position, the
facet across the opposite face is based at `u - e_d` and starts by restoring
`d`.  The two facets share exactly the prefix simplex. -/
theorem facetAdjacent_realize_decrease_firstPositive
    {N n : ℕ} (u : Fin n → ℤ) (p : List (Fin n))
    (d : Fin n)
    (hl : (p ++ [d]).Nodup)
    (hlen : (p ++ [d]).length = n)
    (hGamma : ∀ z ∈ freudenthalSimplex u (p ++ [d]),
      IsGammaPoint (N : ℤ) z)
    (hd : IsFirstPositive u d) :
    FacetChain.Adjacent (freudenthalFacets N n) n
      (realizeGammaSet N n
        (freudenthalSimplex u (p ++ [d])))
      (realizeGammaSet N n
        (freudenthalSimplex (u - Pi.single d 1) (d :: p))) := by
  let u' := u - Pi.single d 1
  let A := freudenthalSimplex u p
  let x := freudenthalEndpoint u p + Pi.single d 1
  let R := freudenthalSimplex u (p ++ [d])
  let S := freudenthalSimplex u' (d :: p)
  have huGamma : IsGammaPoint (N : ℤ) u := by
    apply hGamma u
    rw [freudenthalSimplex_append_single]
    exact Finset.mem_insert_of_mem (freudenthalBase_mem_simplex u p)
  have hu'Gamma : IsGammaPoint (N : ℤ) u' := by
    exact isGammaPoint_sub_single_of_firstPositive huGamma hd
  have huRestore : u' + Pi.single d 1 = u := by
    exact sub_single_add_single u d
  have hR : R = insert x A := by
    exact freudenthalSimplex_append_single u p d
  have hS : S = insert u' A := by
    rw [show S = freudenthalSimplex u' (d :: p) by rfl,
      freudenthalSimplex_cons, huRestore]
  have hxA : x ∉ A := by
    have hweightX : cumulativeWeight x =
        cumulativeWeight u + p.length + 1 := by
      change cumulativeWeight
        (freudenthalEndpoint u p + Pi.single d 1) = _
      rw [cumulativeWeight_add_single,
        cumulativeWeight_freudenthalEndpoint]
    intro hx
    obtain ⟨r, hr, hwr⟩ := exists_rank_of_mem_freudenthalSequence
      u p (by simpa [A, freudenthalSimplex] using hx)
    omega
  have hu'NotA : u' ∉ A := by
    intro hu'A
    have hbaseLe := freudenthalSequence_base_le_of_mem u p
      (by simpa [A, freudenthalSimplex] using hu'A)
    have hcoord := hbaseLe d
    have hu'd : u' d = u d - 1 := by
      simp [u']
    have : u d ≤ u d - 1 := hcoord.trans_eq hu'd
    omega
  have hxNe : x ≠ u' := by
    intro h
    have hweightX : cumulativeWeight x =
        cumulativeWeight u + p.length + 1 := by
      change cumulativeWeight
        (freudenthalEndpoint u p + Pi.single d 1) = _
      rw [cumulativeWeight_add_single,
        cumulativeWeight_freudenthalEndpoint]
    have hweightU' : cumulativeWeight u' =
        cumulativeWeight u - 1 := by
      exact cumulativeWeight_sub_single u d
    rw [h] at hweightX
    rw [hweightU'] at hweightX
    omega
  have hAcard : A.card = n := by
    have hpNodup : p.Nodup :=
      (List.nodup_append.mp hl).1
    have hnpos : 0 < n := by
      have : 0 < (p ++ [d]).length := by simp
      omega
    have hplen : p.length = n - 1 := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    change (freudenthalSimplex u p).card = n
    rw [card_freudenthalSimplex_of_nodup u hpNodup,
      hplen]
    omega
  have hGammaS : ∀ z ∈ S,
      IsGammaPoint (N : ℤ) z := by
    intro z hz
    rw [hS] at hz
    rcases Finset.mem_insert.mp hz with rfl | hzA
    · exact hu'Gamma
    · apply hGamma z
      rw [freudenthalSimplex_append_single]
      exact Finset.mem_insert_of_mem hzA
  have htopR : IsFreudenthalTopSimplex
      (realizeGammaSet N n R) := by
    apply isFreudenthalTopSimplex_realizeGammaList
      u (p ++ [d]) hl hlen
    simpa [R] using hGamma
  have hlistPerm : (p ++ [d]).Perm (d :: p) := by
    simp
  have hlS : (d :: p).Nodup := hlistPerm.nodup_iff.mp hl
  have hlenS : (d :: p).length = n :=
    hlistPerm.length_eq.symm.trans hlen
  have htopS : IsFreudenthalTopSimplex
      (realizeGammaSet N n S) := by
    apply isFreudenthalTopSimplex_realizeGammaList
      u' (d :: p) hlS hlenS
    simpa [S] using hGammaS
  have hInter : (R ∩ S).card = n := by
    have hRS : R ∩ S = A := by
      rw [hR, hS]
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨(rfl | hzA), (hEq | hxMem)⟩
        · exact (hxNe hEq).elim
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
    simp [hxNe, hxA] at hxRight
  · exact hInter

/-- Every valid realized Freudenthal facet has a concrete adjacency path to
the unique zero-base facet.  The recursion measure is the nonnegative sum of
the cumulative base coordinates; every decrease step lowers it by exactly
one. -/
theorem exists_reflTransGen_to_zero_base
    {N n : ℕ} (u : Fin n → ℤ) (l : List (Fin n))
    (hl : l.Nodup) (hlen : l.length = n)
    (hGamma : ∀ z ∈ freudenthalSimplex u l,
      IsGammaPoint (N : ℤ) z) :
    ∃ l₀ : List (Fin n),
      l₀.Nodup ∧ l₀.length = n ∧
      (∀ z ∈ freudenthalSimplex 0 l₀,
        IsGammaPoint (N : ℤ) z) ∧
      Relation.ReflTransGen
        (FacetChain.Adjacent (freudenthalFacets N n) n)
        (realizeGammaSet N n (freudenthalSimplex u l))
        (realizeGammaSet N n (freudenthalSimplex 0 l₀)) := by
  by_cases huZero : u = 0
  · subst u
    exact ⟨l, hl, hlen, hGamma, Relation.ReflTransGen.refl⟩
  · have huGamma : IsGammaPoint (N : ℤ) u := by
      apply hGamma u
      exact freudenthalBase_mem_simplex u l
    have hexPos : ∃ q : Fin n, 0 < u q := by
      by_contra hnot
      push Not at hnot
      apply huZero
      funext q
      have hnonneg := huGamma.1 q
      have hnotpos := hnot q
      simp only [Pi.zero_apply]
      omega
    let d : Fin n := Fin.find (fun q ↦ 0 < u q) hexPos
    have hd : IsFirstPositive u d := by
      constructor
      · exact Fin.find_spec hexPos
      · intro j hj
        have hnotpos := Fin.find_min hexPos hj
        have hnonneg := huGamma.1 j
        omega
    have hdMem : d ∈ l := by
      have hcard : l.toFinset.card = Fintype.card (Fin n) := by
        rw [List.toFinset_card_of_nodup hl, hlen]
        simp
      have huniv : l.toFinset = Finset.univ :=
        Finset.eq_univ_of_card l.toFinset hcard
      simp [← List.mem_toFinset, huniv]
    obtain ⟨p, s, rfl⟩ := List.mem_iff_append.mp hdMem
    let r : List (Fin n) := p ++ s
    let u' : Fin n → ℤ := u - Pi.single d 1
    have hpathBubble := reflTransGen_move_firstPositive_to_end
      u p s d hl hlen hGamma hd
    have hGammaEnd := isGammaPoint_move_firstPositive_to_end
      u p s d hl hGamma hd
    have hEndNodup : (r ++ [d]).Nodup := by
      have hperm : (p ++ d :: s).Perm (r ++ [d]) := by
        dsimp only [r]
        exact (List.Perm.append_left p
          (List.perm_append_comm (l₁ := [d]) (l₂ := s))).trans
          (by simp [List.append_assoc])
      exact hperm.nodup_iff.mp hl
    have hEndLen : (r ++ [d]).length = n := by
      simpa [r, List.append_assoc] using hlen
    have hGammaEnd' : ∀ z ∈ freudenthalSimplex u (r ++ [d]),
        IsGammaPoint (N : ℤ) z := by
      simpa [r, List.append_assoc] using hGammaEnd
    have hadjDecrease := facetAdjacent_realize_decrease_firstPositive
      u r d hEndNodup hEndLen hGammaEnd' hd
    have hGammaDecrease := isGammaPoint_decrease_firstPositive
      u r d hGammaEnd' hd
    have hpermDecrease : (p ++ d :: s).Perm (d :: r) := by
      have h₁ : (p ++ d :: s).Perm (d :: s ++ p) := by
        simpa [List.append_assoc] using
          (List.perm_append_comm (l₁ := p) (l₂ := d :: s))
      have h₂ : (d :: s ++ p).Perm (d :: p ++ s) :=
        List.Perm.cons d
          (List.perm_append_comm (l₁ := s) (l₂ := p))
      simp [r]
    have hlDecrease : (d :: r).Nodup :=
      hpermDecrease.nodup_iff.mp hl
    have hlenDecrease : (d :: r).length = n :=
      hpermDecrease.length_eq.symm.trans hlen
    obtain ⟨l₀, hl₀, hlen₀, hGamma₀, hpathRec⟩ :=
      exists_reflTransGen_to_zero_base u' (d :: r)
        hlDecrease hlenDecrease (by simpa [u'] using hGammaDecrease)
    refine ⟨l₀, hl₀, hlen₀, hGamma₀, ?_⟩
    have hpathBubble' : Relation.ReflTransGen
        (FacetChain.Adjacent (freudenthalFacets N n) n)
        (realizeGammaSet N n
          (freudenthalSimplex u (p ++ d :: s)))
        (realizeGammaSet N n
          (freudenthalSimplex u (r ++ [d]))) := by
      simpa [r, List.append_assoc] using hpathBubble
    have hstep := Relation.ReflTransGen.single hadjDecrease
    exact hpathBubble'.trans (hstep.trans (by
      simpa [u'] using hpathRec))
termination_by Int.toNat (cumulativeWeight u)
decreasing_by
  have hsumPos : 0 < cumulativeWeight u := by
    have hsumNonneg : 0 ≤ cumulativeWeight u := by
      exact Finset.sum_nonneg fun q _ ↦ huGamma.1 q
    have hdpos := hd.1
    have hsumGe : u d ≤ cumulativeWeight u := by
      rw [cumulativeWeight]
      exact Finset.single_le_sum (fun q _ ↦ huGamma.1 q)
        (Finset.mem_univ d)
    omega
  apply (Int.toNat_lt_toNat hsumPos).2
  rw [cumulativeWeight_sub_single]
  omega

/-- Every abstract top simplex has an exact realization by a duplicate-free
full transfer list, with Gamma validity proved for every listed vertex. -/
theorem exists_valid_realization_of_topSimplex
    {N n : ℕ} {rho : Finset (Point N n)}
    (hrho : IsFreudenthalTopSimplex rho) :
    ∃ (u : Fin n → ℤ) (l : List (Fin n)),
      l.Nodup ∧ l.length = n ∧
      (∀ z ∈ freudenthalSimplex u l,
        IsGammaPoint (N : ℤ) z) ∧
      rho = realizeGammaSet N n (freudenthalSimplex u l) := by
  obtain ⟨u, omega, himage⟩ :=
    (isFreudenthalTopSimplex_iff_cumulative rho).1 hrho
  let l := permutationList omega
  have hl : l.Nodup := nodup_permutationList omega
  have hlen : l.length = n := length_permutationList omega
  have hGamma : ∀ z ∈ freudenthalSimplex u l,
      IsGammaPoint (N : ℤ) z := by
    intro z hz
    have hzImage : z ∈ rho.image pointPrefix := by
      rw [himage]
      simpa [l] using hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzImage
    exact pointPrefix_isGammaPoint a
  refine ⟨u, l, hl, hlen, hGamma, ?_⟩
  apply Finset.image_injective pointPrefix_injective
  rw [himage]
  exact (image_pointPrefix_realizeGammaSet
    (freudenthalSimplex u l) hGamma).symm

/-- Facet adjacency is symmetric, including all membership and exact-cardinal
data in its definition. -/
theorem facetAdjacent_symm {N n : ℕ}
    {rho sigma : Finset (Point N n)}
    (h : FacetChain.Adjacent (freudenthalFacets N n) n rho sigma) :
    FacetChain.Adjacent (freudenthalFacets N n) n sigma rho := by
  exact ⟨h.2.1, h.1, h.2.2.1.symm, by
    simpa [Finset.inter_comm] using h.2.2.2⟩

/-- The concrete Freudenthal facet set is strongly connected through genuine
codimension-one adjacencies.  This closes the last combinatorial hypothesis
needed by the chain-uniqueness theorem; no connectivity axiom is assumed. -/
theorem freudenthalFacets_stronglyFacetConnected (N n : ℕ) :
    FacetChain.StronglyFacetConnected (freudenthalFacets N n) n := by
  intro rho hrho sigma hsigma
  have hrhoTop := (mem_freudenthalFacets_iff rho).1 hrho
  have hsigmaTop := (mem_freudenthalFacets_iff sigma).1 hsigma
  obtain ⟨u, l, hl, hlen, hGamma, hrhoEq⟩ :=
    exists_valid_realization_of_topSimplex hrhoTop
  obtain ⟨v, m, hm, hmlen, hmGamma, hsigmaEq⟩ :=
    exists_valid_realization_of_topSimplex hsigmaTop
  obtain ⟨l₀, hl₀, hl₀len, hl₀Gamma, hpathRho⟩ :=
    exists_reflTransGen_to_zero_base u l hl hlen hGamma
  obtain ⟨m₀, hm₀, hm₀len, hm₀Gamma, hpathSigma⟩ :=
    exists_reflTransGen_to_zero_base v m hm hmlen hmGamma
  have hzeroLists : l₀ = m₀ :=
    valid_zero_base_lists_eq l₀ m₀ hl₀ hm₀
      hl₀len hm₀len hl₀Gamma hm₀Gamma
  subst m₀
  rw [hrhoEq, hsigmaEq]
  have hreverseSwap : Relation.ReflTransGen
      (Function.swap
        (FacetChain.Adjacent (freudenthalFacets N n) n))
      (realizeGammaSet N n (freudenthalSimplex 0 l₀))
      (realizeGammaSet N n (freudenthalSimplex v m)) :=
    (Relation.reflTransGen_swap).2 hpathSigma
  have hreverse : Relation.ReflTransGen
      (FacetChain.Adjacent (freudenthalFacets N n) n)
      (realizeGammaSet N n (freudenthalSimplex 0 l₀))
      (realizeGammaSet N n (freudenthalSimplex v m)) := by
    exact (Relation.ReflTransGen.mono
      (r := Function.swap
        (FacetChain.Adjacent (freudenthalFacets N n) n))
      (p := FacetChain.Adjacent (freudenthalFacets N n) n)
      (fun _ _ hab ↦ facetAdjacent_symm hab)) _ _ hreverseSwap
  exact hpathRho.trans hreverse

/-- With connectivity now concrete, the positive-dimensional top-chain
uniqueness step needs only the scale assumptions and the inductive boundary
identity. -/
theorem associatedTopChain_eq_freudenthalTopChain_of_boundary_eq_of_pos
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (hboundaryEq :
      SimplexFamily.boundary (associatedTopChain N n) =
        SimplexFamily.boundary (freudenthalTopChain N n)) :
    associatedTopChain N n = freudenthalTopChain N n := by
  exact associatedTopChain_eq_freudenthalTopChain_of_boundary_eq
    (freudenthalFacets_nonbranching hn)
    (freudenthalFacets_stronglyFacetConnected N n)
    (freudenthalFacets_hasNonemptyBoundary_of_pos hN hn)
    hboundaryEq

/-- Positive-dimensional Theorem 4.8 has likewise been reduced to its
dimension-lowering boundary identity; nonbranching, connectivity, and
nonempty boundary are no longer interface hypotheses. -/
theorem associatedComplex_eq_freudenthalComplex_of_boundary_eq_of_pos
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (hboundaryEq :
      SimplexFamily.boundary (associatedTopChain N n) =
        SimplexFamily.boundary (freudenthalTopChain N n)) :
    (pointOrders N n).associatedComplex Finset.univ =
      freudenthalComplex N n := by
  apply associatedComplex_eq_freudenthalComplex_of_topChain_eq
  exact associatedTopChain_eq_freudenthalTopChain_of_boundary_eq_of_pos
    hN hn hboundaryEq

end IntegerSimplex

end BeyondSperner
