import BeyondSperner.Freudenthal.IntegerSimplex
import Mathlib.Data.Finset.Sort

/-!
# Classification of full cells in the integer simplex

This file contains the genuinely combinatorial layer of Section 4, separated
from the coordinate arithmetic in `IntegerSimplex`.  In particular, an
arbitrary list of vertices is never treated as the ordered list of a cell:
`cellOrderVertex` is the canonical increasing enumeration supplied by the
chosen cyclic linear order.
-/

namespace BeyondSperner

open Classical

namespace IntegerSimplex

variable {N n : ℕ} {σ : Finset (Point N n)}

theorem fullCell_card
    (hcell : (pointOrders N n).IsCell σ Finset.univ) :
    σ.card = n + 1 := by
  simpa using hcell.2

theorem fullCell_nonempty
    (hcell : (pointOrders N n).IsCell σ Finset.univ) :
    σ.Nonempty := by
  apply Finset.card_pos.mp
  rw [fullCell_card hcell]
  omega

/-- The minimum of a full cell in its `i`-th cyclic order. -/
noncomputable def cellMinimum
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) : Point N n :=
  @Finset.min' (Point N n) ((pointOrders N n) i) σ
    (fullCell_nonempty hcell)

theorem cellMinimum_mem
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) : cellMinimum hcell i ∈ σ := by
  exact @Finset.min'_mem (Point N n) ((pointOrders N n) i) σ
    (fullCell_nonempty hcell)

theorem cellMinimum_le
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) {x : Point N n} (hx : x ∈ σ) :
    ((pointOrders N n) i).le (cellMinimum hcell i) x := by
  exact @Finset.min'_le (Point N n) ((pointOrders N n) i) σ x hx

/-- The minimum map, with its mathematically correct codomain restricted to
the vertices of the cell. -/
noncomputable def cellMinimumEquiv
    (hcell : (pointOrders N n).IsCell σ Finset.univ) :
    Fin (n + 1) ≃ {x : Point N n // x ∈ σ} := by
  let f : Fin (n + 1) → {x : Point N n // x ∈ σ} := fun i ↦
    ⟨cellMinimum hcell i, cellMinimum_mem hcell i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    have hv : cellMinimum hcell i = cellMinimum hcell j :=
      congrArg Subtype.val h
    have himage : σ = Finset.univ.image
        (fun r : Fin (n + 1) ↦ cellMinimum hcell r) := by
      simpa [cellMinimum] using
        (pointOrders N n).eq_image_min_of_isDominant
          (fullCell_nonempty hcell) hcell.1
    have hcardImage :
        ((Finset.univ : Finset (Fin (n + 1))).image
          (fun r ↦ cellMinimum hcell r)).card =
          (Finset.univ : Finset (Fin (n + 1))).card := by
      rw [← himage]
      simpa using hcell.2
    exact (Finset.injOn_of_card_image_eq hcardImage)
      (Finset.mem_univ i) (Finset.mem_univ j) hv
  · rintro ⟨x, hx⟩
    have himage : σ = Finset.univ.image
        (fun r : Fin (n + 1) ↦ cellMinimum hcell r) := by
      simpa [cellMinimum] using
        (pointOrders N n).eq_image_min_of_isDominant
          (fullCell_nonempty hcell) hcell.1
    rw [himage] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i, rfl⟩

/-- Canonical increasing enumeration of the cell in cyclic order `i`. -/
noncomputable def cellOrderVertex
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r : Fin (n + 1)) : Point N n := by
  letI : LinearOrder (Point N n) := (pointOrders N n) i
  exact (σ.orderIsoOfFin (fullCell_card hcell) r).1

theorem cellOrderVertex_mem
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r : Fin (n + 1)) : cellOrderVertex hcell i r ∈ σ := by
  let : LinearOrder (Point N n) := (pointOrders N n) i
  exact (σ.orderIsoOfFin (fullCell_card hcell) r).2

theorem cellOrderVertex_injective
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) :
    Function.Injective (cellOrderVertex hcell i) := by
  intro r s h
  let : LinearOrder (Point N n) := (pointOrders N n) i
  apply (σ.orderIsoOfFin (fullCell_card hcell)).injective
  apply Subtype.ext
  exact h

theorem cellOrderVertex_surjective_on
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) {x : Point N n} (hx : x ∈ σ) :
    ∃ r, cellOrderVertex hcell i r = x := by
  let : LinearOrder (Point N n) := (pointOrders N n) i
  let y : {z : Point N n // z ∈ σ} := ⟨x, hx⟩
  refine ⟨(σ.orderIsoOfFin (fullCell_card hcell)).symm y, ?_⟩
  simp [cellOrderVertex, y]

theorem cellOrderVertex_lt_iff
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r s : Fin (n + 1)) :
    ((pointOrders N n) i).lt (cellOrderVertex hcell i r)
      (cellOrderVertex hcell i s) ↔ r < s := by
  let : LinearOrder (Point N n) := (pointOrders N n) i
  change cellOrderVertex hcell i r < cellOrderVertex hcell i s ↔ r < s
  simp [cellOrderVertex]

theorem cellOrderVertex_le_iff
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r s : Fin (n + 1)) :
    ((pointOrders N n) i).le (cellOrderVertex hcell i r)
      (cellOrderVertex hcell i s) ↔ r ≤ s := by
  let : LinearOrder (Point N n) := (pointOrders N n) i
  change cellOrderVertex hcell i r ≤ cellOrderVertex hcell i s ↔ r ≤ s
  simp [cellOrderVertex]

theorem cellOrderVertex_zero_eq_minimum
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) :
    cellOrderVertex hcell i 0 = cellMinimum hcell i := by
  let : LinearOrder (Point N n) := (pointOrders N n) i
  apply le_antisymm
  · obtain ⟨r, hr⟩ := cellOrderVertex_surjective_on hcell i
      (cellMinimum_mem hcell i)
    rw [← hr]
    exact (cellOrderVertex_le_iff hcell i 0 r).2 (Fin.zero_le r)
  · exact cellMinimum_le hcell i (cellOrderVertex_mem hcell i 0)

/-- The canonical order enumeration, now packaged as an equivalence onto the
cell rather than onto the entire ambient point set. -/
noncomputable def cellOrderEquiv
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) : Fin (n + 1) ≃ {x : Point N n // x ∈ σ} := by
  let f : Fin (n + 1) → {x : Point N n // x ∈ σ} := fun r ↦
    ⟨cellOrderVertex hcell i r, cellOrderVertex_mem hcell i r⟩
  apply Equiv.ofBijective f
  constructor
  · intro r s h
    apply cellOrderVertex_injective hcell i
    exact congrArg Subtype.val h
  · rintro ⟨x, hx⟩
    obtain ⟨r, rfl⟩ := cellOrderVertex_surjective_on hcell i hx
    exact ⟨r, rfl⟩

@[simp]
theorem cellOrderEquiv_apply
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r : Fin (n + 1)) :
    (cellOrderEquiv hcell i r).1 = cellOrderVertex hcell i r := by
  rfl

@[simp]
theorem cellMinimumEquiv_apply
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) :
    (cellMinimumEquiv hcell i).1 = cellMinimum hcell i := by
  rfl

/-- The permutation assigning to each vertex in increasing `i`-order the
unique order for which that vertex is the minimum.  For `i = 0` this is the
permutation denoted `ι` in Theorem 4.5. -/
noncomputable def cellIndexPermutation
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (cellOrderEquiv hcell i).trans (cellMinimumEquiv hcell).symm

theorem cellIndexPermutation_spec
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r : Fin (n + 1)) :
    cellMinimum hcell (cellIndexPermutation hcell i r) =
      cellOrderVertex hcell i r := by
  have h := (cellMinimumEquiv hcell).apply_symm_apply
    (cellOrderEquiv hcell i r)
  exact congrArg Subtype.val h

@[simp]
theorem cellIndexPermutation_zero_zero
    (hcell : (pointOrders N n).IsCell σ Finset.univ) :
    cellIndexPermutation hcell 0 0 = 0 := by
  apply (cellMinimumEquiv hcell).injective
  apply Subtype.ext
  change cellMinimum hcell (cellIndexPermutation hcell 0 0) =
    cellMinimum hcell 0
  rw [cellIndexPermutation_spec,
    cellOrderVertex_zero_eq_minimum]

/-- Position, in increasing `i`-order, of the minimum for order `j`. -/
noncomputable def cellCut
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i j : Fin (n + 1)) : Fin (n + 1) :=
  (cellOrderEquiv hcell i).symm (cellMinimumEquiv hcell j)

theorem cellOrderVertex_cut_eq_minimum
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i j : Fin (n + 1)) :
    cellOrderVertex hcell i (cellCut hcell i j) = cellMinimum hcell j := by
  have h := (cellOrderEquiv hcell i).apply_symm_apply
    (cellMinimumEquiv hcell j)
  exact congrArg Subtype.val h

theorem cellCut_ne_zero_of_ne
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    {i j : Fin (n + 1)} (hij : i ≠ j) :
    cellCut hcell i j ≠ 0 := by
  intro hzero
  apply hij
  apply (cellMinimumEquiv hcell).injective
  apply Subtype.ext
  change cellMinimum hcell i = cellMinimum hcell j
  rw [← cellOrderVertex_zero_eq_minimum hcell i,
    ← cellOrderVertex_cut_eq_minimum hcell i j, hzero]

/-- The first coordinate of a lexicographically increasing enumeration is
monotone. -/
theorem cellOrderVertex_coord_mono
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) :
    Monotone (fun r ↦ pointCoords (cellOrderVertex hcell i r) i) := by
  intro r s hrs
  by_contra hcoord
  have hrev : pointCoords (cellOrderVertex hcell i s) i <
      pointCoords (cellOrderVertex hcell i r) i := lt_of_not_ge hcoord
  have hlt := pointOrders_refines i hrev
  have hle := (cellOrderVertex_le_iff hcell i r s).2 hrs
  change cyclicKey i (pointCoords (cellOrderVertex hcell i s)) <
    cyclicKey i (pointCoords (cellOrderVertex hcell i r)) at hlt
  change cyclicKey i (pointCoords (cellOrderVertex hcell i r)) ≤
    cyclicKey i (pointCoords (cellOrderVertex hcell i s)) at hle
  exact (not_lt_of_ge hle) hlt

/-- By Lemmas 4.2--4.3, every primary coordinate on an ordered full cell is
either its initial value or that value plus one. -/
theorem cellOrderVertex_coord_eq_low_or_high (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r : Fin (n + 1)) :
    pointCoords (cellOrderVertex hcell i r) i =
        pointCoords (cellOrderVertex hcell i 0) i ∨
      pointCoords (cellOrderVertex hcell i r) i =
        pointCoords (cellOrderVertex hcell i 0) i + 1 := by
  have hlo := cellOrderVertex_coord_mono hcell i (Fin.zero_le r)
  have hrange := coord_range_of_isCell hn hcell
    (cellOrderVertex_mem hcell i 0) (cellOrderVertex_mem hcell i r) i
  change pointCoords (cellOrderVertex hcell i 0) i ≤
    pointCoords (cellOrderVertex hcell i r) i at hlo
  omega

theorem exists_cellOrderVertex_coord_high (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) :
    ∃ r, pointCoords (cellOrderVertex hcell i r) i =
      pointCoords (cellOrderVertex hcell i 0) i + 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_pair_coord_ne_of_isCell hn hcell i
  obtain ⟨r, hr⟩ := cellOrderVertex_surjective_on hcell i ha
  obtain ⟨s, hs⟩ := cellOrderVertex_surjective_on hcell i hb
  have hrCases := cellOrderVertex_coord_eq_low_or_high hn hcell i r
  have hsCases := cellOrderVertex_coord_eq_low_or_high hn hcell i s
  rcases hrCases with hrLow | hrHigh
  · rcases hsCases with hsLow | hsHigh
    · exfalso
      apply hab
      rw [← hr, ← hs]
      exact hrLow.trans hsLow.symm
    · exact ⟨s, hsHigh⟩
  · exact ⟨r, hrHigh⟩

/-- The cut at the next cyclic order belongs to the high-coordinate block. -/
theorem cellCut_next_coord_high (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) :
    pointCoords
        (cellOrderVertex hcell i (cellCut hcell i (finRotate _ i))) i =
      pointCoords (cellOrderVertex hcell i 0) i + 1 := by
  let j : Fin (n + 1) := finRotate _ i
  have hij : i ≠ j := by
    by_cases hilast : i = Fin.last n
    · subst i
      simp only [j, finRotate_last]
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    · exact ne_of_lt ((lt_finRotate_iff_ne_last i).2 hilast)
  let c : Fin (n + 1) := cellCut hcell i j
  have hc0 : c ≠ 0 := cellCut_ne_zero_of_ne hcell hij
  have hcases := cellOrderVertex_coord_eq_low_or_high hn hcell i c
  rcases hcases with hlow | hhigh
  · have h0c : (0 : Fin (n + 1)) < c := Fin.pos_iff_ne_zero.mpr hc0
    have hlt_i := (cellOrderVertex_lt_iff hcell i 0 c).2 h0c
    change cyclicKey i (pointCoords (cellOrderVertex hcell i 0)) <
      cyclicKey i (pointCoords (cellOrderVertex hcell i c)) at hlt_i
    have hlt_j : cyclicKey j (pointCoords (cellOrderVertex hcell i 0)) <
        cyclicKey j (pointCoords (cellOrderVertex hcell i c)) := by
      exact (cyclicKey_lt_iff_next_of_eq i hlow.symm).mp hlt_i
    have hminle := cellMinimum_le hcell j
      (cellOrderVertex_mem hcell i 0)
    rw [← cellOrderVertex_cut_eq_minimum hcell i j] at hminle
    change cyclicKey j (pointCoords (cellOrderVertex hcell i c)) ≤
      cyclicKey j (pointCoords (cellOrderVertex hcell i 0)) at hminle
    exact (not_le_of_gt hlt_j hminle).elim
  · simpa [j, c] using hhigh

/-- Exact low/high block decomposition at the next-order cut. -/
theorem cellOrderVertex_coord_low_iff_lt_cut (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r : Fin (n + 1)) :
    pointCoords (cellOrderVertex hcell i r) i =
        pointCoords (cellOrderVertex hcell i 0) i ↔
      r < cellCut hcell i (finRotate _ i) := by
  let j : Fin (n + 1) := finRotate _ i
  let c : Fin (n + 1) := cellCut hcell i j
  have hcutHigh : pointCoords (cellOrderVertex hcell i c) i =
      pointCoords (cellOrderVertex hcell i 0) i + 1 := by
    simpa [j, c] using cellCut_next_coord_high hn hcell i
  constructor
  · intro hlow
    by_contra hnot
    have hcr : c ≤ r := le_of_not_gt hnot
    have hmono := cellOrderVertex_coord_mono hcell i hcr
    change pointCoords (cellOrderVertex hcell i c) i ≤
      pointCoords (cellOrderVertex hcell i r) i at hmono
    omega
  · intro hrc
    rcases cellOrderVertex_coord_eq_low_or_high hn hcell i r with hlow | hhigh
    · exact hlow
    · have hlt_i := (cellOrderVertex_lt_iff hcell i r c).2 hrc
      change cyclicKey i (pointCoords (cellOrderVertex hcell i r)) <
        cyclicKey i (pointCoords (cellOrderVertex hcell i c)) at hlt_i
      have heq : pointCoords (cellOrderVertex hcell i r) i =
          pointCoords (cellOrderVertex hcell i c) i := by omega
      have hlt_j : cyclicKey j (pointCoords (cellOrderVertex hcell i r)) <
          cyclicKey j (pointCoords (cellOrderVertex hcell i c)) := by
        exact (cyclicKey_lt_iff_next_of_eq i heq).mp hlt_i
      have hminle := cellMinimum_le hcell j
        (cellOrderVertex_mem hcell i r)
      rw [← cellOrderVertex_cut_eq_minimum hcell i j] at hminle
      change cyclicKey j (pointCoords (cellOrderVertex hcell i c)) ≤
        cyclicKey j (pointCoords (cellOrderVertex hcell i r)) at hminle
      exact (not_le_of_gt hlt_j hminle).elim

theorem cellOrderVertex_coord_high_iff_cut_le (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r : Fin (n + 1)) :
    pointCoords (cellOrderVertex hcell i r) i =
        pointCoords (cellOrderVertex hcell i 0) i + 1 ↔
      cellCut hcell i (finRotate _ i) ≤ r := by
  have hcases := cellOrderVertex_coord_eq_low_or_high hn hcell i r
  have hlowIff := cellOrderVertex_coord_low_iff_lt_cut hn hcell i r
  omega

private theorem rotate_ne_self_of_pos (hn : 0 < n) (i : Fin (n + 1)) :
    finRotate _ i ≠ i := by
  by_cases hilast : i = Fin.last n
  · subst i
    rw [finRotate_last]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  · exact ne_of_gt ((lt_finRotate_iff_ne_last i).2 hilast)

private theorem rotate_symm_ne_self_of_pos (hn : 0 < n)
    (i : Fin (n + 1)) : (finRotate _).symm i ≠ i := by
  intro h
  have hr := congrArg (finRotate (n + 1)) h
  simp only [Equiv.apply_symm_apply] at hr
  exact rotate_ne_self_of_pos hn i hr.symm

/-- The wrap comparison in Lemma 4.4.  In the next cyclic order, the final
high-coordinate vertex precedes the initial low-coordinate vertex. -/
theorem cellOrderVertex_last_lt_next_zero (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) :
    ((pointOrders N n) (finRotate _ i)).lt
      (cellOrderVertex hcell i (Fin.last n))
      (cellOrderVertex hcell i 0) := by
  let j : Fin (n + 1) := finRotate _ i
  let x0 : Point N n := cellOrderVertex hcell i 0
  let xl : Point N n := cellOrderVertex hcell i (Fin.last n)
  have hij : j ≠ i := rotate_ne_self_of_pos hn i
  have hcut0 : cellCut hcell i j ≠ 0 :=
    cellCut_ne_zero_of_ne hcell hij.symm
  have hx0Low : pointCoords x0 i = pointCoords x0 i := rfl
  have hlastHigh : pointCoords xl i = pointCoords x0 i + 1 := by
    have := (cellOrderVertex_coord_high_iff_cut_le hn hcell i (Fin.last n)).2
      (Fin.le_last _)
    simpa [j, x0, xl] using this
  have hpos : 0 < pointCoords xl i := by
    have hnonneg := (pointCoords_isPoint x0).1 i
    omega
  let hzPoint := cyclicStep_isPoint hn i (pointCoords xl)
    (pointCoords_isPoint xl) hpos
  let z : Point N n := pointOfIsPoint (cyclicStep i (pointCoords xl)) hzPoint
  have hzcoords : pointCoords z = cyclicStep i (pointCoords xl) :=
    pointCoords_pointOfIsPoint _ _
  have hpi : (finRotate _).symm i ≠ i :=
    rotate_symm_ne_self_of_pos hn i
  have hcoord0z : pointCoords x0 i = pointCoords z i := by
    rw [hzcoords, cyclicStep_apply, if_neg hpi.symm, if_pos rfl]
    omega
  change cyclicKey j (pointCoords xl) < cyclicKey j (pointCoords x0)
  by_contra hnot
  have hxl0 : xl ≠ x0 := by
    intro h
    have hind := cellOrderVertex_injective hcell i h
    have hv := congrArg Fin.val hind
    simp at hv
    omega
  have hkeyNe : cyclicKey j (pointCoords x0) ≠ cyclicKey j (pointCoords xl) := by
    intro h
    apply hxl0.symm
    apply pointCoords_injective
    exact cyclicKey_injective j h
  have h0l : cyclicKey j (pointCoords x0) < cyclicKey j (pointCoords xl) :=
    lt_of_le_of_ne (le_of_not_gt hnot) hkeyNe
  have hlzj : cyclicKey j (pointCoords xl) < cyclicKey j (pointCoords z) := by
    rw [hzcoords]
    exact cyclicKey_lt_cyclicStep_of_ne hn i j hij (pointCoords xl)
  have h0zj : cyclicKey j (pointCoords x0) < cyclicKey j (pointCoords z) :=
    h0l.trans hlzj
  have h0zi : cyclicKey i (pointCoords x0) < cyclicKey i (pointCoords z) :=
    (cyclicKey_lt_iff_next_of_eq i hcoord0z).mpr h0zj
  obtain ⟨d, _, hdz⟩ := hcell.1.2 z
  by_cases hdi : d = i
  · subst d
    have hzle := hdz x0 (cellOrderVertex_mem hcell i 0)
    change cyclicKey i (pointCoords z) ≤ cyclicKey i (pointCoords x0) at hzle
    exact (not_le_of_gt h0zi) hzle
  · have hlzd : cyclicKey d (pointCoords xl) < cyclicKey d (pointCoords z) := by
      rw [hzcoords]
      exact cyclicKey_lt_cyclicStep_of_ne hn i d hdi (pointCoords xl)
    have hzle := hdz xl (cellOrderVertex_mem hcell i (Fin.last n))
    change cyclicKey d (pointCoords z) ≤ cyclicKey d (pointCoords xl) at hzle
    exact (not_le_of_gt hlzd) hzle

/-- Every vertex in the high block precedes every vertex in the low block
after passing to the next cyclic order. -/
theorem cellOrderVertex_high_lt_next_low (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i u v : Fin (n + 1))
    (hu : cellCut hcell i (finRotate _ i) ≤ u)
    (hv : v < cellCut hcell i (finRotate _ i)) :
    ((pointOrders N n) (finRotate _ i)).lt
      (cellOrderVertex hcell i u) (cellOrderVertex hcell i v) := by
  let j : Fin (n + 1) := finRotate _ i
  have huHigh := (cellOrderVertex_coord_high_iff_cut_le hn hcell i u).2 hu
  have hlastHigh :=
    (cellOrderVertex_coord_high_iff_cut_le hn hcell i (Fin.last n)).2
      (Fin.le_last _)
  have hvLow := (cellOrderVertex_coord_low_iff_lt_cut hn hcell i v).2 hv
  have hzeroLow :=
    (cellOrderVertex_coord_low_iff_lt_cut hn hcell i 0).2
      (Fin.pos_iff_ne_zero.mpr
        (cellCut_ne_zero_of_ne hcell (rotate_ne_self_of_pos hn i).symm))
  have huLast : cyclicKey j (pointCoords (cellOrderVertex hcell i u)) ≤
      cyclicKey j (pointCoords (cellOrderVertex hcell i (Fin.last n))) := by
    by_cases hulast : u = Fin.last n
    · subst u
      exact le_rfl
    · have hult : u < Fin.last n := Fin.lt_last_iff_ne_last.mpr hulast
      have hlt_i := (cellOrderVertex_lt_iff hcell i u (Fin.last n)).2 hult
      change cyclicKey i (pointCoords (cellOrderVertex hcell i u)) <
        cyclicKey i (pointCoords (cellOrderVertex hcell i (Fin.last n))) at hlt_i
      have heq : pointCoords (cellOrderVertex hcell i u) i =
          pointCoords (cellOrderVertex hcell i (Fin.last n)) i := by omega
      exact le_of_lt ((cyclicKey_lt_iff_next_of_eq i heq).mp hlt_i)
  have hlastZero : cyclicKey j
      (pointCoords (cellOrderVertex hcell i (Fin.last n))) <
      cyclicKey j (pointCoords (cellOrderVertex hcell i 0)) := by
    exact cellOrderVertex_last_lt_next_zero hn hcell i
  have hzeroV : cyclicKey j (pointCoords (cellOrderVertex hcell i 0)) ≤
      cyclicKey j (pointCoords (cellOrderVertex hcell i v)) := by
    by_cases hvzero : v = 0
    · subst v
      exact le_rfl
    · have h0v : (0 : Fin (n + 1)) < v := Fin.pos_iff_ne_zero.mpr hvzero
      have hlt_i := (cellOrderVertex_lt_iff hcell i 0 v).2 h0v
      change cyclicKey i (pointCoords (cellOrderVertex hcell i 0)) <
        cyclicKey i (pointCoords (cellOrderVertex hcell i v)) at hlt_i
      have heq : pointCoords (cellOrderVertex hcell i 0) i =
          pointCoords (cellOrderVertex hcell i v) i := by omega
      exact le_of_lt ((cyclicKey_lt_iff_next_of_eq i heq).mp hlt_i)
  change cyclicKey j (pointCoords (cellOrderVertex hcell i u)) <
    cyclicKey j (pointCoords (cellOrderVertex hcell i v))
  exact huLast.trans_lt (hlastZero.trans_le hzeroV)

private theorem finCycle_order_cases {n : ℕ}
    (c r s : Fin (n + 1)) (hrs : r < s) :
    (c ≤ finCycle c r ∧ c ≤ finCycle c s ∧ finCycle c r < finCycle c s) ∨
      (finCycle c r < c ∧ finCycle c s < c ∧ finCycle c r < finCycle c s) ∨
      (c ≤ finCycle c r ∧ finCycle c s < c) := by
  by_cases hrw : n + 1 ≤ r.val + c.val
  · have hsw : n + 1 ≤ s.val + c.val := by omega
    right
    left
    constructor
    · change (finCycle c r).val < c.val
      rw [finCycle_apply]
      simp only [Fin.val_add_eq_ite, hrw, if_pos]
      omega
    constructor
    · change (finCycle c s).val < c.val
      rw [finCycle_apply]
      simp only [Fin.val_add_eq_ite, hsw, if_pos]
      omega
    · change (finCycle c r).val < (finCycle c s).val
      rw [finCycle_apply, finCycle_apply]
      simp only [Fin.val_add_eq_ite, hrw, hsw, if_pos]
      omega
  · by_cases hsw : n + 1 ≤ s.val + c.val
    · right
      right
      constructor
      · change c.val ≤ (finCycle c r).val
        rw [finCycle_apply]
        simp [Fin.val_add_eq_ite, hrw]
      · change (finCycle c s).val < c.val
        rw [finCycle_apply]
        simp only [Fin.val_add_eq_ite, hsw, if_pos]
        omega
    · left
      constructor
      · change c.val ≤ (finCycle c r).val
        rw [finCycle_apply]
        simp [Fin.val_add_eq_ite, hrw]
      constructor
      · change c.val ≤ (finCycle c s).val
        rw [finCycle_apply]
        simp [Fin.val_add_eq_ite, hsw]
      · change (finCycle c r).val < (finCycle c s).val
        rw [finCycle_apply, finCycle_apply]
        simp [Fin.val_add_eq_ite, hrw, hsw]
        omega

/-- The full content of the cyclic-order assertion in Lemma 4.4: the
increasing enumeration for the next order is obtained by rotating the current
enumeration so that the next minimum is first. -/
theorem cellOrderVertex_next_eq_rotate (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i r : Fin (n + 1)) :
    cellOrderVertex hcell (finRotate _ i) r =
      cellOrderVertex hcell i
        (finCycle (cellCut hcell i (finRotate _ i)) r) := by
  let j : Fin (n + 1) := finRotate _ i
  let c : Fin (n + 1) := cellCut hcell i j
  let f : Fin (n + 1) → Point N n := fun q ↦
    cellOrderVertex hcell i (finCycle c q)
  let : LinearOrder (Point N n) := (pointOrders N n) j
  have hfmem : ∀ q, f q ∈ σ := fun q ↦
    cellOrderVertex_mem hcell i (finCycle c q)
  have hfmono : StrictMono f := by
    intro q t hqt
    rcases finCycle_order_cases c q t hqt with hhigh | hlow | hcross
    · obtain ⟨hqc, htc, hqtl⟩ := hhigh
      have hqHigh := (cellOrderVertex_coord_high_iff_cut_le hn hcell i
        (finCycle c q)).2 (by simpa [c, j] using hqc)
      have htHigh := (cellOrderVertex_coord_high_iff_cut_le hn hcell i
        (finCycle c t)).2 (by simpa [c, j] using htc)
      have hlt_i := (cellOrderVertex_lt_iff hcell i
        (finCycle c q) (finCycle c t)).2 hqtl
      change cyclicKey i (pointCoords (cellOrderVertex hcell i (finCycle c q))) <
        cyclicKey i (pointCoords (cellOrderVertex hcell i (finCycle c t))) at hlt_i
      have heq : pointCoords (cellOrderVertex hcell i (finCycle c q)) i =
          pointCoords (cellOrderVertex hcell i (finCycle c t)) i := by omega
      change cyclicKey j (pointCoords (cellOrderVertex hcell i (finCycle c q))) <
        cyclicKey j (pointCoords (cellOrderVertex hcell i (finCycle c t)))
      exact (cyclicKey_lt_iff_next_of_eq i heq).mp hlt_i
    · obtain ⟨hqc, htc, hqtl⟩ := hlow
      have hqLow := (cellOrderVertex_coord_low_iff_lt_cut hn hcell i
        (finCycle c q)).2 (by simpa [c, j] using hqc)
      have htLow := (cellOrderVertex_coord_low_iff_lt_cut hn hcell i
        (finCycle c t)).2 (by simpa [c, j] using htc)
      have hlt_i := (cellOrderVertex_lt_iff hcell i
        (finCycle c q) (finCycle c t)).2 hqtl
      change cyclicKey i (pointCoords (cellOrderVertex hcell i (finCycle c q))) <
        cyclicKey i (pointCoords (cellOrderVertex hcell i (finCycle c t))) at hlt_i
      have heq : pointCoords (cellOrderVertex hcell i (finCycle c q)) i =
          pointCoords (cellOrderVertex hcell i (finCycle c t)) i := by omega
      change cyclicKey j (pointCoords (cellOrderVertex hcell i (finCycle c q))) <
        cyclicKey j (pointCoords (cellOrderVertex hcell i (finCycle c t)))
      exact (cyclicKey_lt_iff_next_of_eq i heq).mp hlt_i
    · obtain ⟨hqc, htc⟩ := hcross
      exact cellOrderVertex_high_lt_next_low hn hcell i
        (finCycle c q) (finCycle c t)
        (by simpa [c, j] using hqc) (by simpa [c, j] using htc)
  have huniq : f = σ.orderEmbOfFin (fullCell_card hcell) :=
    Finset.orderEmbOfFin_unique (fullCell_card hcell) hfmem hfmono
  simpa [f, c, j, cellOrderVertex] using (congrFun huniq r).symm

/-- At the next-order cut, the old primary coordinate increases by exactly
one. -/
theorem cellCut_oldCoord_increases (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) {q : Fin n}
    (hq : q.succ = cellCut hcell i (finRotate _ i)) :
    pointCoords
        (cellOrderVertex hcell i (cellCut hcell i (finRotate _ i))) i =
      pointCoords (cellOrderVertex hcell i q.castSucc) i + 1 := by
  have hqcut : q.castSucc < cellCut hcell i (finRotate _ i) := by
    rw [← hq]
    exact q.castSucc_lt_succ
  have hlow := (cellOrderVertex_coord_low_iff_lt_cut hn hcell i q.castSucc).2
    hqcut
  have hhigh := cellCut_next_coord_high hn hcell i
  omega

private theorem finCycle_last_eq_castSucc_of_succ_eq {n : ℕ}
    {c : Fin (n + 1)} {q : Fin n} (hq : q.succ = c) :
    finCycle c (Fin.last n) = q.castSucc := by
  apply Fin.ext
  rw [finCycle_apply]
  simp only [Fin.val_add_eq_ite, Fin.val_last]
  have hcval : c.val = q.val + 1 := by
    rw [← hq]
    rfl
  rw [hcval]
  change (if n + 1 ≤ n + (q.val + 1) then
      n + (q.val + 1) - (n + 1) else n + (q.val + 1)) = q.val
  have hq_lt : q.val < n := q.isLt
  rw [if_pos (by omega)]
  omega

/-- At the same cut, the new primary coordinate decreases by exactly one. -/
theorem cellCut_newCoord_decreases (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) {q : Fin n}
    (hq : q.succ = cellCut hcell i (finRotate _ i)) :
    pointCoords (cellOrderVertex hcell i q.castSucc) (finRotate _ i) =
      pointCoords
        (cellOrderVertex hcell i (cellCut hcell i (finRotate _ i)))
        (finRotate _ i) + 1 := by
  let j : Fin (n + 1) := finRotate _ i
  let c : Fin (n + 1) := cellCut hcell i j
  have hzero : cellOrderVertex hcell j 0 = cellOrderVertex hcell i c := by
    simpa [j, c, finCycle_apply] using
      cellOrderVertex_next_eq_rotate hn hcell i 0
  have hlast : cellOrderVertex hcell j (Fin.last n) =
      cellOrderVertex hcell i q.castSucc := by
    rw [cellOrderVertex_next_eq_rotate hn hcell i (Fin.last n)]
    congr 1
    exact finCycle_last_eq_castSucc_of_succ_eq (by simpa [j, c] using hq)
  have hhigh :=
    (cellOrderVertex_coord_high_iff_cut_le hn hcell j (Fin.last n)).2
      (Fin.le_last _)
  rw [hlast, hzero] at hhigh
  simpa [j, c] using hhigh

/-- Lemma 4.4, expressed without an arbitrary external numbering of the
vertices.  The cut vertex is the next minimum, the next ordered enumeration
is the corresponding cyclic rotation, and the two distinguished coordinates
change by exactly one in opposite directions. -/
theorem lemma4_4 (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) :
    ∃ q : Fin n,
      q.succ = cellCut hcell i (finRotate _ i) ∧
      cellOrderVertex hcell i q.succ = cellMinimum hcell (finRotate _ i) ∧
      (∀ r : Fin (n + 1),
        cellOrderVertex hcell (finRotate _ i) r =
          cellOrderVertex hcell i
            (finCycle (cellCut hcell i (finRotate _ i)) r)) ∧
      pointCoords (cellOrderVertex hcell i q.succ) i =
        pointCoords (cellOrderVertex hcell i q.castSucc) i + 1 ∧
      pointCoords (cellOrderVertex hcell i q.castSucc) (finRotate _ i) =
        pointCoords (cellOrderVertex hcell i q.succ) (finRotate _ i) + 1 := by
  have hcut0 : cellCut hcell i (finRotate _ i) ≠ 0 :=
    cellCut_ne_zero_of_ne hcell (rotate_ne_self_of_pos hn i).symm
  obtain ⟨q, hq⟩ := Fin.exists_succ_eq_of_ne_zero hcut0
  refine ⟨q, hq, ?_, ?_, ?_, ?_⟩
  · rw [hq]
    exact cellOrderVertex_cut_eq_minimum hcell i (finRotate _ i)
  · exact cellOrderVertex_next_eq_rotate hn hcell i
  · rw [hq]
    exact cellCut_oldCoord_increases hn hcell i hq
  · rw [hq]
    exact cellCut_newCoord_decreases hn hcell i hq

/-! The cyclic edge set does not depend on which cyclic lexicographic order
is used to enumerate the cell.  Making this invariant explicit avoids a
hidden appeal to an arbitrary numbering in the proof of Theorem 4.5. -/

/-- A directed edge in the cyclic ordering of the vertices of a full cell. -/
def IsCellCyclicEdge
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) (x y : Point N n) : Prop :=
  ∃ r : Fin (n + 1),
    x = cellOrderVertex hcell i r ∧
      y = cellOrderVertex hcell i (finRotate _ r)

private theorem finCycle_finRotate {n : ℕ} (c r : Fin (n + 1)) :
    finCycle c (finRotate _ r) = finRotate _ (finCycle c r) := by
  simp only [finCycle_apply, finRotate_apply]
  abel

/-- Passing to the next coordinate order only rotates the enumeration, so it
preserves the directed cyclic edge relation. -/
theorem isCellCyclicEdge_next_iff (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) (x y : Point N n) :
    IsCellCyclicEdge hcell (finRotate _ i) x y ↔
    IsCellCyclicEdge hcell i x y := by
  let c : Fin (n + 1) := cellCut hcell i (finRotate _ i)
  constructor
  · rintro ⟨r, rfl, rfl⟩
    refine ⟨finCycle c r, ?_, ?_⟩
    · simpa [c] using cellOrderVertex_next_eq_rotate hn hcell i r
    · rw [cellOrderVertex_next_eq_rotate hn hcell i]
      rw [finCycle_finRotate]
  · rintro ⟨s, rfl, rfl⟩
    let r : Fin (n + 1) := (finCycle c).symm s
    refine ⟨r, ?_, ?_⟩
    · rw [cellOrderVertex_next_eq_rotate hn hcell i]
      simp [c, r]
    · rw [cellOrderVertex_next_eq_rotate hn hcell i]
      rw [finCycle_finRotate]
      simp [c, r]

/-- Every cyclic coordinate order induces the same directed cyclic edge set
on a full cell. -/
theorem isCellCyclicEdge_iff_zero (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (i : Fin (n + 1)) (x y : Point N n) :
    IsCellCyclicEdge hcell i x y ↔ IsCellCyclicEdge hcell 0 x y := by
  induction i using Fin.induction with
  | zero => rfl
  | succ q ih =>
      have hnext := isCellCyclicEdge_next_iff hn hcell q.castSucc x y
      simpa [finRotate_apply] using hnext.trans ih

/-- In a directed cyclic edge, every coordinate other than the one whose
minimum is the target is nondecreasing.  This is the precise monotonicity
fact needed to rule out unnoticed changes in other coordinates. -/
theorem coord_le_of_isCellCyclicEdge_of_ne_minimum (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (j i : Fin (n + 1)) {x y : Point N n}
    (hedge : IsCellCyclicEdge hcell j x y)
    (hy : y ≠ cellMinimum hcell i) :
    pointCoords x i ≤ pointCoords y i := by
  have hedge0 : IsCellCyclicEdge hcell 0 x y :=
    (isCellCyclicEdge_iff_zero hn hcell j x y).1 hedge
  have hedgei : IsCellCyclicEdge hcell i x y :=
    (isCellCyclicEdge_iff_zero hn hcell i x y).2 hedge0
  obtain ⟨r, hx, hyr⟩ := hedgei
  rcases Fin.eq_castSucc_or_eq_last r with ⟨q, rfl⟩ | rfl
  · rw [hx, hyr]
    apply cellOrderVertex_coord_mono hcell i
    simpa [finRotate_apply] using q.castSucc_lt_succ.le
  · exfalso
    apply hy
    rw [hyr]
    simpa using cellOrderVertex_zero_eq_minimum hcell i

/-- The predecessor of a noninitial vertex in the zero-order cyclic edge is
the preceding element of the canonical zero-order enumeration. -/
theorem isCellCyclicEdge_zero_predecessor
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (k : Fin n) {x : Point N n}
    (hedge : IsCellCyclicEdge hcell 0 x
      (cellOrderVertex hcell 0 k.succ)) :
    x = cellOrderVertex hcell 0 k.castSucc := by
  obtain ⟨r, hx, hy⟩ := hedge
  have hrRotate : finRotate _ r = k.succ := by
    apply cellOrderVertex_injective hcell 0
    exact hy.symm
  have hr : r = k.castSucc := by
    apply (finRotate (n + 1)).injective
    simpa [finRotate_apply] using hrRotate
  simpa [hr] using hx

/-- Consecutive vertices in the canonical zero-order enumeration are related
by exactly the cyclic transfer indexed by the minimum of the target vertex.
The proof uses equality of coordinate sums to show that no third coordinate
can change. -/
theorem cellOrderVertex_succ_eq_cyclicStep (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (k : Fin n) :
    pointCoords (cellOrderVertex hcell 0 k.succ) =
      cyclicStep (cellIndexPermutation hcell 0 k.succ)
        (pointCoords (cellOrderVertex hcell 0 k.castSucc)) := by
  let i : Fin (n + 1) := cellIndexPermutation hcell 0 k.succ
  have hi0 : i ≠ 0 := by
    intro hi
    have hk0 : k.succ = (0 : Fin (n + 1)) := by
      apply (cellIndexPermutation hcell 0).injective
      simp [i, hi]
    exact Fin.succ_ne_zero k hk0
  obtain ⟨p, hp⟩ := Fin.exists_succ_eq_of_ne_zero hi0
  have hpRotate : finRotate _ p.castSucc = i := by
    simpa [finRotate_apply] using hp
  have hpred : (finRotate _).symm i = p.castSucc := by
    apply (finRotate (n + 1)).injective
    simp only [Equiv.apply_symm_apply]
    exact hpRotate.symm
  have hpne : p.castSucc ≠ i := by
    rw [← hp]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  obtain ⟨q, hq, hqmin, _, hinc, hdec⟩ :=
    lemma4_4 hn hcell p.castSucc
  let x : Point N n := cellOrderVertex hcell p.castSucc q.castSucc
  let y : Point N n := cellOrderVertex hcell p.castSucc q.succ
  have hyTarget : y = cellOrderVertex hcell 0 k.succ := by
    calc
      y = cellMinimum hcell (finRotate _ p.castSucc) := by
        simpa [y] using hqmin
      _ = cellMinimum hcell i := by rw [hpRotate]
      _ = cellOrderVertex hcell 0 k.succ := by
        simpa [i] using cellIndexPermutation_spec hcell 0 k.succ
  have hedgePred : IsCellCyclicEdge hcell p.castSucc x y := by
    refine ⟨q.castSucc, rfl, ?_⟩
    simp [y, finRotate_apply]
  have hedgeZero : IsCellCyclicEdge hcell 0 x y :=
    (isCellCyclicEdge_iff_zero hn hcell p.castSucc x y).1 hedgePred
  have hxSource : x = cellOrderVertex hcell 0 k.castSucc := by
    apply isCellCyclicEdge_zero_predecessor hcell k
    simpa [hyTarget] using hedgeZero
  have hinc' :
      pointCoords (cellOrderVertex hcell 0 k.succ) p.castSucc =
        pointCoords (cellOrderVertex hcell 0 k.castSucc) p.castSucc + 1 := by
    rw [← hyTarget, ← hxSource]
    simpa [x, y] using hinc
  have hdec' :
      pointCoords (cellOrderVertex hcell 0 k.castSucc) i =
        pointCoords (cellOrderVertex hcell 0 k.succ) i + 1 := by
    rw [← hyTarget, ← hxSource, ← hpRotate]
    simpa [x, y] using hdec
  have hedgeCanonical : IsCellCyclicEdge hcell 0
      (cellOrderVertex hcell 0 k.castSucc)
      (cellOrderVertex hcell 0 k.succ) := by
    refine ⟨k.castSucc, rfl, ?_⟩
    simp [finRotate_apply]
  have hle : ∀ j : Fin (n + 1),
      cyclicStep i (pointCoords (cellOrderVertex hcell 0 k.castSucc)) j ≤
        pointCoords (cellOrderVertex hcell 0 k.succ) j := by
    intro j
    by_cases hjp : j = p.castSucc
    · subst j
      rw [cyclicStep_apply, if_pos hpred.symm, if_neg hpne]
      omega
    · by_cases hji : j = i
      · subst j
        rw [cyclicStep_apply,
          if_neg (fun h ↦ hpne ((h.trans hpred).symm)), if_pos rfl]
        omega
      · have hyne : cellOrderVertex hcell 0 k.succ ≠
            cellMinimum hcell j := by
          intro heq
          have hminEq : cellMinimum hcell i = cellMinimum hcell j := by
            rw [cellIndexPermutation_spec hcell 0 k.succ]
            exact heq
          have hij : i = j := by
            apply (cellMinimumEquiv hcell).injective
            apply Subtype.ext
            exact hminEq
          exact hji hij.symm
        have hmono := coord_le_of_isCellCyclicEdge_of_ne_minimum
          hn hcell 0 j hedgeCanonical hyne
        rw [cyclicStep_apply, if_neg (fun h ↦ hjp (h.trans hpred)),
          if_neg hji]
        simpa using hmono
  have hsum :
      ∑ j, cyclicStep i
          (pointCoords (cellOrderVertex hcell 0 k.castSucc)) j =
        ∑ j, pointCoords (cellOrderVertex hcell 0 k.succ) j := by
    rw [sum_cyclicStep]
    exact (pointCoords_isPoint
      (cellOrderVertex hcell 0 k.castSucc)).2.trans
        (pointCoords_isPoint (cellOrderVertex hcell 0 k.succ)).2.symm
  have hall := (Finset.sum_eq_sum_iff_of_le
    (s := (Finset.univ : Finset (Fin (n + 1))))
    (fun j _ ↦ hle j)).1 hsum
  funext j
  exact (hall j (Finset.mem_univ j)).symm

theorem cellIndexPermutation_succ_ne_zero
    (hcell : (pointOrders N n).IsCell σ Finset.univ) (k : Fin n) :
    cellIndexPermutation hcell 0 k.succ ≠ 0 := by
  intro hk
  have hzero : k.succ = (0 : Fin (n + 1)) := by
    apply (cellIndexPermutation hcell 0).injective
    simp [hk]
  exact Fin.succ_ne_zero k hzero

/-- The restriction of the paper's permutation `ι` to the nonzero
coordinates, reindexed by `Fin n`. -/
noncomputable def cellStepPermutation
    (hcell : (pointOrders N n).IsCell σ Finset.univ) :
    Equiv.Perm (Fin n) := by
  let f : Fin n → Fin n := fun k ↦
    (cellIndexPermutation hcell 0 k.succ).pred
      (cellIndexPermutation_succ_ne_zero hcell k)
  apply Equiv.ofBijective f
  constructor
  · intro k l hkl
    apply Fin.succ_injective
    apply (cellIndexPermutation hcell 0).injective
    calc
      cellIndexPermutation hcell 0 k.succ = (f k).succ := by
        symm
        exact Fin.succ_pred _ _
      _ = (f l).succ := congrArg Fin.succ hkl
      _ = cellIndexPermutation hcell 0 l.succ := Fin.succ_pred _ _
  · intro j
    obtain ⟨r, hr⟩ := (cellIndexPermutation hcell 0).surjective j.succ
    have hr0 : r ≠ 0 := by
      intro hrzero
      subst r
      rw [cellIndexPermutation_zero_zero] at hr
      exact Fin.succ_ne_zero j hr.symm
    obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hr0
    refine ⟨k, ?_⟩
    apply Fin.succ_injective
    rw [Fin.succ_pred]
    simpa [f, hk] using hr

@[simp]
theorem cellStepPermutation_succ
    (hcell : (pointOrders N n).IsCell σ Finset.univ) (k : Fin n) :
    (cellStepPermutation hcell k).succ =
      cellIndexPermutation hcell 0 k.succ := by
  change ((cellIndexPermutation hcell 0 k.succ).pred
    (cellIndexPermutation_succ_ne_zero hcell k)).succ = _
  exact Fin.succ_pred _ _

/-- Away from the wrap coordinate, the cyclic transfer `S_i` is the
`step` operator used in the step-simplex definition. -/
theorem cyclicStep_succ_eq_step (i : Fin n) (a : Fin (n + 1) → ℤ) :
    cyclicStep i.succ a = step i a := by
  have hpred : (finRotate _).symm i.succ = i.castSucc := by
    apply (finRotate (n + 1)).injective
    simp [finRotate_apply]
  ext j
  simp [cyclicStep_apply, step_apply, hpred]

/-- Standard-step form of the consecutive-vertex recurrence. -/
theorem cellOrderVertex_succ_eq_step (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ)
    (k : Fin n) :
    pointCoords (cellOrderVertex hcell 0 k.succ) =
      step (cellStepPermutation hcell k)
        (pointCoords (cellOrderVertex hcell 0 k.castSucc)) := by
  rw [← cyclicStep_succ_eq_step]
  rw [cellStepPermutation_succ]
  exact cellOrderVertex_succ_eq_cyclicStep hn hcell k

private theorem stepSequence_ofFn_eq_of_succ
    {m n : ℕ} (f : Fin (m + 1) → (Fin (n + 1) → ℤ))
    (g : Fin m → Fin n)
    (hrec : ∀ k : Fin m, f k.succ = step (g k) (f k.castSucc)) :
    stepSequence (f 0) (List.ofFn g) = List.ofFn f := by
  induction m with
  | zero => simp [stepSequence, List.ofFn_succ]
  | succ m ih =>
      have hg : List.ofFn g = g 0 :: List.ofFn (fun r ↦ g r.succ) :=
        List.ofFn_succ
      have hf : List.ofFn f = f 0 :: List.ofFn (fun r ↦ f r.succ) :=
        List.ofFn_succ
      rw [hg, hf, stepSequence]
      congr 1
      have hzero : f (0 : Fin (m + 1)).succ = step (g 0) (f 0) := by
        simpa using hrec 0
      rw [← hzero]
      apply ih (f := fun r ↦ f r.succ) (g := fun r ↦ g r.succ)
      intro k
      simpa using hrec k.succ

/-- The complete ordered coordinate sequence of a full cell is exactly the
step sequence attached to its canonical permutation. -/
theorem cellStepSequence_eq (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ) :
    stepSequence (pointCoords (cellMinimum hcell 0))
        (permutationList (cellStepPermutation hcell)) =
      List.ofFn (fun r : Fin (n + 1) ↦
        pointCoords (cellOrderVertex hcell 0 r)) := by
  rw [← cellOrderVertex_zero_eq_minimum hcell 0]
  unfold permutationList
  apply stepSequence_ofFn_eq_of_succ
    (f := fun r : Fin (n + 1) ↦
      pointCoords (cellOrderVertex hcell 0 r))
    (g := fun k : Fin n ↦ cellStepPermutation hcell k)
  intro k
  exact cellOrderVertex_succ_eq_step hn hcell k

/-- Canonical, nonexistential form of Theorem 4.5: after the injective
coordinate embedding, a full cell is exactly the step simplex based at its
zero-order minimum and indexed by the induced permutation of the nonzero
coordinates. -/
theorem fullCell_image_eq_stepSimplex (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ) :
    σ.image pointCoords =
      stepSimplex (pointCoords (cellMinimum hcell 0))
        (permutationList (cellStepPermutation hcell)) := by
  rw [stepSimplex, cellStepSequence_eq hn hcell]
  ext x
  rw [Finset.mem_image, List.mem_toFinset, List.mem_ofFn]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨r, hr⟩ := cellOrderVertex_surjective_on hcell 0 ha
    exact ⟨r, congrArg pointCoords hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨cellOrderVertex hcell 0 r,
      cellOrderVertex_mem hcell 0 r, hr⟩

/-- The positive-dimensional part of Theorem 4.5 in the paper's existential
form.  The permutation is on the nonzero indices; adjoining the fixed index
zero recovers `cellIndexPermutation hcell 0`. -/
theorem theorem4_5_of_pos (hn : 0 < n)
    (hcell : (pointOrders N n).IsCell σ Finset.univ) :
    ∃ a : Point N n, a ∈ σ ∧
      ∃ ω : Equiv.Perm (Fin n),
        σ.image pointCoords =
          stepSimplex (pointCoords a) (permutationList ω) := by
  refine ⟨cellMinimum hcell 0, cellMinimum_mem hcell 0,
    cellStepPermutation hcell, ?_⟩
  exact fullCell_image_eq_stepSimplex hn hcell

/-- Theorem 4.5 in every dimension, including the trivial but mathematically
necessary zero-dimensional case. -/
theorem theorem4_5
    (hcell : (pointOrders N n).IsCell σ Finset.univ) :
    ∃ a : Point N n, a ∈ σ ∧
      ∃ ω : Equiv.Perm (Fin n),
        σ.image pointCoords =
          stepSimplex (pointCoords a) (permutationList ω) := by
  by_cases hn : n = 0
  · subst n
    have hcard : σ.card = 1 := by simpa using hcell.2
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    refine ⟨a, Finset.mem_singleton_self a, Equiv.refl (Fin 0), ?_⟩
    ext x
    simp [stepSimplex, permutationList, stepSequence]
  · exact theorem4_5_of_pos (Nat.pos_of_ne_zero hn) hcell

end IntegerSimplex

end BeyondSperner
