import BeyondSperner.OrientedMatroid.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Realizable oriented matroids

This file constructs the signed-circuit layer associated with a finite real
vector configuration.  Nothing in the construction is postulated: circuits
are the sign vectors of support-minimal nonzero linear dependences.

The construction is kept separate from `VectorColoring`: it is a general
compatibility theorem between finite-dimensional linear algebra and the
signed-circuit API, not an additional hypothesis on a vector-coloring
framework.
-/

namespace BeyondSperner

open Classical
open Set
open scoped BigOperators

namespace RealizableOrientedMatroid

variable {α V : Type*} [Fintype α] [AddCommGroup V] [Module ℝ V]

/-- The linear combination of a finite real vector configuration. -/
def combination (v : α → V) (a : α → ℝ) : V :=
  ∑ i, a i • v i

theorem combination_zero (v : α → V) : combination v 0 = 0 := by
  simp [combination]

theorem combination_add (v : α → V) (a b : α → ℝ) :
    combination v (a + b) = combination v a + combination v b := by
  simp only [combination, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem combination_smul (v : α → V) (c : ℝ) (a : α → ℝ) :
    combination v (c • a) = c • combination v a := by
  simp only [combination, Pi.smul_apply, smul_eq_mul, mul_smul,
    Finset.smul_sum]

theorem combination_neg (v : α → V) (a : α → ℝ) :
    combination v (-a) = -combination v a := by
  simpa using combination_smul v (-1) a

theorem combination_sub (v : α → V) (a b : α → ℝ) :
    combination v (a - b) = combination v a - combination v b := by
  rw [sub_eq_add_neg, combination_add, combination_neg, sub_eq_add_neg]

theorem combination_single (v : α → V) (i : α) (c : ℝ) :
    combination v (Pi.single i c) = c • v i := by
  simp [combination]

/-- The indices carrying nonzero coefficients. -/
def coefficientSupport (a : α → ℝ) : Set α :=
  Function.support a

omit [Fintype α] in @[simp]
theorem mem_coefficientSupport {a : α → ℝ} {i : α} :
    i ∈ coefficientSupport a ↔ a i ≠ 0 :=
  Iff.rfl

omit [Fintype α] in @[simp]
theorem coefficientSupport_zero : coefficientSupport (0 : α → ℝ) = ∅ := by
  ext i
  simp

omit [Fintype α] in theorem coefficientSupport_smul_subset (c : ℝ) (a : α → ℝ) :
    coefficientSupport (c • a) ⊆ coefficientSupport a := by
  intro i hi
  simp only [mem_coefficientSupport, Pi.smul_apply, smul_eq_mul] at hi ⊢
  exact fun hai ↦ hi (by simp [hai])

omit [Fintype α] in theorem coefficientSupport_smul_eq {c : ℝ} (hc : c ≠ 0)
    (a : α → ℝ) :
    coefficientSupport (c • a) = coefficientSupport a := by
  ext i
  simp [coefficientSupport, hc]

omit [Fintype α] in @[simp]
theorem coefficientSupport_neg (a : α → ℝ) :
    coefficientSupport (-a) = coefficientSupport a := by
  simpa using coefficientSupport_smul_eq (c := (-1 : ℝ)) (by norm_num) a

omit [Fintype α] in theorem coefficientSupport_add_subset (a b : α → ℝ) :
    coefficientSupport (a + b) ⊆
      coefficientSupport a ∪ coefficientSupport b := by
  intro i hi
  simp only [mem_coefficientSupport, Pi.add_apply, Set.mem_union] at hi ⊢
  by_contra h
  push Not at h
  exact hi (by rw [h.1, h.2, add_zero])

/-- The signed subset determined by the strict signs of a coefficient
vector. -/
def signVector (a : α → ℝ) : SignedSubset α where
  positive := {i | 0 < a i}
  negative := {i | a i < 0}
  disjoint := by
    rw [Set.disjoint_left]
    intro i hiPos hiNeg
    change 0 < a i at hiPos
    change a i < 0 at hiNeg
    exact (not_lt_of_ge hiPos.le hiNeg)

omit [Fintype α] in @[simp]
theorem mem_signVector_positive {a : α → ℝ} {i : α} :
    i ∈ (signVector a).positive ↔ 0 < a i :=
  Iff.rfl

omit [Fintype α] in @[simp]
theorem mem_signVector_negative {a : α → ℝ} {i : α} :
    i ∈ (signVector a).negative ↔ a i < 0 :=
  Iff.rfl

omit [Fintype α] in @[simp]
theorem signVector_support (a : α → ℝ) :
    (signVector a).support = coefficientSupport a := by
  ext i
  simp only [SignedSubset.support, Set.mem_union,
    mem_signVector_positive, mem_signVector_negative,
    mem_coefficientSupport]
  constructor
  · rintro (hi | hi)
    · exact ne_of_gt hi
    · exact ne_of_lt hi
  · intro hi
    rcases lt_or_gt_of_ne hi with hiNeg | hiPos
    · exact Or.inr hiNeg
    · exact Or.inl hiPos

omit [Fintype α] in @[simp]
theorem signVector_neg (a : α → ℝ) :
    signVector (-a) = -(signVector a) := by
  ext i <;> simp

omit [Fintype α] in theorem signVector_smul_of_pos {c : ℝ} (hc : 0 < c) (a : α → ℝ) :
    signVector (c • a) = signVector a := by
  apply SignedSubset.ext
  · ext i
    change (0 < c * a i) ↔ 0 < a i
    constructor <;> intro h
    · rcases (mul_pos_iff.mp h) with hsame | hsame
      · exact hsame.2
      · nlinarith [hc, hsame.1]
    · exact mul_pos hc h
  · ext i
    change (c * a i < 0) ↔ a i < 0
    constructor <;> intro h
    · rcases (mul_neg_iff.mp h) with hsign | hsign
      · exact hsign.2
      · nlinarith [hc, hsign.1]
    · exact mul_neg_of_pos_of_neg hc h

omit [Fintype α] in theorem signVector_smul_of_neg {c : ℝ} (hc : c < 0) (a : α → ℝ) :
    signVector (c • a) = -(signVector a) := by
  apply SignedSubset.ext
  · ext i
    change (0 < c * a i) ↔ a i < 0
    constructor <;> intro h
    · rcases (mul_pos_iff.mp h) with hsame | hsame
      · nlinarith [hc, hsame.1]
      · exact hsame.2
    · exact mul_pos_of_neg_of_neg hc h
  · ext i
    change (c * a i < 0) ↔ 0 < a i
    constructor <;> intro h
    · rcases (mul_neg_iff.mp h) with hsign | hsign
      · nlinarith [hc, hsign.1]
      · exact hsign.2
    · exact mul_neg_of_neg_of_pos hc h

/-- A nonzero coefficient vector in the kernel of the configuration map. -/
def IsDependence (v : α → V) (a : α → ℝ) : Prop :=
  a ≠ 0 ∧ combination v a = 0

theorem IsDependence.smul {v : α → V} {a : α → ℝ}
    (ha : IsDependence v a) {c : ℝ} (hc : c ≠ 0) :
    IsDependence v (c • a) := by
  constructor
  · intro hzero
    apply ha.1
    funext i
    have hi := congrFun hzero i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_left hc
  · rw [combination_smul, ha.2, smul_zero]

/-- An elementary dependence is a nonzero dependence with inclusion-minimal
support.  This is the coefficient-level notion underlying a realizable
oriented circuit. -/
def IsElementary (v : α → V) (a : α → ℝ) : Prop :=
  IsDependence v a ∧
    ∀ ⦃b : α → ℝ⦄, IsDependence v b →
      coefficientSupport b ⊆ coefficientSupport a →
        coefficientSupport a ⊆ coefficientSupport b

/-- `a` is conformal to `x` when it is supported inside `x` and never has
the opposite strict sign. -/
def ConformalTo (a x : α → ℝ) : Prop :=
  coefficientSupport a ⊆ coefficientSupport x ∧
    ∀ i, 0 ≤ a i * x i

omit [Fintype α] in theorem ConformalTo.signVector_le {a x : α → ℝ}
    (h : ConformalTo a x) : signVector a ≤ signVector x := by
  constructor
  · intro i hi
    change 0 < a i at hi
    change 0 < x i
    have hxiNe : x i ≠ 0 := mem_coefficientSupport.mp
      (h.1 (mem_coefficientSupport.mpr (ne_of_gt hi)))
    have hprod := h.2 i
    rcases lt_or_gt_of_ne hxiNe with hxiNeg | hxiPos
    · nlinarith
    · exact hxiPos
  · intro i hi
    change a i < 0 at hi
    change x i < 0
    have hxiNe : x i ≠ 0 := mem_coefficientSupport.mp
      (h.1 (mem_coefficientSupport.mpr (ne_of_lt hi)))
    have hprod := h.2 i
    rcases lt_or_gt_of_ne hxiNe with hxiNeg | hxiPos
    · exact hxiNeg
    · nlinarith

omit [Fintype α] in theorem conformalTo_refl (a : α → ℝ) : ConformalTo a a := by
  constructor
  · exact Set.Subset.rfl
  · intro i
    simpa [pow_two] using sq_nonneg (a i)

omit [Fintype α] in theorem ConformalTo.trans {a y x : α → ℝ}
    (hay : ConformalTo a y) (hyx : ConformalTo y x) :
    ConformalTo a x := by
  constructor
  · exact hay.1.trans hyx.1
  · intro i
    by_cases hai : a i = 0
    · simp [hai]
    have hyiNe : y i ≠ 0 := mem_coefficientSupport.mp
      (hay.1 (mem_coefficientSupport.mpr hai))
    have hxiNe : x i ≠ 0 := mem_coefficientSupport.mp
      (hyx.1 (mem_coefficientSupport.mpr hyiNe))
    rcases lt_or_gt_of_ne hai with haiNeg | haiPos
    · have hyiNeg : y i < 0 := by
        rcases lt_or_gt_of_ne hyiNe with hyiNeg | hyiPos
        · exact hyiNeg
        · nlinarith [hay.2 i]
      have hxiNeg : x i < 0 := by
        rcases lt_or_gt_of_ne hxiNe with hxiNeg | hxiPos
        · exact hxiNeg
        · nlinarith [hyx.2 i]
      exact mul_nonneg_of_nonpos_of_nonpos haiNeg.le hxiNeg.le
    · have hyiPos : 0 < y i := by
        rcases lt_or_gt_of_ne hyiNe with hyiNeg | hyiPos
        · nlinarith [hay.2 i]
        · exact hyiPos
      have hxiPos : 0 < x i := by
        rcases lt_or_gt_of_ne hxiNe with hxiNeg | hxiPos
        · nlinarith [hyx.2 i]
        · exact hxiPos
      exact mul_nonneg haiPos.le hxiPos.le

/-- If a dependence contains a strictly smaller dependent support, one can
subtract a suitable multiple of that smaller dependence without crossing
any coordinate hyperplane in the wrong direction.  The output is a
nonzero conformal dependence with strictly smaller support.

The multiplier is the minimum of finitely many positive coordinate ratios;
this is the numerical core of realizable circuit elimination. -/
theorem exists_conformal_dependence_ssubset
    {v : α → V} {x w : α → ℝ}
    (hx : IsDependence v x) (hw : IsDependence v w)
    (hwx : coefficientSupport w ⊂ coefficientSupport x) :
    ∃ y : α → ℝ, IsDependence v y ∧ ConformalTo y x ∧
      coefficientSupport y ⊂ coefficientSupport x ∧
        ∀ i, i ∉ coefficientSupport w → y i = x i := by
  obtain ⟨e, hwe⟩ : ∃ e, w e ≠ 0 := by
    simpa [Function.ne_iff] using hw.1
  have hew : e ∈ coefficientSupport w :=
    mem_coefficientSupport.mpr hwe
  have hex : e ∈ coefficientSupport x := hwx.le hew
  have hxe : x e ≠ 0 := mem_coefficientSupport.mp hex
  let s : ℝ := x e / w e
  have hsNe : s ≠ 0 := div_ne_zero hxe hwe
  let w' : α → ℝ := s • w
  have hw'Dep : IsDependence v w' := hw.smul hsNe
  have hw'Support : coefficientSupport w' = coefficientSupport w :=
    coefficientSupport_smul_eq hsNe w
  have hw'x : coefficientSupport w' ⊂ coefficientSupport x := by
    simpa [hw'Support] using hwx
  have hw'e : w' e = x e := by
    simp [w', s, hwe]
  let S : Finset α := Finset.univ.filter fun i ↦ 0 < x i * w' i
  have heS : e ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hw'e]
    exact mul_self_pos.mpr hxe
  obtain ⟨i₀, hi₀S, hi₀min⟩ :=
    S.exists_min_image (fun i ↦ x i / w' i) ⟨e, heS⟩
  have hi₀prod : 0 < x i₀ * w' i₀ :=
    (Finset.mem_filter.mp hi₀S).2
  have hi₀x : x i₀ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hi₀prod
    exact (lt_irrefl 0 hi₀prod)
  have hi₀w : w' i₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hi₀prod
    exact (lt_irrefl 0 hi₀prod)
  let t : ℝ := x i₀ / w' i₀
  have htPos : 0 < t := by
    dsimp [t]
    exact (div_pos_iff.mpr (mul_pos_iff.mp hi₀prod))
  let y : α → ℝ := x - t • w'
  have hyEq : y = x + (-t) • w' := by
    ext i
    dsimp [y]
    ring
  have hyComb : combination v y = 0 := by
    rw [hyEq, combination_add, combination_smul, hx.2, hw'Dep.2]
    simp
  have hyConformal : ConformalTo y x := by
    constructor
    · intro i hi
      apply mem_coefficientSupport.mpr
      intro hxi
      have hwi : w' i = 0 := by
        by_contra hwi
        have hiw : i ∈ coefficientSupport w' :=
          mem_coefficientSupport.mpr hwi
        exact (mem_coefficientSupport.mp (hw'x.le hiw)) hxi
      have hyi : y i = 0 := by simp [y, hxi, hwi]
      exact (mem_coefficientSupport.mp hi) hyi
    · intro i
      by_cases hsame : 0 < x i * w' i
      · have hiS : i ∈ S := by simp [S, hsame]
        have hratio : t ≤ x i / w' i := hi₀min i hiS
        rcases mul_pos_iff.mp hsame with hpos | hneg
        · have hbound : t * w' i ≤ x i :=
            (le_div_iff₀ hpos.2).mp hratio
          have hyNonneg : 0 ≤ y i := by
            dsimp [y]
            linarith
          exact mul_nonneg hyNonneg hpos.1.le
        · have hbound : x i ≤ t * w' i :=
            (le_div_iff_of_neg hneg.2).mp hratio
          have hyNonpos : y i ≤ 0 := by
            dsimp [y]
            linarith
          exact mul_nonneg_of_nonpos_of_nonpos hyNonpos hneg.1.le
      · have hopposite : x i * w' i ≤ 0 := le_of_not_gt hsame
        have hscaled : t * (x i * w' i) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos htPos.le hopposite
        dsimp [y]
        change 0 ≤ (x i - t * w' i) * x i
        nlinarith [sq_nonneg (x i)]
  have hyAtI₀ : y i₀ = 0 := by
    dsimp [y, t]
    rw [div_mul_cancel₀ _ hi₀w]
    exact sub_self _
  have hi₀NotY : i₀ ∉ coefficientSupport y := by
    simpa [mem_coefficientSupport] using hyAtI₀
  have hi₀InX : i₀ ∈ coefficientSupport x :=
    mem_coefficientSupport.mpr hi₀x
  obtain ⟨k, hkx, hkw'⟩ := Set.exists_of_ssubset hw'x
  have hw'k : w' k = 0 := by
    simpa [mem_coefficientSupport] using hkw'
  have hyk : y k = x k := by simp [y, hw'k]
  have hyNe : y ≠ 0 := by
    intro hzero
    have := congrFun hzero k
    rw [hyk] at this
    exact (mem_coefficientSupport.mp hkx) this
  have hyStrict : coefficientSupport y ⊂ coefficientSupport x :=
    hyConformal.1.ssubset_of_mem_notMem hi₀InX hi₀NotY
  have hyOutside (i : α) (hi : i ∉ coefficientSupport w) : y i = x i := by
    have hi' : i ∉ coefficientSupport w' := by simpa [hw'Support] using hi
    have hwi : w' i = 0 := by simpa [mem_coefficientSupport] using hi'
    simp [y, hwi]
  exact ⟨y, ⟨hyNe, hyComb⟩, hyConformal, hyStrict, hyOutside⟩

/-- Every nonzero dependence contains a conformal elementary dependence.
This is proved by strong induction on the finite support cardinality, using
`exists_conformal_dependence_ssubset` at each nonminimal step. -/
theorem IsDependence.exists_elementary_conformal
    {v : α → V} {x : α → ℝ} (hx : IsDependence v x) :
    ∃ a : α → ℝ, IsElementary v a ∧ ConformalTo a x := by
  generalize hn : (coefficientSupport x).ncard = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hElementary : IsElementary v x
      · exact ⟨x, hElementary, conformalTo_refl x⟩
      · have hFailure : ¬(∀ ⦃w : α → ℝ⦄, IsDependence v w →
            coefficientSupport w ⊆ coefficientSupport x →
              coefficientSupport x ⊆ coefficientSupport w) := by
          intro hminimal
          exact hElementary ⟨hx, hminimal⟩
        push Not at hFailure
        obtain ⟨w, hw, hwSub, hxNotSub⟩ := hFailure
        have hwStrict : coefficientSupport w ⊂ coefficientSupport x := by
          rw [Set.ssubset_iff_subset_ne]
          exact ⟨hwSub, fun hEq ↦ hxNotSub hEq.symm.subset⟩
        obtain ⟨y, hy, hyx, hyStrict, _⟩ :=
          exists_conformal_dependence_ssubset hx hw hwStrict
        have hcard : (coefficientSupport y).ncard < n := by
          rw [← hn]
          exact Set.ncard_lt_ncard hyStrict
        obtain ⟨a, ha, hay⟩ := ih _ hcard hy rfl
        exact ⟨a, ha, hay.trans hyx⟩

/-- Protected-coordinate version of conformal circuit extraction.  If `r`
is supported by the original dependence, the elementary conformal
dependence can be chosen to keep `r` in its support. -/
theorem IsDependence.exists_elementary_conformal_apply_ne_zero
    {v : α → V} {x : α → ℝ} (hx : IsDependence v x)
    {r : α} (hr : x r ≠ 0) :
    ∃ a : α → ℝ,
      IsElementary v a ∧ ConformalTo a x ∧ a r ≠ 0 := by
  generalize hn : (coefficientSupport x).ncard = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      obtain ⟨z, hzElementary, hzConformal⟩ :=
        hx.exists_elementary_conformal
      by_cases hzr : z r = 0
      · have hzSub : coefficientSupport z ⊆ coefficientSupport x :=
          hzConformal.1
        have hzStrict : coefficientSupport z ⊂ coefficientSupport x :=
          hzSub.ssubset_of_mem_notMem
            (mem_coefficientSupport.mpr hr)
            (by simpa [mem_coefficientSupport] using hzr)
        obtain ⟨y, hy, hyx, hyStrict, hyOutside⟩ :=
          exists_conformal_dependence_ssubset hx
            hzElementary.1 hzStrict
        have hrNotZ : r ∉ coefficientSupport z := by
          simpa [mem_coefficientSupport] using hzr
        have hyr : y r ≠ 0 := by
          rw [hyOutside r hrNotZ]
          exact hr
        have hcard : (coefficientSupport y).ncard < n := by
          rw [← hn]
          exact Set.ncard_lt_ncard hyStrict
        obtain ⟨a, haElementary, hay, har⟩ := ih _ hcard hy hyr rfl
        exact ⟨a, haElementary, hay.trans hyx, har⟩
      · exact ⟨z, hzElementary, hzConformal, hzr⟩

theorem IsElementary.isDependence {v : α → V} {a : α → ℝ}
    (ha : IsElementary v a) : IsDependence v a :=
  ha.1

theorem IsElementary.ne_zero {v : α → V} {a : α → ℝ}
    (ha : IsElementary v a) : a ≠ 0 :=
  ha.1.1

theorem IsElementary.combination_eq_zero {v : α → V} {a : α → ℝ}
    (ha : IsElementary v a) : combination v a = 0 :=
  ha.1.2

theorem IsElementary.support_nonempty {v : α → V} {a : α → ℝ}
    (ha : IsElementary v a) : (coefficientSupport a).Nonempty := by
  rw [Set.nonempty_def]
  simpa [Function.ne_iff] using ha.ne_zero

theorem IsElementary.support_eq_of_subset
    {v : α → V} {a b : α → ℝ}
    (ha : IsElementary v a) (hb : IsElementary v b)
    (hab : coefficientSupport a ⊆ coefficientSupport b) :
    coefficientSupport a = coefficientSupport b := by
  exact Set.Subset.antisymm hab (hb.2 ha.isDependence hab)

/-- Two elementary dependences with nested supports are scalar multiples.
The scalar is necessarily nonzero. -/
theorem IsElementary.exists_eq_smul_of_support_subset
    {v : α → V} {a b : α → ℝ}
    (ha : IsElementary v a) (hb : IsElementary v b)
    (hab : coefficientSupport a ⊆ coefficientSupport b) :
    ∃ c : ℝ, c ≠ 0 ∧ b = c • a := by
  have hsupp : coefficientSupport a = coefficientSupport b :=
    ha.support_eq_of_subset hb hab
  obtain ⟨i, hai⟩ := ha.support_nonempty
  have haiNe : a i ≠ 0 := mem_coefficientSupport.mp hai
  have hbiNe : b i ≠ 0 := by
    apply mem_coefficientSupport.mp
    rw [← hsupp]
    exact hai
  let c : ℝ := b i / a i
  let d : α → ℝ := b - c • a
  have hdEq : d = b + (-c) • a := by
    ext j
    dsimp [d]
    ring
  have hdComb : combination v d = 0 := by
    rw [hdEq, combination_add, combination_smul,
      hb.combination_eq_zero, ha.combination_eq_zero]
    simp
  have hdSupport : coefficientSupport d ⊆ coefficientSupport a := by
    intro j hj
    have hj' : j ∈ coefficientSupport (b + (-c) • a) := by
      rwa [← hdEq]
    have hjUnion := coefficientSupport_add_subset b ((-c) • a) hj'
    rcases hjUnion with hjb | hja
    · rw [hsupp]
      exact hjb
    · exact (coefficientSupport_smul_subset (-c) a) (by
        simpa [neg_smul] using hja)
  have hdi : d i = 0 := by
    simp [d, c, haiNe]
  have hdZero : d = 0 := by
    by_contra hdNe
    have hdDep : IsDependence v d := ⟨hdNe, hdComb⟩
    have haiInD : i ∈ coefficientSupport d := ha.2 hdDep hdSupport hai
    exact (mem_coefficientSupport.mp haiInD) hdi
  have hba : b = c • a := by
    have := sub_eq_zero.mp hdZero
    exact this
  refine ⟨c, ?_, hba⟩
  intro hc
  apply hbiNe
  rw [hba, hc]
  simp

/-- Consequently the signed circuits on nested supports agree up to global
sign reversal. -/
theorem IsElementary.signVector_eq_or_eq_neg_of_support_subset
    {v : α → V} {a b : α → ℝ}
    (ha : IsElementary v a) (hb : IsElementary v b)
    (hab : coefficientSupport a ⊆ coefficientSupport b) :
    signVector a = signVector b ∨ signVector a = -(signVector b) := by
  obtain ⟨c, hcNe, hba⟩ :=
    ha.exists_eq_smul_of_support_subset hb hab
  rcases lt_or_gt_of_ne hcNe with hcNeg | hcPos
  · right
    apply SignedSubset.ext
    · ext i
      change (0 < a i) ↔ b i < 0
      rw [hba]
      change (0 < a i) ↔ c * a i < 0
      constructor <;> intro h <;> nlinarith
    · ext i
      change (a i < 0) ↔ 0 < b i
      rw [hba]
      change (a i < 0) ↔ 0 < c * a i
      constructor <;> intro h <;> nlinarith
  · left
    apply SignedSubset.ext
    · ext i
      change (0 < a i) ↔ 0 < b i
      rw [hba]
      change (0 < a i) ↔ 0 < c * a i
      constructor <;> intro h <;> nlinarith
    · ext i
      change (a i < 0) ↔ b i < 0
      rw [hba]
      change (a i < 0) ↔ c * a i < 0
      constructor <;> intro h <;> nlinarith

theorem IsElementary.neg {v : α → V} {a : α → ℝ}
    (ha : IsElementary v a) : IsElementary v (-a) := by
  constructor
  · simpa using
      ha.isDependence.smul (c := (-1 : ℝ)) (by norm_num)
  · intro b hb hsub
    rw [coefficientSupport_neg] at hsub ⊢
    exact ha.2 hb hsub

/-- The cancellation dependence used in weak circuit elimination.  Positive
absolute-value multipliers cancel the chosen opposite coordinate.  The
assumption that the two sign vectors are not global negatives is used
exactly to prove that the resulting dependence is nonzero. -/
theorem exists_elimination_dependence
    {v : α → V} {a b : α → ℝ} {u : α}
    (ha : IsElementary v a) (hb : IsElementary v b)
    (hne : signVector a ≠ -(signVector b))
    (hu : (signVector a).OppositeAt (signVector b) u) :
    ∃ x : α → ℝ,
      IsDependence v x ∧ x u = 0 ∧
        (signVector x).positive ⊆
          ((signVector a).positive ∪ (signVector b).positive) \ {u} ∧
        (signVector x).negative ⊆
          ((signVector a).negative ∪ (signVector b).negative) \ {u} := by
  have hau : a u ≠ 0 := by
    rcases hu with hu | hu
    · exact ne_of_gt hu.1
    · exact ne_of_lt hu.1
  have hbu : b u ≠ 0 := by
    rcases hu with hu | hu
    · exact ne_of_lt hu.2
    · exact ne_of_gt hu.2
  let p : ℝ := |b u|
  let q : ℝ := |a u|
  have hpPos : 0 < p := by simpa [p] using abs_pos.mpr hbu
  have hqPos : 0 < q := by simpa [q] using abs_pos.mpr hau
  let x : α → ℝ := p • a + q • b
  have hxComb : combination v x = 0 := by
    change combination v (p • a + q • b) = 0
    rw [combination_add, combination_smul, combination_smul,
      ha.combination_eq_zero, hb.combination_eq_zero]
    simp
  have hxU : x u = 0 := by
    rcases hu with hu | hu
    · rcases hu with ⟨hauPos, hbuNeg⟩
      change 0 < a u at hauPos
      change b u < 0 at hbuNeg
      simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul, p, q,
        abs_of_neg hbuNeg, abs_of_pos hauPos]
      ring
    · rcases hu with ⟨hauNeg, hbuPos⟩
      change a u < 0 at hauNeg
      change 0 < b u at hbuPos
      simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul, p, q,
        abs_of_pos hbuPos, abs_of_neg hauNeg]
      ring
  have hxNe : x ≠ 0 := by
    intro hxZero
    let c : ℝ := -p / q
    have hcNeg : c < 0 := by
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hpPos) hqPos
    have hba : b = c • a := by
      funext i
      have hxi := congrFun hxZero i
      simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at hxi
      change b i = c * a i
      dsimp [c]
      calc
        b i = (-p * a i) / q :=
          (eq_div_iff hqPos.ne').2 (by nlinarith)
        _ = (-p / q) * a i := by field_simp
    have hsignB : signVector b = -(signVector a) := by
      rw [hba]
      exact signVector_smul_of_neg hcNeg a
    apply hne
    rw [hsignB]
    simp
  have hxPos : (signVector x).positive ⊆
      ((signVector a).positive ∪ (signVector b).positive) \ {u} := by
    intro i hi
    change 0 < x i at hi
    constructor
    · change 0 < a i ∨ 0 < b i
      by_cases hai : 0 < a i
      · exact Or.inl hai
      · by_cases hbi : 0 < b i
        · exact Or.inr hbi
        · have hai' : a i ≤ 0 := le_of_not_gt hai
          have hbi' : b i ≤ 0 := le_of_not_gt hbi
          have hpNonneg : 0 ≤ p := hpPos.le
          have hqNonneg : 0 ≤ q := hqPos.le
          have hpa : p * a i ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hpNonneg hai'
          have hqb : q * b i ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hqNonneg hbi'
          dsimp [x] at hi
          change 0 < p * a i + q * b i at hi
          linarith
    · intro hiu
      have hiEq : i = u := by simpa using hiu
      subst i
      exact (ne_of_gt hi) hxU
  have hxNeg : (signVector x).negative ⊆
      ((signVector a).negative ∪ (signVector b).negative) \ {u} := by
    intro i hi
    change x i < 0 at hi
    constructor
    · change a i < 0 ∨ b i < 0
      by_cases hai : a i < 0
      · exact Or.inl hai
      · by_cases hbi : b i < 0
        · exact Or.inr hbi
        · have hai' : 0 ≤ a i := le_of_not_gt hai
          have hbi' : 0 ≤ b i := le_of_not_gt hbi
          have hpa : 0 ≤ p * a i := mul_nonneg hpPos.le hai'
          have hqb : 0 ≤ q * b i := mul_nonneg hqPos.le hbi'
          dsimp [x] at hi
          change p * a i + q * b i < 0 at hi
          linarith
    · intro hiu
      have hiEq : i = u := by simpa using hiu
      subst i
      exact (ne_of_lt hi) hxU
  exact ⟨x, ⟨hxNe, hxComb⟩, hxU, hxPos, hxNeg⟩

/-- The signed circuits of a real vector configuration. -/
def signedCircuits (v : α → V) : Set (SignedSubset α) :=
  {C | ∃ a : α → ℝ, IsElementary v a ∧ signVector a = C}

/-- The realizable oriented matroid determined by a finite real vector
configuration.  Its weak elimination field is supplied by explicit linear
cancellation followed by conformal support minimization. -/
noncomputable def data (v : α → V) : OrientedMatroid.Data α where
  circuits := signedCircuits v
  support_nonempty := by
    rintro C ⟨a, ha, rfl⟩
    rw [signVector_support]
    exact ha.support_nonempty
  neg_mem := by
    rintro C ⟨a, ha, rfl⟩
    exact ⟨-a, ha.neg, by simp⟩
  eq_or_eq_neg_of_support_subset := by
    rintro C D ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hsub
    rw [signVector_support, signVector_support] at hsub
    exact ha.signVector_eq_or_eq_neg_of_support_subset hb hsub
  weakElimination := by
    rintro C D ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hne u hu
    obtain ⟨x, hx, hxU, hxPos, hxNeg⟩ :=
      exists_elimination_dependence ha hb hne hu
    obtain ⟨z, hzElementary, hzConformal⟩ :=
      hx.exists_elementary_conformal
    let Z := signVector z
    have hzLe : Z ≤ signVector x := hzConformal.signVector_le
    refine ⟨Z, ⟨z, hzElementary, rfl⟩, ?_⟩
    constructor
    · intro i hi
      exact hxPos (hzLe.1 hi)
    · intro i hi
      exact hxNeg (hzLe.2 hi)

@[simp]
theorem mem_data_circuits {v : α → V} {C : SignedSubset α} :
    C ∈ (data v).circuits ↔
      ∃ a : α → ℝ, IsElementary v a ∧ signVector a = C :=
  Iff.rfl

/-- Extend coefficients on a subtype by zero. -/
noncomputable def extendByZero (X : Set α) (g : X → ℝ) : α → ℝ :=
  fun i ↦ if hi : i ∈ X then g ⟨i, hi⟩ else 0

omit [Fintype α] in theorem coefficientSupport_extendByZero_subset (X : Set α) (g : X → ℝ) :
    coefficientSupport (extendByZero X g) ⊆ X := by
  intro i hi
  by_contra hiX
  exact (mem_coefficientSupport.mp hi) (by simp [extendByZero, hiX])

theorem combination_eq_sum_subtype_of_support_subset
    (v : α → V) (a : α → ℝ) (X : Set α)
    (haX : coefficientSupport a ⊆ X) :
    combination v a = ∑ i : X, a i • v i := by
  classical
  calc
    combination v a =
        ∑ i ∈ Finset.univ.filter (fun i ↦ i ∈ X), a i • v i := by
      rw [combination]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hiNotFilter
      have hiNotX : i ∉ X := by simpa using hiNotFilter
      have hai : a i = 0 := by
        by_contra hai
        exact hiNotX (haX (mem_coefficientSupport.mpr hai))
      simp [hai]
    _ = ∑ i : X, a i • v i := by
      apply Finset.sum_subtype
      intro i
      simp

theorem combination_extendByZero (v : α → V) (X : Set α) (g : X → ℝ) :
    combination v (extendByZero X g) = ∑ i : X, g i • v i := by
  rw [combination_eq_sum_subtype_of_support_subset v _ X
    (coefficientSupport_extendByZero_subset X g)]
  apply Finset.sum_congr rfl
  intro i _
  simp [extendByZero]

/-- Oriented-matroid independence for the realizable construction is
exactly ordinary linear independence of the indexed subfamily. -/
theorem isIndependent_iff_linearIndependent (v : α → V) (X : Set α) :
    (data v).IsIndependent X ↔
      LinearIndependent ℝ (fun i : X ↦ v i) := by
  constructor
  · intro hIndependent
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hgi
    let a : α → ℝ := extendByZero X g
    have haComb : combination v a = 0 := by
      change combination v (extendByZero X g) = 0
      rw [combination_extendByZero]
      exact hg
    have haNe : a ≠ 0 := by
      intro hzero
      have hi := congrFun hzero i
      simp [a, extendByZero] at hi
      exact hgi hi
    obtain ⟨z, hzElementary, hzConformal⟩ :=
      (show IsDependence v a from ⟨haNe, haComb⟩).exists_elementary_conformal
    have hCircuit : (data v).IsCircuit (signVector z) :=
      ⟨z, hzElementary, rfl⟩
    have hSupport : (signVector z).support ⊆ X := by
      rw [signVector_support]
      exact hzConformal.1.trans (coefficientSupport_extendByZero_subset X g)
    exact (hIndependent hCircuit) hSupport
  · intro hLinearIndependent C hCircuit hCX
    obtain ⟨a, haElementary, rfl⟩ := hCircuit
    have haX : coefficientSupport a ⊆ X := by
      simpa [signVector_support] using hCX
    have haSum : ∑ i : X, a i • v i = 0 := by
      rw [← combination_eq_sum_subtype_of_support_subset v a X haX]
      exact haElementary.combination_eq_zero
    have haOnX : ∀ i : X, a i = 0 :=
      Fintype.linearIndependent_iff.mp hLinearIndependent
        (fun i : X ↦ a i) haSum
    apply haElementary.ne_zero
    funext i
    by_cases hiX : i ∈ X
    · exact haOnX ⟨i, hiX⟩
    · by_contra hai
      exact hiX (haX (mem_coefficientSupport.mpr hai))

/-- If a subconfiguration is literally an indexed linear basis, then its
index range is a basis of the realizable oriented matroid. -/
theorem isBasis_range_of_basis
    {β : Type*} [Fintype β] (v : α → V) (e : β ↪ α)
    (B : Module.Basis β ℝ V) (hv : ∀ i, v (e i) = B i) :
    (data v).IsBasis (Set.range e) := by
  let eRange : β ≃ Set.range e := Equiv.ofInjective e e.injective
  have hLinearIndependent :
      LinearIndependent ℝ (fun x : Set.range e ↦ v x) := by
    have hB := B.linearIndependent.comp eRange.symm eRange.symm.injective
    convert hB using 1
    funext x
    have hx : e (eRange.symm x) = x.1 :=
      congrArg Subtype.val (eRange.apply_symm_apply x)
    rw [← hx, hv]
    rfl
  refine ⟨(isIndependent_iff_linearIndependent v _).mpr
    hLinearIndependent, ?_⟩
  intro Y hY hRange y hy
  by_contra hyNotRange
  have hLIY : LinearIndependent ℝ (fun z : Y ↦ v z) :=
    (isIndependent_iff_linearIndependent v Y).mp hY
  let yi : Y := ⟨y, hy⟩
  have hyNotSpan :=
    (linearIndependent_iff_notMem_span.mp hLIY) yi
  apply hyNotSpan
  have hvSpan : v y ∈ Submodule.span ℝ (Set.range B) := by
    rw [B.span_eq]
    trivial
  apply (Submodule.span_mono ?_) hvSpan
  intro z hz
  obtain ⟨i, rfl⟩ := hz
  rw [← hv i]
  let eiY : Y := ⟨e i, hRange ⟨i, rfl⟩⟩
  refine ⟨eiY, ?_, rfl⟩
  constructor
  · trivial
  · intro hei
    apply hyNotRange
    refine ⟨i, ?_⟩
    exact congrArg Subtype.val hei

/-- Acyclicity of a realizable oriented matroid is exactly the absence of a
nonzero nonnegative linear dependence. -/
theorem isAcyclic_iff_no_nonnegative_dependence (v : α → V) :
    (data v).IsAcyclic ↔
      ∀ a : α → ℝ, (∀ i, 0 ≤ a i) → combination v a = 0 → a = 0 := by
  constructor
  · intro hAcyclic a haNonneg haComb
    by_contra haNe
    obtain ⟨z, hzElementary, hzConformal⟩ :=
      (show IsDependence v a from ⟨haNe, haComb⟩).exists_elementary_conformal
    have hCircuit : (data v).IsCircuit (signVector z) :=
      ⟨z, hzElementary, rfl⟩
    obtain ⟨i, hiNeg⟩ := hAcyclic hCircuit
    change z i < 0 at hiNeg
    have haiNe : a i ≠ 0 := mem_coefficientSupport.mp
      (hzConformal.1 (mem_coefficientSupport.mpr (ne_of_lt hiNeg)))
    have haiPos : 0 < a i := lt_of_le_of_ne (haNonneg i) (Ne.symm haiNe)
    nlinarith [hzConformal.2 i]
  · intro hNo C hCircuit
    obtain ⟨a, haElementary, rfl⟩ := hCircuit
    by_contra hNegative
    have haNonneg : ∀ i, 0 ≤ a i := by
      intro i
      apply le_of_not_gt
      intro hi
      apply hNegative
      exact ⟨i, hi⟩
    exact haElementary.ne_zero
      (hNo a haNonneg haElementary.combination_eq_zero)

/-- For an element outside `X`, oriented-matroid convex-hull membership in
the realizable construction is exactly representability as a nonnegative
linear combination of the vectors indexed by `X`. -/
theorem memConvexHull_iff_exists_nonnegative_combination
    (v : α → V) {b : α} {X : Set α} (hbX : b ∉ X) :
    (data v).MemConvexHull b X ↔
      ∃ a : α → ℝ,
        (∀ i, 0 ≤ a i) ∧
          coefficientSupport a ⊆ X ∧ combination v a = v b := by
  constructor
  · intro hConvex
    rcases hConvex with hb | ⟨C, hC, hCpos, hCneg⟩
    · exact (hbX hb).elim
    · obtain ⟨a, haElementary, rfl⟩ := hC
      have habNeg : a b < 0 := by
        have : b ∈ (signVector a).negative := by rw [hCneg]; simp
        exact this
      let d : ℝ := -a b
      have hdPos : 0 < d := by dsimp [d]; linarith
      let y : α → ℝ := (1 / d) • (a - Pi.single b (a b))
      have hyNonneg : ∀ i, 0 ≤ y i := by
        intro i
        have hinner : 0 ≤ (a - Pi.single b (a b) : α → ℝ) i := by
          by_cases hib : i = b
          · subst i
            simp
          · have haiNonneg : 0 ≤ a i := by
              apply le_of_not_gt
              intro haiNeg
              have hiNeg : i ∈ (signVector a).negative := haiNeg
              have hib' : i = b := by simpa [hCneg] using hiNeg
              exact hib hib'
            simpa [Pi.single_apply, hib] using haiNonneg
        change 0 ≤ (1 / d) * (a - Pi.single b (a b) : α → ℝ) i
        exact mul_nonneg (one_div_nonneg.mpr hdPos.le) hinner
      have hySupport : coefficientSupport y ⊆ X := by
        intro i hi
        have hyiNe : y i ≠ 0 := mem_coefficientSupport.mp hi
        have hib : i ≠ b := by
          intro hib
          subst i
          apply hyiNe
          simp [y]
        have haiNonneg : 0 ≤ a i := by
          apply le_of_not_gt
          intro haiNeg
          have hiNeg : i ∈ (signVector a).negative := haiNeg
          have hib' : i = b := by simpa [hCneg] using hiNeg
          exact hib hib'
        have hyi : y i = (1 / d) * a i := by
          simp [y, hib]
        have haiNe : a i ≠ 0 := by
          intro hai
          apply hyiNe
          rw [hyi, hai, mul_zero]
        have haiPos : 0 < a i := lt_of_le_of_ne haiNonneg (Ne.symm haiNe)
        exact hCpos haiPos
      have hyCombination : combination v y = v b := by
        change combination v ((1 / d) •
          (a - Pi.single b (a b))) = v b
        rw [combination_smul, combination_sub, combination_single,
          haElementary.combination_eq_zero, zero_sub]
        rw [show -(a b • v b) = (-a b) • v b by simp, smul_smul]
        have hscalar : (1 / d) * -a b = 1 := by
          dsimp [d]
          exact div_mul_cancel₀ 1 (neg_ne_zero.mpr (ne_of_lt habNeg))
        rw [hscalar, one_smul]
      exact ⟨y, hyNonneg, hySupport, hyCombination⟩
  · rintro ⟨a, haNonneg, haSupport, haCombination⟩
    have hab : a b = 0 := by
      by_contra hab
      exact hbX (haSupport (mem_coefficientSupport.mpr hab))
    let x : α → ℝ := a - Pi.single b 1
    have hxCombination : combination v x = 0 := by
      change combination v (a - Pi.single b 1) = 0
      rw [combination_sub, combination_single, haCombination, one_smul,
        sub_self]
    have hxb : x b = -1 := by simp [x, hab]
    have hxNe : x ≠ 0 := by
      intro hzero
      have := congrFun hzero b
      rw [hxb] at this
      norm_num at this
    obtain ⟨z, hzElementary, hzConformal, hzbNe⟩ :=
      (show IsDependence v x from ⟨hxNe, hxCombination⟩).exists_elementary_conformal_apply_ne_zero
        (r := b) (by rw [hxb]; norm_num)
    have hzbNeg : z b < 0 := by
      have hprod := hzConformal.2 b
      rw [hxb] at hprod
      have hzbNonpos : z b ≤ 0 := by linarith
      exact lt_of_le_of_ne hzbNonpos hzbNe
    have hzNegative : (signVector z).negative = {b} := by
      ext i
      constructor
      · intro hziNeg
        change z i < 0 at hziNeg
        change i = b
        by_contra hib
        have hxi : x i = a i := by simp [x, hib]
        have hxiNe : x i ≠ 0 := mem_coefficientSupport.mp
          (hzConformal.1
            (mem_coefficientSupport.mpr (ne_of_lt hziNeg)))
        have hxiPos : 0 < x i := by
          have haiNe : a i ≠ 0 := by rwa [hxi] at hxiNe
          rw [hxi]
          exact lt_of_le_of_ne (haNonneg i) (Ne.symm haiNe)
        nlinarith [hzConformal.2 i]
      · intro hib
        have : i = b := by simpa using hib
        subst i
        exact hzbNeg
    have hzPositive : (signVector z).positive ⊆ X := by
      intro i hziPos
      change 0 < z i at hziPos
      have hib : i ≠ b := by
        intro hib
        subst i
        linarith
      have hxiNe : x i ≠ 0 := mem_coefficientSupport.mp
        (hzConformal.1
          (mem_coefficientSupport.mpr (ne_of_gt hziPos)))
      have haiNe : a i ≠ 0 := by
        simpa [x, Pi.single_apply, hib] using hxiNe
      exact haSupport (mem_coefficientSupport.mpr haiNe)
    exact Or.inr ⟨signVector z, ⟨z, hzElementary, rfl⟩,
      hzPositive, hzNegative⟩

end RealizableOrientedMatroid

end BeyondSperner
