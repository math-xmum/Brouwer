import BeyondSperner.Scarf.Classical
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Scarf's proof of Brouwer's fixed-point theorem

This file formalizes the geometric part of Section 3.  We use coordinatewise
distance, which is equivalent to the Euclidean metric in finite dimension and
gives a particularly transparent quantitative form of Lemma 3.1.
-/

namespace BeyondSperner

open Classical Filter Set
open scoped Topology

namespace ScarfBrouwer

variable {I V : Type*}

/-- The standard simplex in the finite coordinate space `I → ℝ`. -/
def standardSimplex [Fintype I] : Set (I → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

theorem standardSimplex_nonempty [Fintype I] [Nonempty I] :
    (standardSimplex : Set (I → ℝ)).Nonempty := by
  let n : ℝ := Fintype.card I
  refine ⟨fun _ ↦ n⁻¹, ?_⟩
  constructor
  · intro i
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · have hn : (n : ℝ) ≠ 0 := by
      simp [n, Fintype.card_ne_zero]
    simp [n, hn]

/-- The orders on a finite sample refine its coordinate orders, exactly as in
Section 3: strict coordinate inequality implies strict order inequality. -/
def RefinesCoordinates (F : IndexedLinearOrders I V) (p : V → I → ℝ) : Prop :=
  ∀ i x y, p x i < p y i → (F i).lt x y

/-- A canonical choice of coordinate-refining orders.  The second
lexicographic component only breaks ties and has no geometric content. -/
noncomputable def coordinateOrders [Fintype V]
    (p : V → I → ℝ) : IndexedLinearOrders I V where
  order i :=
    let e := Fintype.equivFin V
    LinearOrder.lift' (α := V) (β := ℝ ×ₗ Fin (Fintype.card V))
      (fun v ↦ (toLex (p v i, e v) : ℝ ×ₗ Fin (Fintype.card V)))
      (fun _x _y h ↦ e.injective
        (congrArg (fun z : ℝ ×ₗ Fin (Fintype.card V) ↦ (ofLex z).2) h))

theorem coordinateOrders_refines [Fintype V] (p : V → I → ℝ) :
    RefinesCoordinates (coordinateOrders p) p := by
  intro i x y hxy
  change (toLex (p x i, (Fintype.equivFin V) x) :
      ℝ ×ₗ Fin (Fintype.card V)) < toLex (p y i, (Fintype.equivFin V) y)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hxy)

/-- Coordinatewise `δ`-density in the standard simplex.  For finite `I` this
is equivalent to density for the sup norm. -/
def IsCoordDense [Fintype I] (δ : ℝ) (p : V → I → ℝ) : Prop :=
  ∀ z ∈ (standardSimplex : Set (I → ℝ)),
    ∃ v : V, ∀ i, |p v i - z i| < δ

/-- Coordinate lower bounds defining `Δ(σ,C)`. -/
noncomputable def lowerBound [Fintype V] [DecidableEq I]
    (F : IndexedLinearOrders I V) (p : V → I → ℝ)
    (σ : Finset V) (hσ : σ.Nonempty) (C : Finset I) (i : I) : ℝ :=
  if i ∈ C then p (@Finset.min' V (F i) σ hσ) i else 0

/-- The geometric simplex `Δ(σ,C)` from Section 3. -/
def envelope [Fintype I] [Fintype V] [DecidableEq I]
    (F : IndexedLinearOrders I V) (p : V → I → ℝ)
    (σ : Finset V) (hσ : σ.Nonempty) (C : Finset I) : Set (I → ℝ) :=
  {z | (∑ i, z i) = 1 ∧ ∀ i, lowerBound F p σ hσ C i ≤ z i}

theorem lowerBound_nonneg [Fintype I] [Fintype V] [DecidableEq I]
    (F : IndexedLinearOrders I V) (p : V → I → ℝ)
    (hp : ∀ v, p v ∈ (standardSimplex : Set (I → ℝ)))
    (σ : Finset V) (hσ : σ.Nonempty) (C : Finset I) (i : I) :
    0 ≤ lowerBound F p σ hσ C i := by
  simp only [lowerBound]
  split_ifs
  · exact (hp _).1 i
  · exact le_rfl

/-- Every sampled point of `σ` lies in `Δ(σ,C)`. -/
theorem sample_mem_envelope [Fintype I] [Fintype V] [DecidableEq I]
    (F : IndexedLinearOrders I V) (p : V → I → ℝ)
    (hp : ∀ v, p v ∈ (standardSimplex : Set (I → ℝ)))
    (href : RefinesCoordinates F p)
    (σ : Finset V) (hσ : σ.Nonempty) (C : Finset I)
    {v : V} (hv : v ∈ σ) : p v ∈ envelope F p σ hσ C := by
  refine ⟨(hp v).2, fun i ↦ ?_⟩
  by_cases hi : i ∈ C
  · rw [lowerBound, if_pos hi]
    let : LinearOrder V := F i
    let m : V := @Finset.min' V (F i) σ hσ
    have hmle : (F i).le m v := @Finset.min'_le V (F i) σ v hv
    exact le_of_not_gt fun hvm ↦
      (not_lt_of_ge hmle) (href i v m hvm)
  · rw [lowerBound, if_neg hi]
    exact (hp v).1 i

/-- Every geometric envelope is contained in the standard simplex. -/
theorem envelope_subset_standardSimplex
    [Fintype I] [Fintype V] [DecidableEq I]
    (F : IndexedLinearOrders I V) (p : V → I → ℝ)
    (hp : ∀ v, p v ∈ (standardSimplex : Set (I → ℝ)))
    (σ : Finset V) (hσ : σ.Nonempty) (C : Finset I) :
    envelope F p σ hσ C ⊆ standardSimplex := by
  intro z hz
  exact ⟨fun i ↦ (lowerBound_nonneg F p hp σ hσ C i).trans (hz.2 i), hz.1⟩

/-- Dominance says that no sample point can satisfy all defining inequalities
of `Δ(σ,C)` strictly.  This is the key combinatorial-geometric observation
inside the proof of Lemma 3.1. -/
theorem no_sample_strictly_above_lowerBounds
    [Fintype I] [Fintype V] [DecidableEq I]
    (F : IndexedLinearOrders I V) (p : V → I → ℝ)
    (href : RefinesCoordinates F p)
    (σ : Finset V) (hσ : σ.Nonempty) (C : Finset I)
    (hdom : F.IsDominant σ C) (v : V) :
    ¬ ∀ i, lowerBound F p σ hσ C i < p v i := by
  intro hstrict
  obtain ⟨i, hiC, hvi⟩ := hdom.2 v
  let : LinearOrder V := F i
  let m : V := @Finset.min' V (F i) σ hσ
  have hmσ : m ∈ σ := @Finset.min'_mem V (F i) σ hσ
  have hvim : (F i).le v m := hvi m hmσ
  have hcoord : p m i < p v i := by
    simpa [lowerBound, hiC, m] using hstrict i
  exact (not_lt_of_ge hvim) (href i m v hcoord)

/-- Every coordinate not in `C` vanishes at some point of `Δ(σ,C)`.
This is the face-intersection assertion immediately before Lemma 3.1. -/
theorem exists_mem_envelope_coord_eq_zero
    [Fintype I] [Fintype V] [DecidableEq I]
    (F : IndexedLinearOrders I V) (p : V → I → ℝ)
    (hp : ∀ v, p v ∈ (standardSimplex : Set (I → ℝ)))
    (href : RefinesCoordinates F p)
    (σ : Finset V) (hσ : σ.Nonempty) (C : Finset I) (hC : C.Nonempty)
    {i : I} (hiC : i ∉ C) :
    ∃ q ∈ envelope F p σ hσ C, q i = 0 := by
  let a : I → ℝ := lowerBound F p σ hσ C
  let L : ℝ := 1 - ∑ k, a k
  let v₀ : V := hσ.choose
  have hv₀σ : v₀ ∈ σ := hσ.choose_spec
  have hpv₀ := sample_mem_envelope F p hp href σ hσ C hv₀σ
  have hLnonneg : 0 ≤ L := by
    have hsumle : ∑ k, a k ≤ ∑ k, p v₀ k :=
      Finset.sum_le_sum fun k _ ↦ hpv₀.2 k
    rw [(hp v₀).2] at hsumle
    dsimp [L]
    linarith
  let j : I := hC.choose
  have hjC : j ∈ C := hC.choose_spec
  have hij : i ≠ j := fun hij ↦ hiC (hij ▸ hjC)
  let q : I → ℝ := fun k ↦ a k + if k = j then L else 0
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · simp only [q, Finset.sum_add_distrib]
    rw [Fintype.sum_ite_eq']
    dsimp [L]
    ring
  · intro k
    dsimp [q]
    exact le_add_of_nonneg_right (by split_ifs <;> positivity)
  · simp [q, a, lowerBound, hiC, hij]

/-- Quantitative Lemma 3.1 in coordinatewise form.  If the sample is
`δ`-dense and `|I|·δ < ε`, every coordinate diameter of
`Δ(σ,C)` is less than `ε`. -/
theorem envelope_coordDiameter_lt
    [Fintype I] [Nonempty I] [Fintype V] [DecidableEq I]
    (F : IndexedLinearOrders I V) (p : V → I → ℝ)
    (hp : ∀ v, p v ∈ (standardSimplex : Set (I → ℝ)))
    (href : RefinesCoordinates F p)
    {δ ε : ℝ} (hδ : 0 < δ)
    (hscale : (Fintype.card I : ℝ) * δ < ε)
    (hdense : IsCoordDense δ p)
    (σ : Finset V) (hσ : σ.Nonempty) (C : Finset I)
    (hdom : F.IsDominant σ C) :
    ∀ x ∈ envelope F p σ hσ C,
      ∀ y ∈ envelope F p σ hσ C,
        ∀ i, |x i - y i| < ε := by
  let a : I → ℝ := lowerBound F p σ hσ C
  let L : ℝ := 1 - ∑ i, a i
  have ha (i : I) : 0 ≤ a i := lowerBound_nonneg F p hp σ hσ C i
  let v₀ : V := hσ.choose
  have hv₀σ : v₀ ∈ σ := hσ.choose_spec
  have hpv₀ := sample_mem_envelope F p hp href σ hσ C hv₀σ
  have hLnonneg : 0 ≤ L := by
    have hsumle : ∑ i, a i ≤ ∑ i, p v₀ i :=
      Finset.sum_le_sum fun i _ ↦ hpv₀.2 i
    rw [(hp v₀).2] at hsumle
    dsimp [L]
    linarith
  have hLlt : L < ε := by
    by_contra hnot
    have hεL : ε ≤ L := le_of_not_gt hnot
    have hLpos : 0 < L := lt_of_lt_of_le (lt_of_le_of_lt
      (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hδ)) hscale) hεL
    let n : ℝ := Fintype.card I
    have hn : 0 < n := by
      dsimp [n]
      exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
    let q : I → ℝ := fun i ↦ a i + L / n
    have hqSimplex : q ∈ (standardSimplex : Set (I → ℝ)) := by
      constructor
      · intro i
        exact add_nonneg (ha i) (div_nonneg hLnonneg (le_of_lt hn))
      · simp only [q, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        have hn0 : n ≠ 0 := ne_of_gt hn
        dsimp [L, n]
        field_simp
        ring
    obtain ⟨v, hvclose⟩ := hdense q hqSimplex
    apply no_sample_strictly_above_lowerBounds F p href σ hσ C hdom v
    intro i
    have hδsmall : δ < L / n := by
      have hnδ : n * δ < L := lt_of_lt_of_le hscale hεL
      exact (lt_div_iff₀ hn).mpr (by simpa [mul_comm] using hnδ)
    have habs := hvclose i
    rw [abs_lt] at habs
    change a i < p v i
    dsimp [q] at habs
    linarith
  intro x hx y hy i
  have hresx (j : I) : 0 ≤ x j - a j := sub_nonneg.mpr (hx.2 j)
  have hresy (j : I) : 0 ≤ y j - a j := sub_nonneg.mpr (hy.2 j)
  have hsumx : ∑ j, (x j - a j) = L := by
    simp only [Finset.sum_sub_distrib, hx.1]
    rfl
  have hsumy : ∑ j, (y j - a j) = L := by
    simp only [Finset.sum_sub_distrib, hy.1]
    rfl
  have hxL : x i - a i ≤ L := by
    rw [← hsumx]
    exact Finset.single_le_sum (fun j _ ↦ hresx j) (Finset.mem_univ i)
  have hyL : y i - a i ≤ L := by
    rw [← hsumy]
    exact Finset.single_le_sum (fun j _ ↦ hresy j) (Finset.mem_univ i)
  rw [abs_lt]
  constructor
  · have := hresx i
    linarith
  · have := hresy i
    linarith

section ColoringApproximation

variable [Fintype I] [Nonempty I]

/-- If two points have the same coordinate sum, some coordinate of the first
is at most the corresponding coordinate of the second. -/
theorem exists_coordinate_le_of_sum_eq (x y : I → ℝ)
    (hsum : (∑ i, x i) = ∑ i, y i) : ∃ i, x i ≤ y i := by
  by_contra h
  push Not at h
  let i₀ : I := Classical.choice (inferInstance : Nonempty I)
  have hlt : (∑ i, y i) < ∑ i, x i :=
    Finset.sum_lt_sum (fun i _ ↦ (h i).le)
      ⟨i₀, Finset.mem_univ i₀, h i₀⟩
  linarith

/-- Scarf's coloring rule (14): choose a coordinate with `xᵢ ≤ f(x)ᵢ`. -/
noncomputable def scarfColor
    (f : (I → ℝ) → I → ℝ) (hf : MapsTo f standardSimplex standardSimplex)
    (p : V → I → ℝ) (hp : ∀ v, p v ∈ (standardSimplex : Set (I → ℝ))) :
    V → I := fun v ↦ Classical.choose
      (exists_coordinate_le_of_sum_eq (p v) (f (p v)) ((hp v).2.trans (hf (hp v)).2.symm))

theorem scarfColor_spec
    (f : (I → ℝ) → I → ℝ) (hf : MapsTo f standardSimplex standardSimplex)
    (p : V → I → ℝ) (hp : ∀ v, p v ∈ (standardSimplex : Set (I → ℝ)))
    (v : V) :
    p v (scarfColor f hf p hp v) ≤ f (p v) (scarfColor f hf p hp v) :=
  Classical.choose_spec
    (exists_coordinate_le_of_sum_eq (p v) (f (p v)) ((hp v).2.trans (hf (hp v)).2.symm))

/-- Compactness of the standard simplex supplies finite coordinatewise dense
samples at every positive scale. -/
theorem exists_finite_coordDense (δ : ℝ) (hδ : 0 < δ) :
    ∃ X : Finset (I → ℝ), X.Nonempty ∧
      (∀ x ∈ X, x ∈ (standardSimplex : Set (I → ℝ))) ∧
      ∀ z ∈ (standardSimplex : Set (I → ℝ)),
        ∃ x ∈ X, ∀ i, |x i - z i| < δ := by
  have hcompact : IsCompact (standardSimplex : Set (I → ℝ)) := by
    change IsCompact (stdSimplex ℝ I)
    exact isCompact_stdSimplex ℝ I
  obtain ⟨t, hts, htfin, hcover⟩ := hcompact.finite_cover_balls hδ
  let X : Finset (I → ℝ) := htfin.toFinset
  have hXdense : ∀ z ∈ (standardSimplex : Set (I → ℝ)),
      ∃ x ∈ X, ∀ i, |x i - z i| < δ := by
    intro z hz
    have hzcover := hcover hz
    obtain ⟨x, hxcover⟩ := Set.mem_iUnion.mp hzcover
    obtain ⟨hxt, hzball⟩ := Set.mem_iUnion.mp hxcover
    refine ⟨x, by simpa [X] using hxt, fun i ↦ ?_⟩
    have hcoord := (dist_pi_lt_iff hδ).mp hzball i
    simpa [Real.dist_eq, abs_sub_comm] using hcoord
  have hXnonempty : X.Nonempty := by
    obtain ⟨z, hz⟩ := standardSimplex_nonempty (I := I)
    obtain ⟨x, hx, _⟩ := hXdense z hz
    exact ⟨x, hx⟩
  refine ⟨X, hXnonempty, ?_, hXdense⟩
  intro x hx
  exact hts (by simpa [X] using hx)

/-- The finite approximation delivered by classical Scarf plus Lemma 3.1.
There is a small geometric envelope and, for every coordinate, a point in it
at which Scarf's inequality holds. -/
theorem exists_small_envelope_with_coordinate_witnesses
    [Fintype V] [Nonempty V] [DecidableEq I] [DecidableEq V]
    (F : IndexedLinearOrders I V) (p : V → I → ℝ)
    (hp : ∀ v, p v ∈ (standardSimplex : Set (I → ℝ)))
    (href : RefinesCoordinates F p)
    {δ ε : ℝ} (hδ : 0 < δ)
    (hscale : (Fintype.card I : ℝ) * δ < ε)
    (hdense : IsCoordDense δ p)
    (f : (I → ℝ) → I → ℝ) (hf : MapsTo f standardSimplex standardSimplex) :
    ∃ (C : Finset I) (σ : Finset V) (hσ : σ.Nonempty)
        (x : I → ℝ),
      F.IsCell σ C ∧ x ∈ envelope F p σ hσ C ∧
      (∀ y ∈ envelope F p σ hσ C,
        ∀ i, |x i - y i| < ε) ∧
      ∀ i, ∃ y ∈ envelope F p σ hσ C, y i ≤ f y i := by
  let c : V → I := scarfColor f hf p hp
  obtain ⟨C, σ, hcell, hcolor⟩ := ClassicalScarf.exists_colorfulCell F c
  have hC : C.Nonempty := hcell.1.1
  have hσ : σ.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcell.2]
    exact Finset.card_pos.mpr hC
  let v₀ : V := hσ.choose
  have hv₀σ : v₀ ∈ σ := hσ.choose_spec
  let x : I → ℝ := p v₀
  have hx : x ∈ envelope F p σ hσ C :=
    sample_mem_envelope F p hp href σ hσ C hv₀σ
  have hdiam := envelope_coordDiameter_lt F p hp href hδ hscale hdense
    σ hσ C hcell.1
  refine ⟨C, σ, hσ, x, hcell, hx, hdiam x hx, fun i ↦ ?_⟩
  by_cases hiC : i ∈ C
  · have hiImage : i ∈ σ.image c := by simpa [hcolor] using hiC
    obtain ⟨v, hvσ, hcvi⟩ := Finset.mem_image.mp hiImage
    refine ⟨p v, sample_mem_envelope F p hp href σ hσ C hvσ, ?_⟩
    simpa [c, hcvi] using scarfColor_spec f hf p hp v
  · obtain ⟨q, hq, hqi⟩ :=
      exists_mem_envelope_coord_eq_zero F p hp href σ hσ C hC hiC
    refine ⟨q, hq, ?_⟩
    rw [hqi]
    exact (hf (envelope_subset_standardSimplex F p hp σ hσ C hq)).1 i

/-- Intrinsic finite approximation statement, with the finite sample and its
orders existentially discharged. -/
theorem exists_close_coordinate_witnesses
    [DecidableEq I]
    (ε : ℝ) (hε : 0 < ε)
    (f : (I → ℝ) → I → ℝ) (hf : MapsTo f standardSimplex standardSimplex) :
    ∃ x ∈ (standardSimplex : Set (I → ℝ)),
      ∀ i, ∃ y ∈ (standardSimplex : Set (I → ℝ)),
        dist x y < ε ∧ y i ≤ f y i := by
  let n : ℝ := Fintype.card I
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
  let δ : ℝ := ε / (2 * n)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hn)
  have hscale : (Fintype.card I : ℝ) * δ < ε := by
    dsimp [δ, n] at *
    field_simp
    nlinarith
  obtain ⟨X, hXne, hXsimplex, hXdense⟩ :=
    exists_finite_coordDense (I := I) δ hδ
  let V := {x : I → ℝ // x ∈ X}
  let : Fintype V := Finset.fintypeCoeSort X
  let : Nonempty V := ⟨⟨hXne.choose, hXne.choose_spec⟩⟩
  let p : V → I → ℝ := fun v ↦ v.1
  have hp : ∀ v, p v ∈ (standardSimplex : Set (I → ℝ)) := by
    intro v
    exact hXsimplex v.1 v.2
  have hdense : IsCoordDense δ p := by
    intro z hz
    obtain ⟨x, hxX, hxclose⟩ := hXdense z hz
    exact ⟨⟨x, hxX⟩, hxclose⟩
  let F : IndexedLinearOrders I V := coordinateOrders p
  obtain ⟨C, σ, hσ, x, hcell, hx, hdiam, hwitness⟩ :=
    exists_small_envelope_with_coordinate_witnesses F p hp
      (coordinateOrders_refines p) hδ hscale hdense f hf
  refine ⟨x, envelope_subset_standardSimplex F p hp σ hσ C hx, fun i ↦ ?_⟩
  obtain ⟨y, hy, hyineq⟩ := hwitness i
  refine ⟨y, envelope_subset_standardSimplex F p hp σ hσ C hy, ?_, hyineq⟩
  rw [dist_pi_lt_iff hε]
  intro j
  simpa [Real.dist_eq] using hdiam y hy j

/-- Brouwer's fixed-point theorem on the finite standard simplex, proved by
Scarf's finite approximations.  No fixed-point theorem from the library is
used in this proof. -/
theorem scarf_brouwer_fixedPoint
    [DecidableEq I]
    (f : (I → ℝ) → I → ℝ) (hcont : ContinuousOn f standardSimplex)
    (hf : MapsTo f standardSimplex standardSimplex) :
    ∃ x ∈ (standardSimplex : Set (I → ℝ)), f x = x := by
  let η : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hηpos (n : ℕ) : 0 < η n := by
    dsimp [η]
    positivity
  let A (n : ℕ) := exists_close_coordinate_witnesses (I := I)
    (η n) (hηpos n) f hf
  let x : ℕ → (I → ℝ) := fun n ↦ (A n).choose
  have hx (n : ℕ) : x n ∈ (standardSimplex : Set (I → ℝ)) :=
    (A n).choose_spec.1
  let y : ℕ → I → (I → ℝ) := fun n i ↦ ((A n).choose_spec.2 i).choose
  have hy_mem (n : ℕ) (i : I) :
      y n i ∈ (standardSimplex : Set (I → ℝ)) :=
    ((A n).choose_spec.2 i).choose_spec.1
  have hy_close (n : ℕ) (i : I) : dist (x n) (y n i) < η n :=
    ((A n).choose_spec.2 i).choose_spec.2.1
  have hy_ineq (n : ℕ) (i : I) : y n i i ≤ f (y n i) i :=
    ((A n).choose_spec.2 i).choose_spec.2.2
  have hcompact : IsCompact (standardSimplex : Set (I → ℝ)) := by
    change IsCompact (stdSimplex ℝ I)
    exact isCompact_stdSimplex ℝ I
  obtain ⟨z, hz, φ, hφmono, hxlim⟩ := hcompact.tendsto_subseq hx
  have hηlim : Tendsto (fun n ↦ η (φ n)) atTop (𝓝 0) := by
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      hφmono.tendsto_atTop
  have hle (i : I) : z i ≤ f z i := by
    let ys : ℕ → (I → ℝ) := fun n ↦ y (φ n) i
    have hyslim : Tendsto ys atTop (𝓝 z) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hxlim) (ε / 2) (by linarith)
      obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hηlim) (ε / 2) (by linarith)
      refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
      have hxz : dist (x (φ n)) z < ε / 2 := hN₁ n (le_trans (Nat.le_max_left _ _) hn)
      have hηdist : dist (η (φ n)) 0 < ε / 2 :=
        hN₂ n (le_trans (Nat.le_max_right _ _) hn)
      have hηsmall : η (φ n) < ε / 2 := by
        simpa [Real.dist_eq, abs_of_nonneg (le_of_lt (hηpos (φ n)))] using hηdist
      calc
        dist (ys n) z ≤ dist (ys n) (x (φ n)) + dist (x (φ n)) z :=
          dist_triangle _ _ _
        _ < η (φ n) + ε / 2 :=
          add_lt_add (by simpa [ys, dist_comm] using hy_close (φ n) i) hxz
        _ < ε := by linarith
    have hcoordLeft : Tendsto (fun n ↦ ys n i) atTop (𝓝 (z i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hyslim
    have hysWithin : Tendsto ys atTop (𝓝[standardSimplex] z) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hyslim, Eventually.of_forall fun n ↦ hy_mem (φ n) i⟩
    have hflim : Tendsto (fun n ↦ f (ys n)) atTop (𝓝 (f z)) :=
      (hcont z hz).tendsto.comp hysWithin
    have hcoordRight : Tendsto (fun n ↦ f (ys n) i) atTop (𝓝 (f z i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hflim
    exact le_of_tendsto_of_tendsto' hcoordLeft hcoordRight fun n ↦ hy_ineq (φ n) i
  have hfix : f z = z := by
    funext i
    apply le_antisymm
    · by_contra hnot
      have hstrict : z i < f z i := lt_of_not_ge hnot
      have hsumlt : (∑ j, z j) < ∑ j, f z j :=
        Finset.sum_lt_sum (fun j _ ↦ hle j)
          ⟨i, Finset.mem_univ i, hstrict⟩
      rw [hz.2, (hf hz).2] at hsumlt
      exact (lt_irrefl 1 hsumlt).elim
    · exact hle i
  exact ⟨z, hz, hfix⟩

/-- Standard subtype formulation of Brouwer's fixed-point theorem on the
simplex. -/
theorem scarf_brouwer_fixedPoint_subtype
    [DecidableEq I]
    (f : standardSimplex (I := I) → standardSimplex (I := I))
    (hcont : Continuous f) : ∃ x, f x = x := by
  let z₀ : I → ℝ := (standardSimplex_nonempty (I := I)).choose
  have hz₀ : z₀ ∈ (standardSimplex : Set (I → ℝ)) :=
    (standardSimplex_nonempty (I := I)).choose_spec
  let g : (I → ℝ) → I → ℝ := fun x ↦
    if hx : x ∈ (standardSimplex : Set (I → ℝ)) then (f ⟨x, hx⟩).1 else z₀
  have hgMaps : MapsTo g standardSimplex standardSimplex := by
    intro x hx
    simp [g, hx]
  have hgCont : ContinuousOn g standardSimplex := by
    intro x hx
    rw [continuousWithinAt_iff_continuousAt_domRestrict g hx]
    have hc : Continuous (fun u : standardSimplex (I := I) ↦ (f u).1) :=
      continuous_subtype_val.comp hcont
    simpa [g] using hc.continuousAt
  obtain ⟨x, hx, hgfix⟩ := scarf_brouwer_fixedPoint g hgCont hgMaps
  let xs : standardSimplex (I := I) := ⟨x, hx⟩
  refine ⟨xs, Subtype.ext ?_⟩
  simpa [xs, g, hx] using hgfix

end ColoringApproximation

end ScarfBrouwer

end BeyondSperner
