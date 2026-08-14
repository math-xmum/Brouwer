import BeyondSperner.FixedPoint.ScarfBrouwer
import BeyondSperner.Scarf.Vector
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card

/-!
# Scarf's route to Kakutani: the vector-coloring layer

This file begins Section 9.  It deliberately separates the immediate
fixed-point case from the case in which the associated color

`c(x) = f(x) - x + b`

lands in the required set `M \ {b}`.  The printed proof suppresses this
case distinction: `c(x) = b` is equivalent to `f(x) = x`.

The first completed result is Lemma 9.1.  The associated finite vector
configuration is packaged as the literal raw-`φ` interface of
`VectorScarf`, and boundedness of equation (30) is derived from the
coordinate-sum argument rather than assumed.
-/

namespace BeyondSperner

open Classical Filter Set
open scoped BigOperators Topology

namespace KakutaniScarf

variable {I X : Type*}

/-- The barycenter of the standard simplex in `I → ℝ`. -/
noncomputable def barycenter [Fintype I] : I → ℝ :=
  fun _ ↦ (Fintype.card I : ℝ)⁻¹

theorem barycenter_sum [Fintype I] [Nonempty I] :
    ∑ i, barycenter (I := I) i = 1 := by
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [barycenter, hcard]

theorem barycenter_nonneg [Fintype I] (i : I) :
    0 ≤ barycenter (I := I) i := by
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem barycenter_mem_standardSimplex [Fintype I] [Nonempty I] :
    barycenter (I := I) ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)) :=
  ⟨barycenter_nonneg, barycenter_sum⟩

theorem barycenter_ne_zero [Fintype I] [Nonempty I] :
    barycenter (I := I) ≠ 0 := by
  intro hzero
  have hsum := barycenter_sum (I := I)
  rw [hzero] at hsum
  simp at hsum

/-- In positive dimension the barycenter is different from every standard
basis vector.  The `Nontrivial I` hypothesis is essential: for the
zero-dimensional simplex the barycenter is its unique basis vector. -/
theorem barycenter_ne_single [Fintype I] [DecidableEq I]
    [Nontrivial I] (i : I) :
    barycenter (I := I) ≠ Pi.single i 1 := by
  intro h
  obtain ⟨j, hji⟩ := exists_ne i
  have hcardPos : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hj := congrFun h j
  have hij : i ≠ j := hji.symm
  simp [barycenter, hij, ne_of_gt hcardPos] at hj

/-- Section 9's vector color `c(x) = f(x) - x + b`. -/
noncomputable def vectorColor [Fintype I]
    (p f : X → I → ℝ) (x : X) : I → ℝ :=
  f x - p x + barycenter

theorem vectorColor_sum [Fintype I] [Nonempty I]
    (p f : X → I → ℝ)
    (hp : ∀ x, p x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hf : ∀ x, f x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (x : X) :
    ∑ i, vectorColor p f x i = 1 := by
  simp only [vectorColor, Pi.add_apply, Pi.sub_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [(hp x).2, (hf x).2, barycenter_sum]
  ring

/-- The exceptional color `b` occurs exactly at an already fixed sample
point. -/
theorem vectorColor_eq_barycenter_iff [Fintype I]
    (p f : X → I → ℝ) (x : X) :
    vectorColor p f x = barycenter ↔ f x = p x := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    dsimp [vectorColor] at hi
    linarith
  · intro h
    funext i
    have hi := congrFun h i
    dsimp [vectorColor]
    rw [hi]
    simp

/-- The finite vector configuration associated with a sample map, in the
non-fixed branch.  The positive-dimensional hypothesis is exactly what
makes `b` a label separate from the standard basis. -/
noncomputable def rawData [Fintype I] [Fintype X]
    [DecidableEq I] [Nontrivial I]
    (p f : X → I → ℝ)
    (hnoFixed : ∀ x, f x ≠ p x) : VectorScarf.RawData I X where
  phi := Sum.elim (vectorColor p f) (fun i ↦ Pi.single i 1)
  b := barycenter
  b_ne_zero := barycenter_ne_zero
  b_nonneg := barycenter_nonneg
  phi_inr := fun _ ↦ rfl
  old_ne_b := by
    intro x hxb
    exact hnoFixed x ((vectorColor_eq_barycenter_iff p f x).mp hxb)
  b_ne_basis := barycenter_ne_single

@[simp]
theorem rawData_phi_inl [Fintype I] [Fintype X]
    [DecidableEq I] [Nontrivial I]
    (p f : X → I → ℝ) (hnoFixed : ∀ x, f x ≠ p x) (x : X) :
    (rawData p f hnoFixed).phi (Sum.inl x) = vectorColor p f x :=
  rfl

/-- Every vector in the associated configuration lies in the affine
hyperplane whose coordinate sum is one. -/
theorem rawData_sum_vector_eq_one [Fintype I] [Fintype X]
    [DecidableEq I] [Nontrivial I]
    (p f : X → I → ℝ)
    (hp : ∀ x, p x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hf : ∀ x, f x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hnoFixed : ∀ x, f x ≠ p x)
    (m : (rawData p f hnoFixed).Label) :
    ∑ i, (rawData p f hnoFixed).toFramework.vector m i = 1 := by
  let R := rawData p f hnoFixed
  change ∑ i, m.1 i = 1
  have hm : m.1 = R.b ∨ ∃ z : X ⊕ I, R.phi z = m.1 := by
    simpa [R, VectorScarf.RawData.labels] using m.2
  rcases hm with hz | ⟨z, hz⟩
  · rw [hz]
    simpa [R, rawData] using (barycenter_sum (I := I))
  · rw [← hz]
    cases z with
    | inl x =>
        simpa [R, rawData] using vectorColor_sum p f hp hf x
    | inr i => simp [R, rawData]

/-- Lemma 9.1, pointwise part: every coefficient of every nonnegative
solution of equation (30) is at most one. -/
theorem lemma9_1_coefficient_le_one [Fintype I] [Fintype X]
    [DecidableEq I] [Nontrivial I]
    (p f : X → I → ℝ)
    (hp : ∀ x, p x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hf : ∀ x, f x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hnoFixed : ∀ x, f x ≠ p x)
    {a : (rawData p f hnoFixed).Label → ℝ}
    (ha : (rawData p f hnoFixed).toFramework.IsNonnegativeSolution a)
    (m : (rawData p f hnoFixed).Label) :
    a m ≤ 1 :=
  (rawData p f hnoFixed).toFramework
    |>.coefficient_le_one_of_sum_vector_eq_one
      (rawData_sum_vector_eq_one p f hp hf hnoFixed) ha m

/-- Lemma 9.1, boundedness part. -/
theorem lemma9_1_isBounded [Fintype I] [Fintype X]
    [DecidableEq I] [Nontrivial I]
    (p f : X → I → ℝ)
    (hp : ∀ x, p x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hf : ∀ x, f x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hnoFixed : ∀ x, f x ≠ p x) :
    Bornology.IsBounded
      (rawData p f hnoFixed).toFramework.nonnegativeSolutions :=
  (rawData p f hnoFixed).toFramework
    |>.isBounded_nonnegativeSolutions_of_sum_vector_eq_one
      (rawData_sum_vector_eq_one p f hp hf hnoFixed)

/-- The Scarf conclusion for a single Section 9 sample, after the immediate
fixed-point branch has been excluded. -/
theorem exists_scarf_solution_of_noFixed
    [Fintype I] [Fintype X] [Nonempty X]
    [DecidableEq I] [DecidableEq X] [LinearOrder I] [Nontrivial I]
    (orders : IndexedLinearOrders I X)
    (p f : X → I → ℝ)
    (hp : ∀ x, p x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hf : ∀ x, f x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hnoFixed : ∀ x, f x ≠ p x) :
    ∃ S : Finset (X ⊕ I),
      (rawData p f hnoFixed).IsSolution orders S :=
  (rawData p f hnoFixed).scarf orders
    (lemma9_1_isBounded p f hp hf hnoFixed)

/-- The literal vector set in formula (34). -/
noncomputable def cellVectorImage [Fintype I] [Fintype X]
    [DecidableEq I]
    (p f : X → I → ℝ) (C : Finset I) (τ : Finset X) :
    Finset (I → ℝ) :=
  τ.image (vectorColor p f) ∪
    (Finset.univ \ C).image (fun i ↦ Pi.single i 1)

/-- The Section 9 coloring on the vertex subtype of the associated
simplex-family. -/
noncomputable def cellColoring
    [Fintype I] [Fintype X] [Nonempty X]
    [DecidableEq I] [DecidableEq X]
    [Nontrivial I]
    (orders : IndexedLinearOrders I X)
    (p f : X → I → ℝ) (hnoFixed : ∀ x, f x ≠ p x) :
    VectorColoring.Framework.Coloring
      (rawData p f hnoFixed).toFramework orders.associatedFamily :=
  fun x ↦ (rawData p f hnoFixed).coloring x.1

/-- The native completed vector image used by Theorem 7.2 is exactly
formula (34), with no remaining label-level encoding. -/
theorem completedVectorImage_eq_cellVectorImage
    [Fintype I] [Fintype X] [Nonempty X]
    [DecidableEq I] [DecidableEq X]
    [LinearOrder I] [Nontrivial I]
    (orders : IndexedLinearOrders I X)
    (p f : X → I → ℝ) (hnoFixed : ∀ x, f x ≠ p x)
    (C : Finset I) (τ : Finset X)
    (hτ : τ ∈ orders.associatedFamily.complex C) :
    (rawData p f hnoFixed).toFramework.vectorImage
        ((rawData p f hnoFixed).toFramework.completedImage
          orders.associatedFamily
          (cellColoring orders p f hnoFixed) C τ hτ) =
      cellVectorImage p f C τ := by
  let R := rawData p f hnoFixed
  let F := R.toFramework
  ext w
  change w ∈ F.vectorImage
      (F.completedImage orders.associatedFamily
        (cellColoring orders p f hnoFixed) C τ hτ) ↔
    w ∈ cellVectorImage p f C τ
  constructor
  · intro hw
    obtain ⟨m, hm, hmw⟩ := Finset.mem_image.mp hw
    rcases Finset.mem_union.mp hm with hmColor | hmBasis
    · obtain ⟨v, hv, hvm⟩ := Finset.mem_image.mp hmColor
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨v.1, v.2, ?_⟩
      have hvm' : (R.coloring v.1).1 = m := by
        simpa [cellColoring, R] using hvm
      calc
        vectorColor p f v.1 = R.phi (Sum.inl v.1) := by
          simp [R]
        _ = F.vector (R.coloring v.1).1 := by
          simpa [F] using (R.coloring_vector v.1).symm
        _ = F.vector m := congrArg F.vector hvm'
        _ = w := hmw
    · obtain ⟨i, hi, him⟩ := Finset.mem_image.mp hmBasis
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨i, hi, ?_⟩
      have hbasis : Pi.single i 1 = F.vector (F.basis i) := by
        rw [F.basis_vector]
        ext j
        by_cases hij : i = j <;> simp [hij]
      calc
        Pi.single i 1 = F.vector (F.basis i) := hbasis
        _ = F.vector m := congrArg F.vector him
        _ = w := hmw
  · intro hw
    rcases Finset.mem_union.mp hw with hwColor | hwBasis
    · obtain ⟨x, hx, hxw⟩ := Finset.mem_image.mp hwColor
      apply Finset.mem_image.mpr
      refine ⟨(R.coloring x).1, ?_, ?_⟩
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨⟨x, hx⟩, by simp, ?_⟩
        simp [cellColoring, R]
      · calc
          F.vector (R.coloring x).1 = R.phi (Sum.inl x) := by
            simpa [F] using R.coloring_vector x
          _ = vectorColor p f x := by
            simp [R]
          _ = w := hxw
    · obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hwBasis
      apply Finset.mem_image.mpr
      refine ⟨F.basis i, ?_, ?_⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
      · have hbasis : F.vector (F.basis i) = Pi.single i 1 := by
          rw [F.basis_vector]
          ext j
          by_cases hij : i = j <;> simp [hij]
        exact hbasis.trans hiw

/-- The exact cell-form conclusion used in Lemma 9.2.  Both the basis and
the coefficient function are indexed by the literal vector set (34). -/
def IsCellSolution [Fintype I] [Fintype X]
    [DecidableEq I] [DecidableEq X]
    (orders : IndexedLinearOrders I X)
    (p f : X → I → ℝ) (C : Finset I) (τ : Finset X) : Prop :=
  orders.IsCell τ C ∧
    ∃ B : Module.Basis (cellVectorImage p f C τ : Set (I → ℝ))
        ℝ (I → ℝ),
      (∀ w, B w = w.1) ∧
        ∃ q : {w : I → ℝ // w ∈ cellVectorImage p f C τ} → ℝ,
          (∀ w, 0 ≤ q w) ∧
            ∑ w, q w • w.1 = barycenter

/-- Formula (34), indexed uniformly by `I`: indices in `C` use the color
at the corresponding minimum of the cell, and the remaining indices use
standard basis vectors. -/
noncomputable def indexedCellVector
    [Fintype I] [Fintype X] [DecidableEq I]
    (orders : IndexedLinearOrders I X) (p f : X → I → ℝ)
    (C : Finset I) (τ : Finset X) (hτ : τ.Nonempty) (i : I) : I → ℝ :=
  if _hi : i ∈ C then
    vectorColor p f (@Finset.min' X (orders i) τ hτ)
  else Pi.single i 1

theorem image_indexedCellVector
    [Fintype I] [Fintype X] [DecidableEq I] [DecidableEq X]
    (orders : IndexedLinearOrders I X) (p f : X → I → ℝ)
    (C : Finset I) (τ : Finset X) (hτ : τ.Nonempty)
    (hcell : orders.IsCell τ C) :
    Finset.univ.image (indexedCellVector orders p f C τ hτ) =
      cellVectorImage p f C τ := by
  have hmins := orders.eq_image_min_of_isDominant hτ hcell.1
  ext w
  constructor
  · intro hw
    obtain ⟨i, _, hiw⟩ := Finset.mem_image.mp hw
    by_cases hiC : i ∈ C
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨@Finset.min' X (orders i) τ hτ,
        @Finset.min'_mem X (orders i) τ hτ, ?_⟩
      simpa [indexedCellVector, hiC] using hiw
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiC⟩,
        by simpa [indexedCellVector, hiC] using hiw⟩
  · intro hw
    rcases Finset.mem_union.mp hw with hwColor | hwBasis
    · obtain ⟨x, hxτ, hxw⟩ := Finset.mem_image.mp hwColor
      have hxImage := (Finset.ext_iff.mp hmins x).mp hxτ
      obtain ⟨i, hiC, hix⟩ :=
        (@Finset.mem_image I X (Classical.decEq X)
          (fun i ↦ @Finset.min' X (orders i) τ hτ) C x).mp hxImage
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [indexedCellVector, dif_pos hiC]
      exact (congrArg (vectorColor p f) hix).trans hxw
    · obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hwBasis
      have hiC : i ∉ C := (Finset.mem_sdiff.mp hi).2
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_univ _, by
        simpa [indexedCellVector, hiC] using hiw⟩

/-- Equation (35): reindex the literal coefficients supplied by the vector
Scarf theorem by the fixed coordinate type `I`. -/
theorem IsCellSolution.exists_indexed_coefficients
    [Fintype I] [Fintype X] [DecidableEq I] [DecidableEq X]
    {orders : IndexedLinearOrders I X} {p f : X → I → ℝ}
    {C : Finset I} {τ : Finset X}
    (h : IsCellSolution orders p f C τ) :
    ∃ (hτ : τ.Nonempty) (y : I → ℝ),
      (∀ i, 0 ≤ y i) ∧
        ∑ i, y i • indexedCellVector orders p f C τ hτ i =
          barycenter := by
  rcases h with ⟨hcell, B, hB, q, hq, hcomb⟩
  have hτ : τ.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcell.2]
    exact Finset.card_pos.mpr hcell.1.1
  let g : I → I → ℝ := indexedCellVector orders p f C τ hτ
  have hgImage : Finset.univ.image g = cellVectorImage p f C τ :=
    image_indexedCellVector orders p f C τ hτ hcell
  have hcardCell : (cellVectorImage p f C τ).card = Fintype.card I := by
    have hfinrank := Module.finrank_eq_card_basis B
    rw [Module.finrank_pi] at hfinrank
    calc
      (cellVectorImage p f C τ).card =
          (cellVectorImage p f C τ : Set (I → ℝ)).ncard :=
        (Set.ncard_coe_finset _).symm
      _ = Fintype.card
          {w : I → ℝ // w ∈ (cellVectorImage p f C τ : Set (I → ℝ))} :=
        (Set.fintypeCard_eq_ncard _).symm
      _ = Fintype.card I := hfinrank.symm
  have hcardImage : (Finset.univ.image g).card =
      (Finset.univ : Finset I).card := by
    rw [hgImage, hcardCell, Finset.card_univ]
  have hgInj : Function.Injective g := by
    intro i j hij
    exact (Finset.card_image_iff.mp hcardImage)
      (Finset.mem_univ i) (Finset.mem_univ j) hij
  let e : I ≃ {w : I → ℝ // w ∈ cellVectorImage p f C τ} :=
    Equiv.ofBijective
      (fun i ↦ ⟨g i, by
        rw [← hgImage]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
      ⟨fun i j hij ↦ hgInj (congrArg Subtype.val hij), by
        intro w
        have hw : w.1 ∈ Finset.univ.image g := by
          rw [hgImage]
          exact w.2
        obtain ⟨i, _, hiw⟩ := Finset.mem_image.mp hw
        refine ⟨i, Subtype.ext ?_⟩
        exact hiw⟩
  let y : I → ℝ := fun i ↦ q (e i)
  refine ⟨hτ, y, fun i ↦ hq (e i), ?_⟩
  change ∑ i, y i • g i = barycenter
  calc
    ∑ i, y i • g i =
        ∑ w : {w : I → ℝ // w ∈ cellVectorImage p f C τ},
          q w • w.1 := by
      apply Fintype.sum_equiv e
      intro i
      rfl
    _ = barycenter := hcomb

/-- The coefficients in (35) actually lie in `[0,1]`.  This is again a
consequence of the unit coordinate sum, not an extra compactness
assumption. -/
theorem IsCellSolution.exists_indexed_coefficients_bounded
    [Fintype I] [Fintype X] [Nonempty I]
    [DecidableEq I] [DecidableEq X]
    {orders : IndexedLinearOrders I X} {p f : X → I → ℝ}
    {C : Finset I} {τ : Finset X}
    (hp : ∀ x, p x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hf : ∀ x, f x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (h : IsCellSolution orders p f C τ) :
    ∃ (hτ : τ.Nonempty) (y : I → ℝ),
      (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
        ∑ i, y i • indexedCellVector orders p f C τ hτ i =
          barycenter := by
  obtain ⟨hτ, y, hy, heq⟩ := h.exists_indexed_coefficients
  have hunit (i : I) :
      ∑ j, indexedCellVector orders p f C τ hτ i j = 1 := by
    by_cases hi : i ∈ C
    · rw [indexedCellVector, dif_pos hi]
      exact vectorColor_sum p f hp hf _
    · simp [indexedCellVector, hi]
  have hsumY : ∑ i, y i = 1 := by
    calc
      ∑ i, y i = ∑ i, y i *
          (∑ j, indexedCellVector orders p f C τ hτ i j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hunit i, mul_one]
      _ = ∑ i, ∑ j,
          y i * indexedCellVector orders p f C τ hτ i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ j, ∑ i,
          y i * indexedCellVector orders p f C τ hτ i j :=
        Finset.sum_comm
      _ = ∑ j, (∑ i,
          y i • indexedCellVector orders p f C τ hτ i) j := by
        simp [Finset.sum_apply]
      _ = ∑ j, barycenter (I := I) j := by rw [heq]
      _ = 1 := barycenter_sum
  refine ⟨hτ, y, fun i ↦ ⟨hy i, ?_⟩, heq⟩
  rw [← hsumY]
  exact Finset.single_le_sum (fun j _ ↦ hy j) (Finset.mem_univ i)

/-- Cell form of the Section 9 Scarf application in the branch with no
sample fixed point. -/
theorem exists_cellSolution_of_noFixed
    [Fintype I] [Fintype X] [Nonempty X]
    [DecidableEq I] [DecidableEq X] [LinearOrder I] [Nontrivial I]
    (orders : IndexedLinearOrders I X)
    (p f : X → I → ℝ)
    (hp : ∀ x, p x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hf : ∀ x, f x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hnoFixed : ∀ x, f x ≠ p x) :
    ∃ C : Finset I, ∃ τ : Finset X,
      IsCellSolution orders p f C τ := by
  let R := rawData p f hnoFixed
  let F := R.toFramework
  let D := orders.associatedFamily
  let c := cellColoring orders p f hnoFixed
  obtain ⟨C, τ, hτ, hC, hcard, B, hB, q, hq, hcomb⟩ :=
    F.theorem7_2 (lemma9_1_isBounded p f hp hf hnoFixed)
      D orders.associatedFamily_isChainSimplex c
  have hcell : orders.IsCell τ C := by
    have hassoc : orders.IsAssociatedSimplex C τ :=
      (Finset.mem_filter.mp hτ).2
    rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg hC.ne_empty] at hassoc
    rcases hassoc with hτempty | ⟨σ, hσcell, hτσ⟩
    · subst τ
      have hCcard : C.card = 0 := by simpa using hcard.symm
      exact (Finset.card_ne_zero.mpr hC hCcard).elim
    · have hτσeq : τ = σ := Finset.eq_of_subset_of_card_le hτσ (by
        rw [hσcell.2, hcard])
      simpa [hτσeq] using hσcell
  have hImage :
      F.vectorImage (F.completedImage D c C τ hτ) =
        cellVectorImage p f C τ := by
    simpa [F, D, c, R] using
      completedVectorImage_eq_cellVectorImage
        orders p f hnoFixed C τ hτ
  refine ⟨C, τ, hcell, ?_⟩
  rw [← hImage]
  refine ⟨B, hB, q, hq, ?_⟩
  change (∑ w, q w • w.1) = R.b
  exact hcomb

/-- Correct total interface for a single sample map.  If an associated
color equals `b`, a fixed sample point has already been found; otherwise
the literal cell conclusion (34) follows. -/
theorem exists_fixed_or_cellSolution
    [Fintype I] [Fintype X] [Nonempty X]
    [DecidableEq I] [DecidableEq X] [LinearOrder I]
    (orders : IndexedLinearOrders I X)
    (p f : X → I → ℝ)
    (hp : ∀ x, p x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hf : ∀ x, f x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ))) :
    (∃ x, f x = p x) ∨
      ∃ C : Finset I, ∃ τ : Finset X,
        IsCellSolution orders p f C τ := by
  let x₀ : X := Classical.choice inferInstance
  have : Nonempty I := by
    rw [← Finset.univ_nonempty_iff]
    by_contra hEmpty
    have hEq : (Finset.univ : Finset I) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hsum := (hp x₀).2
    rw [hEq] at hsum
    simp at hsum
  rcases subsingleton_or_nontrivial I with hSub | hNontrivial
  · left
    refine ⟨x₀, funext fun i ↦ ?_⟩
    have huniv : (Finset.univ : Finset I) = {i} := by
      ext j
      simp [hSub.elim j i]
    have hpOne : p x₀ i = 1 := by
      have hsum := (hp x₀).2
      rw [huniv] at hsum
      simpa using hsum
    have hfOne : f x₀ i = 1 := by
      have hsum := (hf x₀).2
      rw [huniv] at hsum
      simpa using hsum
    exact hfOne.trans hpOne.symm
  · let : Nontrivial I := hNontrivial
    by_cases hfixed : ∃ x, f x = p x
    · exact Or.inl hfixed
    · right
      apply exists_cellSolution_of_noFixed orders p f hp hf
      intro x hx
      exact hfixed ⟨x, hx⟩

/-- A closed-graph, nonempty convex-valued self-correspondence of the
standard simplex.  This is the precise finite-dimensional Kakutani input
used below; in particular, closedness is imposed on the literal graph, not
hidden in a limit-selection oracle. -/
structure Correspondence (I : Type*) [Fintype I] where
  value : (I → ℝ) → Set (I → ℝ)
  nonempty_value : ∀ x ∈
    (ScarfBrouwer.standardSimplex : Set (I → ℝ)), (value x).Nonempty
  value_subset : ∀ x ∈
    (ScarfBrouwer.standardSimplex : Set (I → ℝ)),
      value x ⊆ ScarfBrouwer.standardSimplex
  convex_value : ∀ x, Convex ℝ (value x)
  isClosed_graph : IsClosed {p : (I → ℝ) × (I → ℝ) | p.2 ∈ value p.1}

/-- One finite sample in the sequence used in Lemma 9.2.  The finite type
`X` represents a literal finite subset after choosing an injective
enumeration; `p` records its points and `f` records the selected values. -/
structure Sample (I : Type*) [Fintype I] where
  X : Type*
  fintypeX : Fintype X
  nonemptyX : Nonempty X
  decidableEqX : DecidableEq X
  orders : IndexedLinearOrders I X
  p : X → I → ℝ
  f : X → I → ℝ
  p_mem : ∀ x, p x ∈
    (ScarfBrouwer.standardSimplex : Set (I → ℝ))
  f_mem : ∀ x, f x ∈
    (ScarfBrouwer.standardSimplex : Set (I → ℝ))
  radius : ℝ
  radius_pos : 0 < radius
  dense : ScarfBrouwer.IsCoordDense radius p
  orders_refine : ScarfBrouwer.RefinesCoordinates orders p

namespace Sample

variable [Fintype I]

/-- The cell-solution predicate with the sample's finite instances installed
internally.  This wrapper is needed because the vertex type varies with the
stage of the approximation sequence. -/
def CellSolution [DecidableEq I] (S : Sample I)
    (C : Finset I) (τ : Finset S.X) : Prop := by
  letI := S.fintypeX
  letI := S.decidableEqX
  exact IsCellSolution S.orders S.p S.f C τ

/-- A selected sample value is already an exact fixed point. -/
def HasFixed (S : Sample I) : Prop :=
  ∃ x, S.f x = S.p x

/-- The cell conclusion of formula (34) for a bundled sample. -/
def HasCellSolution [DecidableEq I] (S : Sample I)
    (C : Finset I) : Prop :=
  ∃ τ : Finset S.X, S.CellSolution C τ

theorem fixed_or_cellSolution
    [DecidableEq I] [LinearOrder I] (S : Sample I) :
    S.HasFixed ∨ ∃ C : Finset I, S.HasCellSolution C := by
  let := S.fintypeX
  let := S.nonemptyX
  let := S.decidableEqX
  rcases exists_fixed_or_cellSolution S.orders S.p S.f S.p_mem S.f_mem with
    hfixed | ⟨C, τ, hτ⟩
  · exact Or.inl hfixed
  · exact Or.inr ⟨C, τ, by simpa [CellSolution] using hτ⟩

/-- The nonemptiness proof selected from a bundled cell solution. -/
theorem cellNonempty [Nonempty I] [DecidableEq I]
    (S : Sample I) {C : Finset I} {τ : Finset S.X}
    (h : S.CellSolution C τ) : τ.Nonempty := by
  let := S.fintypeX
  let := S.decidableEqX
  have h' : IsCellSolution S.orders S.p S.f C τ := by
    simpa [CellSolution] using h
  exact (h'.exists_indexed_coefficients_bounded S.p_mem S.f_mem).choose

/-- The coefficient vector selected from equation (35). -/
noncomputable def cellCoefficients [Nonempty I] [DecidableEq I]
    (S : Sample I) {C : Finset I} {τ : Finset S.X}
    (h : S.CellSolution C τ) : I → ℝ := by
  letI := S.fintypeX
  letI := S.decidableEqX
  have h' : IsCellSolution S.orders S.p S.f C τ := by
    simpa [CellSolution] using h
  exact (h'.exists_indexed_coefficients_bounded S.p_mem S.f_mem).choose_spec.choose

theorem cellCoefficients_nonneg [Nonempty I] [DecidableEq I]
    (S : Sample I) {C : Finset I} {τ : Finset S.X}
    (h : S.CellSolution C τ) (i : I) :
    0 ≤ S.cellCoefficients h i := by
  let := S.fintypeX
  let := S.decidableEqX
  have h' : IsCellSolution S.orders S.p S.f C τ := by
    simpa [CellSolution] using h
  simpa [cellCoefficients] using
    (h'.exists_indexed_coefficients_bounded S.p_mem S.f_mem)
      |>.choose_spec.choose_spec.1 i |>.1

theorem cellCoefficients_le_one [Nonempty I] [DecidableEq I]
    (S : Sample I) {C : Finset I} {τ : Finset S.X}
    (h : S.CellSolution C τ) (i : I) :
    S.cellCoefficients h i ≤ 1 := by
  let := S.fintypeX
  let := S.decidableEqX
  have h' : IsCellSolution S.orders S.p S.f C τ := by
    simpa [CellSolution] using h
  simpa [cellCoefficients] using
    (h'.exists_indexed_coefficients_bounded S.p_mem S.f_mem)
      |>.choose_spec.choose_spec.1 i |>.2

theorem cellCoefficients_equation [Nonempty I] [DecidableEq I]
    (S : Sample I) {C : Finset I} {τ : Finset S.X}
    (h : S.CellSolution C τ) :
    ∑ i, S.cellCoefficients h i •
        (if _hi : i ∈ C then
          vectorColor S.p S.f
            (@Finset.min' S.X (S.orders i) τ (S.cellNonempty h))
        else Pi.single i 1) =
      barycenter := by
  let := S.fintypeX
  let := S.decidableEqX
  have h' : IsCellSolution S.orders S.p S.f C τ := by
    simpa [CellSolution] using h
  have heq :
      ∑ i, S.cellCoefficients h i •
          indexedCellVector S.orders S.p S.f C τ (S.cellNonempty h) i =
        barycenter := by
    simpa [cellCoefficients, cellNonempty] using
      (h'.exists_indexed_coefficients_bounded S.p_mem S.f_mem)
        |>.choose_spec.choose_spec.2
  rw [← heq]
  apply Finset.sum_congr rfl
  intro i _
  rw [indexedCellVector]

/-- Every bundled cell solution has a nonempty index set. -/
theorem cellIndex_nonempty [DecidableEq I]
    (S : Sample I) {C : Finset I} {τ : Finset S.X}
    (h : S.CellSolution C τ) : C.Nonempty := by
  let := S.fintypeX
  let := S.decidableEqX
  exact (show IsCellSolution S.orders S.p S.f C τ by
    simpa [CellSolution] using h).1.1.1

/-- The geometric envelope of a bundled sample cell, with varying finite
vertex instances hidden only at the type-theoretic boundary. -/
noncomputable def cellEnvelope [DecidableEq I]
    (S : Sample I) (C : Finset I) (τ : Finset S.X)
    (hτ : τ.Nonempty) : Set (I → ℝ) := by
  letI := S.fintypeX
  letI := S.decidableEqX
  exact ScarfBrouwer.envelope S.orders S.p τ hτ C

theorem point_mem_cellEnvelope [DecidableEq I]
    (S : Sample I) {C : Finset I} {τ : Finset S.X}
    (hτ : τ.Nonempty) {x : S.X} (hx : x ∈ τ) :
    S.p x ∈ S.cellEnvelope C τ hτ := by
  let := S.fintypeX
  let := S.decidableEqX
  simpa [cellEnvelope] using
    ScarfBrouwer.sample_mem_envelope S.orders S.p S.p_mem
      S.orders_refine τ hτ C hx

theorem cellEnvelope_coordDiameter [Nonempty I] [DecidableEq I]
    (S : Sample I) {C : Finset I} {τ : Finset S.X}
    (h : S.CellSolution C τ)
    (ε : ℝ) (hscale : (Fintype.card I : ℝ) * S.radius < ε) :
    ∀ x ∈ S.cellEnvelope C τ (S.cellNonempty h),
      ∀ x' ∈ S.cellEnvelope C τ (S.cellNonempty h),
        ∀ i, |x i - x' i| < ε := by
  let := S.fintypeX
  let := S.decidableEqX
  have h' : IsCellSolution S.orders S.p S.f C τ := by
    simpa [CellSolution] using h
  simpa [cellEnvelope] using
    ScarfBrouwer.envelope_coordDiameter_lt S.orders S.p S.p_mem
      S.orders_refine S.radius_pos hscale S.dense τ (S.cellNonempty h)
      C h'.1.1

theorem exists_cellEnvelope_coord_eq_zero
    [Nonempty I] [DecidableEq I]
    (S : Sample I) {C : Finset I} {τ : Finset S.X}
    (h : S.CellSolution C τ) {i : I} (hi : i ∉ C) :
    ∃ q ∈ S.cellEnvelope C τ (S.cellNonempty h), q i = 0 := by
  let := S.fintypeX
  let := S.decidableEqX
  simpa [cellEnvelope] using
    ScarfBrouwer.exists_mem_envelope_coord_eq_zero S.orders S.p
      S.p_mem S.orders_refine τ (S.cellNonempty h) C
      (S.cellIndex_nonempty h) hi

end Sample

/-- Lemma 9.2 with the suppressed fixed-point case restored.  Either one
of the selected maps already has an exact fixed sample point, or one fixed
index set `C` supports formula-(34) cell solutions for infinitely many
sample indices. -/
theorem lemma9_2
    [Fintype I] [DecidableEq I] [LinearOrder I]
    (samples : ℕ → Sample I) :
    (∃ k, (samples k).HasFixed) ∨
      ∃ C : Finset I,
        Set.Infinite {k : ℕ | (samples k).HasCellSolution C} := by
  by_cases hfixed : ∃ k, (samples k).HasFixed
  · exact Or.inl hfixed
  · right
    have hsolution : ∀ k, ∃ C : Finset I,
        (samples k).HasCellSolution C := by
      intro k
      rcases (samples k).fixed_or_cellSolution with hk | hk
      · exact (hfixed ⟨k, hk⟩).elim
      · exact hk
    let chosenC : ℕ → Finset I := fun k ↦ (hsolution k).choose
    have hchosen : ∀ k, (samples k).HasCellSolution (chosenC k) :=
      fun k ↦ (hsolution k).choose_spec
    obtain ⟨C, hfiber⟩ := Finite.exists_infinite_fiber chosenC
    refine ⟨C, ?_⟩
    apply (Set.infinite_coe_iff.mp hfiber).mono
    intro k hk
    have hkEq : chosenC k = C := by simpa using hk
    simpa [hkEq] using hchosen k

/-! ## Canonical finite approximations of a correspondence -/

/-- The target envelope diameter at stage `n`. -/
noncomputable def approximationScale (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem approximationScale_pos (n : ℕ) :
    0 < approximationScale n := by
  dsimp [approximationScale]
  positivity

theorem approximationScale_tendsto_zero :
    Tendsto approximationScale atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The sampling radius is chosen with a factor `2|I|`, so Lemma 3.1
gives an envelope diameter strictly below `approximationScale n`. -/
noncomputable def approximationRadius [Fintype I] (n : ℕ) : ℝ :=
  approximationScale n / (2 * (Fintype.card I : ℝ))

theorem approximationRadius_pos [Fintype I] [Nonempty I] (n : ℕ) :
    0 < approximationRadius (I := I) n := by
  apply div_pos (approximationScale_pos n)
  exact mul_pos (by norm_num) (by exact_mod_cast Fintype.card_pos)

theorem approximationRadius_scale [Fintype I] [Nonempty I] (n : ℕ) :
    (Fintype.card I : ℝ) * approximationRadius (I := I) n <
      approximationScale n := by
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hscale := approximationScale_pos n
  dsimp [approximationRadius]
  field_simp
  nlinarith

/-- The finite subset of the simplex chosen at stage `n`. -/
noncomputable def approximationPoints [Fintype I] [Nonempty I]
    (n : ℕ) : Finset (I → ℝ) :=
  (ScarfBrouwer.exists_finite_coordDense
    (approximationRadius (I := I) n)
    (approximationRadius_pos n)).choose

theorem approximationPoints_nonempty [Fintype I] [Nonempty I] (n : ℕ) :
    (approximationPoints (I := I) n).Nonempty :=
  (ScarfBrouwer.exists_finite_coordDense
    (approximationRadius (I := I) n)
    (approximationRadius_pos n)).choose_spec.1

theorem approximationPoints_mem [Fintype I] [Nonempty I]
    (n : ℕ) {x : I → ℝ} (hx : x ∈ approximationPoints (I := I) n) :
    x ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)) :=
  (ScarfBrouwer.exists_finite_coordDense
    (approximationRadius (I := I) n)
    (approximationRadius_pos n)).choose_spec.2.1 x hx

theorem approximationPoints_dense [Fintype I] [Nonempty I] (n : ℕ) :
    ∀ z ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)),
      ∃ x ∈ approximationPoints (I := I) n,
        ∀ i, |x i - z i| < approximationRadius (I := I) n :=
  (ScarfBrouwer.exists_finite_coordDense
    (approximationRadius (I := I) n)
    (approximationRadius_pos n)).choose_spec.2.2

/-- A choice of one correspondence value over every point in the finite
stage-`n` sample. -/
noncomputable def selectedValue [Fintype I] [Nonempty I]
    (K : Correspondence I) (n : ℕ)
    (x : {x : I → ℝ // x ∈ approximationPoints (I := I) n}) : I → ℝ :=
  (K.nonempty_value x.1 (approximationPoints_mem n x.2)).choose

theorem selectedValue_mem_value [Fintype I] [Nonempty I]
    (K : Correspondence I) (n : ℕ)
    (x : {x : I → ℝ // x ∈ approximationPoints (I := I) n}) :
    selectedValue K n x ∈ K.value x.1 :=
  (K.nonempty_value x.1 (approximationPoints_mem n x.2)).choose_spec

theorem selectedValue_mem_simplex [Fintype I] [Nonempty I]
    (K : Correspondence I) (n : ℕ)
    (x : {x : I → ℝ // x ∈ approximationPoints (I := I) n}) :
    selectedValue K n x ∈
      (ScarfBrouwer.standardSimplex : Set (I → ℝ)) :=
  K.value_subset x.1 (approximationPoints_mem n x.2)
    (selectedValue_mem_value K n x)

/-- The canonical finite sample passed to Lemma 9.2. -/
noncomputable def approximationSample [Fintype I] [Nonempty I]
    (K : Correspondence I) (n : ℕ) : Sample I where
  X := {x : I → ℝ // x ∈ approximationPoints (I := I) n}
  fintypeX := Finset.fintypeCoeSort _
  nonemptyX :=
    ⟨⟨(approximationPoints_nonempty n).choose,
      (approximationPoints_nonempty n).choose_spec⟩⟩
  decidableEqX := Classical.decEq _
  orders := ScarfBrouwer.coordinateOrders Subtype.val
  p := Subtype.val
  f := selectedValue K n
  p_mem := fun x ↦ approximationPoints_mem n x.2
  f_mem := selectedValue_mem_simplex K n
  radius := approximationRadius n
  radius_pos := approximationRadius_pos n
  dense := by
    intro z hz
    obtain ⟨x, hx, hclose⟩ := approximationPoints_dense n z hz
    exact ⟨⟨x, hx⟩, hclose⟩
  orders_refine := ScarfBrouwer.coordinateOrders_refines Subtype.val

/-! ## The limiting algebra in the proof of Kakutani's theorem -/

/-- The algebraic core of the last paragraph of Section 9.  It is stated
independently of topology: once equation (35) has converged, the vanishing
coordinates outside `C` force all coefficient mass onto `C`, and the
limit point is the resulting convex combination of the selected limits.

This is the step that prevents the later compactness argument from hiding
the crucial coefficient calculation behind an interface assumption. -/
theorem convex_combination_of_limit_equation
    [Fintype I] [DecidableEq I] [Nonempty I]
    (C : Finset I) (hC : C.Nonempty)
    (z : I → ℝ)
    (hz : z ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (v : I → I → ℝ)
    (hv : ∀ i ∈ C,
      v i ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (y : I → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hzOutside : ∀ i ∉ C, z i = 0)
    (heq : ∑ i, y i •
        (if i ∈ C then v i - z + barycenter else Pi.single i 1) =
      barycenter) :
    (∑ i ∈ C, y i = 1) ∧
      z = ∑ i ∈ C, y i • v i := by
  let g : I → I → ℝ := fun i ↦
    if i ∈ C then v i - z + barycenter else Pi.single i 1
  have hgSum (i : I) : ∑ j, g i j = 1 := by
    by_cases hi : i ∈ C
    · simp only [g, if_pos hi, Pi.add_apply, Pi.sub_apply,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [(hv i hi).2, hz.2, barycenter_sum]
      ring
    · simp [g, hi]
  have heqg : ∑ i, y i • g i = barycenter := by
    simpa [g] using heq
  have hsumY : ∑ i, y i = 1 := by
    calc
      ∑ i, y i = ∑ i, y i * (∑ j, g i j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hgSum i, mul_one]
      _ = ∑ i, ∑ j, y i * g i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, y i * g i j := Finset.sum_comm
      _ = ∑ j, (∑ i, y i • g i) j := by
        simp [Finset.sum_apply]
      _ = ∑ j, barycenter (I := I) j := by rw [heqg]
      _ = 1 := barycenter_sum
  have hzSumC : ∑ j ∈ C, z j = 1 := by
    calc
      ∑ j ∈ C, z j = ∑ j ∈ (Finset.univ : Finset I), z j := by
        apply Finset.sum_subset C.subset_univ
        intro j _ hjC
        exact hzOutside j hjC
      _ = 1 := hz.2
  let bC : ℝ := ∑ j ∈ C, barycenter (I := I) j
  have hbCPos : 0 < bC := by
    obtain ⟨i, hiC⟩ := hC
    have hcardPos : (0 : ℝ) < Fintype.card I := by
      exact_mod_cast Fintype.card_pos
    have hiPos : 0 < barycenter (I := I) i := by
      change 0 < (Fintype.card I : ℝ)⁻¹
      exact inv_pos.mpr hcardPos
    exact lt_of_lt_of_le hiPos
      (Finset.single_le_sum
        (fun j _ ↦ barycenter_nonneg (I := I) j) hiC)
  have hvPartialLe (i : I) (hi : i ∈ C) :
      ∑ j ∈ C, v i j ≤ 1 := by
    calc
      ∑ j ∈ C, v i j ≤ ∑ j, v i j :=
        Finset.sum_le_sum_of_subset_of_nonneg C.subset_univ
          (fun j _ _ ↦ (hv i hi).1 j)
      _ = 1 := (hv i hi).2
  have hgPartialLe (i : I) (hi : i ∈ C) :
      ∑ j ∈ C, g i j ≤ bC := by
    simp only [g, if_pos hi, Pi.add_apply, Pi.sub_apply,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    dsimp [bC]
    linarith [hvPartialLe i hi]
  have hgPartialZero (i : I) (hi : i ∉ C) :
      ∑ j ∈ C, g i j = 0 := by
    simp [g, hi]
  have hpartialEq :
      bC = ∑ i, y i * (∑ j ∈ C, g i j) := by
    calc
      bC = ∑ j ∈ C, (∑ i, y i • g i) j := by
        rw [heqg]
      _ = ∑ j ∈ C, ∑ i, y i * g i j := by
        simp [Finset.sum_apply]
      _ = ∑ i, ∑ j ∈ C, y i * g i j := by
        rw [Finset.sum_comm]
      _ = ∑ i, y i * (∑ j ∈ C, g i j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
  have hpartialRestrict :
      ∑ i, y i * (∑ j ∈ C, g i j) =
        ∑ i ∈ C, y i * (∑ j ∈ C, g i j) := by
    symm
    apply Finset.sum_subset C.subset_univ
    intro i _ hiC
    rw [hgPartialZero i hiC, mul_zero]
  have hbC_le : bC ≤ (∑ i ∈ C, y i) * bC := by
    calc
      bC = ∑ i, y i * (∑ j ∈ C, g i j) := hpartialEq
      _ = ∑ i ∈ C, y i * (∑ j ∈ C, g i j) := hpartialRestrict
      ∑ i ∈ C, y i * (∑ j ∈ C, g i j) ≤
          ∑ i ∈ C, y i * bC := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hgPartialLe i hi) (hy i)
      _ = (∑ i ∈ C, y i) * bC := by rw [Finset.sum_mul]
  have hsumCLe : ∑ i ∈ C, y i ≤ 1 := by
    rw [← hsumY]
    exact Finset.sum_le_sum_of_subset_of_nonneg C.subset_univ
      (fun i _ _ ↦ hy i)
  have hsumCGe : 1 ≤ ∑ i ∈ C, y i := by
    nlinarith
  have hsumC : ∑ i ∈ C, y i = 1 := le_antisymm hsumCLe hsumCGe
  have hyOutsideZero : ∀ i ∉ C, y i = 0 := by
    have houtsideSum : ∑ i ∈ (Finset.univ \ C), y i = 0 := by
      have hsplit := Finset.sum_sdiff C.subset_univ (f := y)
      rw [hsumY, hsumC] at hsplit
      linarith
    intro i hiC
    have hiDiff : i ∈ (Finset.univ \ C) := by simp [hiC]
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ hy j)).mp houtsideSum i hiDiff
  refine ⟨hsumC, ?_⟩
  funext j
  have heqj := congrFun heqg j
  have hrestrict :
      ∑ i, y i * g i j = ∑ i ∈ C, y i * g i j := by
    symm
    apply Finset.sum_subset C.subset_univ
    intro i _ hiC
    rw [hyOutsideZero i hiC, zero_mul]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heqj
  rw [hrestrict] at heqj
  have heqj' :
      ∑ i ∈ C, y i * (v i j - z j + barycenter (I := I) j) =
        barycenter (I := I) j := by
    calc
      ∑ i ∈ C, y i * (v i j - z j + barycenter (I := I) j) =
          ∑ i ∈ C, y i * g i j := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [g, hi]
      _ = barycenter (I := I) j := heqj
  have hdecomp :
      ∑ i ∈ C, y i * (v i j - z j + barycenter (I := I) j) =
        (∑ i ∈ C, y i * v i j) - z j + barycenter (I := I) j := by
    simp_rw [mul_add, mul_sub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, hsumC]
    ring
  rw [hdecomp] at heqj'
  simp only [Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  nlinarith

/-- A convex-valued correspondence conclusion once the topological limit
argument has produced the limiting equation. -/
theorem mem_of_limit_equation
    [Fintype I] [DecidableEq I] [Nonempty I]
    (C : Finset I) (hC : C.Nonempty)
    (z : I → ℝ)
    (hz : z ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (S : Set (I → ℝ)) (hS : Convex ℝ S)
    (v : I → I → ℝ)
    (hvSimplex : ∀ i ∈ C,
      v i ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)))
    (hvS : ∀ i ∈ C, v i ∈ S)
    (y : I → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hzOutside : ∀ i ∉ C, z i = 0)
    (heq : ∑ i, y i •
        (if i ∈ C then v i - z + barycenter else Pi.single i 1) =
      barycenter) :
    z ∈ S := by
  obtain ⟨hsum, hzcomb⟩ :=
    convex_combination_of_limit_equation C hC z hz v hvSimplex y hy
      hzOutside heq
  rw [hzcomb]
  exact hS.sum_mem (fun i _ ↦ hy i) hsum hvS

/-! ## Kakutani's theorem by the Scarf construction -/

/-- Kakutani's fixed-point theorem on a finite standard simplex, proved
through the Section 9 vector-Scarf construction.  The proof uses only the
closed graph, nonempty simplex-valued fibers, and convexity recorded in
`Correspondence`; no library fixed-point theorem is invoked. -/
theorem scarf_kakutani_fixedPoint
    [Fintype I] [Nonempty I] [DecidableEq I] [LinearOrder I]
    (K : Correspondence I) :
    ∃ z ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)),
      z ∈ K.value z := by
  let samples : ℕ → Sample I := approximationSample K
  rcases lemma9_2 samples with hfixed | hcells
  · obtain ⟨n, x, hx⟩ := hfixed
    refine ⟨(samples n).p x, (samples n).p_mem x, ?_⟩
    have hvalue : (samples n).f x ∈ K.value ((samples n).p x) := by
      simpa [samples, approximationSample] using
        selectedValue_mem_value K n x
    simpa [hx] using hvalue
  · obtain ⟨C, hCinf⟩ := hcells
    let e : ℕ ↪ {n : ℕ | (samples n).HasCellSolution C} :=
      hCinf.natEmbedding _
    let k : ℕ → ℕ := fun n ↦ (e n).1
    have hkGood (n : ℕ) : (samples (k n)).HasCellSolution C :=
      (e n).2
    have hkInj : Function.Injective k := by
      intro m n hmn
      apply e.injective
      exact Subtype.ext hmn
    have hkTop : Tendsto k atTop atTop := hkInj.nat_tendsto_atTop
    have hcellExists (n : ℕ) :
        ∃ τ : Finset (samples (k n)).X,
          (samples (k n)).CellSolution C τ := hkGood n
    let τ (n : ℕ) : Finset (samples (k n)).X :=
      (hcellExists n).choose
    have hcellSolution (n : ℕ) :
        (samples (k n)).CellSolution C (τ n) :=
      (hcellExists n).choose_spec
    let hτ (n : ℕ) : (τ n).Nonempty :=
      (samples (k n)).cellNonempty (hcellSolution n)
    let ySeq (n : ℕ) : I → ℝ :=
      (samples (k n)).cellCoefficients (hcellSolution n)
    have hySeq (n : ℕ) (i : I) :
        0 ≤ ySeq n i ∧ ySeq n i ≤ 1 := by
      exact ⟨(samples (k n)).cellCoefficients_nonneg
          (hcellSolution n) i,
        (samples (k n)).cellCoefficients_le_one
          (hcellSolution n) i⟩
    have heqSeq (n : ℕ) :
        ∑ i, ySeq n i •
          (if hi : i ∈ C then
            vectorColor (samples (k n)).p (samples (k n)).f
              (@Finset.min' (samples (k n)).X
                ((samples (k n)).orders i) (τ n) (hτ n))
          else Pi.single i 1) = barycenter := by
      exact (samples (k n)).cellCoefficients_equation (hcellSolution n)
    let base (n : ℕ) : (samples (k n)).X := (hτ n).choose
    have hbaseMem (n : ℕ) : base n ∈ τ n := (hτ n).choose_spec
    let minimum (n : ℕ) (i : I) : (samples (k n)).X :=
      @Finset.min' (samples (k n)).X ((samples (k n)).orders i)
        (τ n) (hτ n)
    have hminimumMem (n : ℕ) (i : I) : minimum n i ∈ τ n :=
      @Finset.min'_mem (samples (k n)).X
        ((samples (k n)).orders i) (τ n) (hτ n)
    let zSeq (n : ℕ) : I → ℝ := (samples (k n)).p (base n)
    let vSeq (n : ℕ) (i : I) : I → ℝ :=
      (samples (k n)).f (minimum n i)
    let state (n : ℕ) :
        (I → ℝ) × ((I → I → ℝ) × (I → ℝ)) :=
      (zSeq n, (vSeq n, ySeq n))
    let simplex : Set (I → ℝ) := ScarfBrouwer.standardSimplex
    let valueCube : Set (I → I → ℝ) :=
      Set.univ.pi (fun _ ↦ simplex)
    let coefficientCube : Set (I → ℝ) :=
      Set.univ.pi (fun _ ↦ Set.Icc (0 : ℝ) 1)
    let compactState : Set
        ((I → ℝ) × ((I → I → ℝ) × (I → ℝ))) :=
      simplex ×ˢ (valueCube ×ˢ coefficientCube)
    have hsimplexCompact : IsCompact simplex := by
      change IsCompact (stdSimplex ℝ I)
      exact isCompact_stdSimplex ℝ I
    have hvalueCubeCompact : IsCompact valueCube := by
      exact isCompact_univ_pi (fun _ ↦ hsimplexCompact)
    have hcoefficientCubeCompact : IsCompact coefficientCube := by
      exact isCompact_univ_pi (fun _ ↦ isCompact_Icc)
    have hcompactState : IsCompact compactState :=
      hsimplexCompact.prod
        (hvalueCubeCompact.prod hcoefficientCubeCompact)
    have hstateMem (n : ℕ) : state n ∈ compactState := by
      refine ⟨(samples (k n)).p_mem (base n), ?_, ?_⟩
      · rw [Set.mem_pi]
        intro i _
        exact (samples (k n)).f_mem (minimum n i)
      · rw [Set.mem_pi]
        intro i _
        exact hySeq n i
    obtain ⟨limitState, hlimitState, φ, hφmono, hstateLim⟩ :=
      hcompactState.tendsto_subseq hstateMem
    rcases limitState with ⟨z, v, y⟩
    have hz : z ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)) :=
      hlimitState.1
    have hvSimplex (i : I) :
        v i ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)) := by
      exact hlimitState.2.1 i (Set.mem_univ i)
    have hy (i : I) : 0 ≤ y i :=
      (hlimitState.2.2 i (Set.mem_univ i)).1
    have hzLim : Tendsto (fun n ↦ zSeq (φ n)) atTop (𝓝 z) := by
      simpa [state, Function.comp_def] using
        (continuous_fst.continuousAt.tendsto.comp hstateLim)
    have hvLim (i : I) :
        Tendsto (fun n ↦ vSeq (φ n) i) atTop (𝓝 (v i)) := by
      have hc : Continuous
          (fun s : (I → ℝ) × ((I → I → ℝ) × (I → ℝ)) ↦ s.2.1 i) :=
        (continuous_apply i).comp (continuous_fst.comp continuous_snd)
      simpa [state, Function.comp_def] using
        (hc.continuousAt.tendsto.comp hstateLim)
    have hyLim (i : I) :
        Tendsto (fun n ↦ ySeq (φ n) i) atTop (𝓝 (y i)) := by
      have hc : Continuous
          (fun s : (I → ℝ) × ((I → I → ℝ) × (I → ℝ)) ↦ s.2.2 i) :=
        (continuous_apply i).comp (continuous_snd.comp continuous_snd)
      simpa [state, Function.comp_def] using
        (hc.continuousAt.tendsto.comp hstateLim)
    have hkφTop : Tendsto (fun n ↦ k (φ n)) atTop atTop :=
      hkTop.comp hφmono.tendsto_atTop
    have hscaleLim :
        Tendsto (fun n ↦ approximationScale (k (φ n)))
          atTop (𝓝 0) :=
      approximationScale_tendsto_zero.comp hkφTop
    have hsampleScale (n : ℕ) :
        (Fintype.card I : ℝ) * (samples (k n)).radius <
          approximationScale (k n) := by
      simpa [samples, approximationSample] using
        (approximationRadius_scale (I := I) (k n))
    have hC : C.Nonempty :=
      (samples (k 0)).cellIndex_nonempty (hcellSolution 0)
    have hbaseEnvelope (n : ℕ) :
        zSeq n ∈ (samples (k n)).cellEnvelope C (τ n) (hτ n) := by
      exact (samples (k n)).point_mem_cellEnvelope
        (hτ n) (hbaseMem n)
    have hminimumEnvelope (n : ℕ) (i : I) :
        (samples (k n)).p (minimum n i) ∈
          (samples (k n)).cellEnvelope C (τ n) (hτ n) := by
      exact (samples (k n)).point_mem_cellEnvelope
        (hτ n) (hminimumMem n i)
    have hdiameter (n : ℕ) :
        ∀ x ∈ (samples (k n)).cellEnvelope C (τ n) (hτ n),
          ∀ x' ∈ (samples (k n)).cellEnvelope C (τ n) (hτ n),
            ∀ i, |x i - x' i| < approximationScale (k n) := by
      simpa [hτ] using
        (samples (k n)).cellEnvelope_coordDiameter
          (hcellSolution n) (approximationScale (k n)) (hsampleScale n)
    have hminimumDist (n : ℕ) (i : I) :
        dist (zSeq n) ((samples (k n)).p (minimum n i)) <
          approximationScale (k n) := by
      rw [dist_pi_lt_iff (approximationScale_pos (k n))]
      intro j
      simpa [Real.dist_eq] using
        hdiameter n (zSeq n) (hbaseEnvelope n)
          ((samples (k n)).p (minimum n i))
          (hminimumEnvelope n i) j
    have hminimumLim (i : I) :
        Tendsto (fun n ↦ (samples (k (φ n))).p (minimum (φ n) i))
          atTop (𝓝 z) := by
      apply hzLim.congr_dist
      apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
        (Eventually.of_forall fun n ↦ (hminimumDist (φ n) i).le)
        hscaleLim
    have hvValue (i : I) : v i ∈ K.value z := by
      have hpairLim : Tendsto
          (fun n ↦ ((samples (k (φ n))).p (minimum (φ n) i),
            vSeq (φ n) i)) atTop (𝓝 (z, v i)) := by
        rw [nhds_prod_eq]
        exact (hminimumLim i).prodMk (hvLim i)
      have hpairMem : (z, v i) ∈
          {p : (I → ℝ) × (I → ℝ) | p.2 ∈ K.value p.1} := by
        apply K.isClosed_graph.mem_of_tendsto hpairLim
        apply Eventually.of_forall
        intro n
        change vSeq (φ n) i ∈
          K.value ((samples (k (φ n))).p (minimum (φ n) i))
        simpa [samples, approximationSample, vSeq, minimum] using
          selectedValue_mem_value K (k (φ n)) (minimum (φ n) i)
      exact hpairMem
    have hzOutside : ∀ i ∉ C, z i = 0 := by
      intro i hiC
      have hcoordSmall (n : ℕ) :
          |zSeq n i| < approximationScale (k n) := by
        obtain ⟨q, hqEnvelope, hqi⟩ :=
          (samples (k n)).exists_cellEnvelope_coord_eq_zero
            (hcellSolution n) hiC
        have hclose := hdiameter n (zSeq n) (hbaseEnvelope n)
          q hqEnvelope i
        simpa [hqi] using hclose
      have hdistZero :
          Tendsto (fun n ↦ dist (zSeq (φ n) i) 0) atTop (𝓝 0) := by
        apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
          (Eventually.of_forall fun n ↦ ?_) hscaleLim
        simpa [Real.dist_eq] using (hcoordSmall (φ n)).le
      have hzeroLim : Tendsto (fun n ↦ zSeq (φ n) i) atTop (𝓝 0) :=
        tendsto_iff_dist_tendsto_zero.mpr hdistZero
      have hzCoordLim :
          Tendsto (fun n ↦ zSeq (φ n) i) atTop (𝓝 (z i)) :=
        (continuous_apply i).continuousAt.tendsto.comp hzLim
      exact (tendsto_nhds_unique hzeroLim hzCoordLim).symm
    let limitTerm (i : I) : I → ℝ :=
      y i • (if i ∈ C then v i - z + barycenter else Pi.single i 1)
    let seqTerm (n : ℕ) (i : I) : I → ℝ :=
      ySeq n i •
        (if i ∈ C then
          vSeq n i - (samples (k n)).p (minimum n i) + barycenter
        else Pi.single i 1)
    have hseqEquation (n : ℕ) : ∑ i, seqTerm n i = barycenter := by
      rw [← heqSeq n]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ C <;>
        simp [seqTerm, vSeq, minimum, vectorColor, hi]
    have htermLim (i : I) :
        Tendsto (fun n ↦ seqTerm (φ n) i) atTop (𝓝 (limitTerm i)) := by
      by_cases hiC : i ∈ C
      · have hvectorLim : Tendsto
            (fun n ↦ vSeq (φ n) i -
              (samples (k (φ n))).p (minimum (φ n) i) + barycenter)
            atTop (𝓝 (v i - z + barycenter)) :=
          ((hvLim i).sub (hminimumLim i)).add tendsto_const_nhds
        simpa [seqTerm, limitTerm, hiC] using
          (hyLim i).smul hvectorLim
      · simpa [seqTerm, limitTerm, hiC] using
          (hyLim i).smul_const (Pi.single i (1 : ℝ))
    have hsumLim :
        Tendsto (fun n ↦ ∑ i, seqTerm (φ n) i)
          atTop (𝓝 (∑ i, limitTerm i)) := by
      simpa using tendsto_finsetSum (Finset.univ : Finset I)
        (fun i _ ↦ htermLim i)
    have hsumConst :
        Tendsto (fun n ↦ ∑ i, seqTerm (φ n) i)
          atTop (𝓝 (barycenter (I := I))) := by
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall fun n ↦ (hseqEquation (φ n)).symm
    have hlimitEquation :
        ∑ i, y i •
            (if i ∈ C then v i - z + barycenter else Pi.single i 1) =
          barycenter := by
      change ∑ i, limitTerm i = barycenter
      exact tendsto_nhds_unique hsumLim hsumConst
    refine ⟨z, hz, ?_⟩
    exact mem_of_limit_equation C hC z hz (K.value z)
      (K.convex_value z) v (fun i _ ↦ hvSimplex i)
      (fun i _ ↦ hvValue i) y hy hzOutside hlimitEquation

/-- Order-free public form: every nonempty finite index type can be given
the auxiliary linear order required by the Scarf construction. -/
theorem kakutani_fixedPoint [Fintype I] [Nonempty I]
    (K : Correspondence I) :
    ∃ z ∈ (ScarfBrouwer.standardSimplex : Set (I → ℝ)),
      z ∈ K.value z := by
  let : LinearOrder I :=
    LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  exact scarf_kakutani_fixedPoint K

end KakutaniScarf

end BeyondSperner
