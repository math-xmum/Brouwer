import BeyondSperner.Coloring.Matroid.General
import BeyondSperner.OrientedMatroid.Realizable
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Vector colorings

This file formalizes the genuinely linear-algebraic layer of Section 7 of
Ivanov's *Beyond Sperner's Lemma*.  It deliberately does not postulate an
oriented matroid associated with a vector configuration.  The first result
is the content of Lemma 7.1 itself: boundedness of the nonnegative solution
set rules out every nontrivial nonnegative linear dependence.
-/

namespace BeyondSperner

open Classical
open Set
open scoped BigOperators

namespace VectorColoring

/-- The finite vector framework at the start of Section 7.  Labels in `M`
are required to represent distinct vectors, the indexed elements are the
standard basis, and the distinguished nonzero vector has the displayed
nonnegative standard-basis coordinates from equation (29). -/
structure Framework (I M : Type*) [Fintype I] [Fintype M] where
  vector : M → I → ℝ
  vector_injective : Function.Injective vector
  basis : I ↪ M
  distinguished : M
  distinguished_notMem_basis : distinguished ∉ Set.range basis
  distinguished_ne_zero : vector distinguished ≠ 0
  basis_vector : ∀ i, vector (basis i) = Pi.single i 1
  distinguishedCoordinates : I → ℝ
  distinguishedCoordinates_nonneg : ∀ i, 0 ≤ distinguishedCoordinates i
  distinguished_eq_sum :
    vector distinguished =
      ∑ i, distinguishedCoordinates i • vector (basis i)

namespace Framework

variable {I M : Type*} [Fintype I] [Fintype M]
  (F : Framework I M)

/-- The linear combination represented by a coefficient vector on the
finite configuration. -/
def combination (a : M → ℝ) : I → ℝ :=
  ∑ m, a m • F.vector m

@[simp]
theorem combination_zero : F.combination 0 = 0 := by
  simp [combination]

theorem combination_add (a z : M → ℝ) :
    F.combination (a + z) = F.combination a + F.combination z := by
  simp only [combination, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem combination_smul (c : ℝ) (a : M → ℝ) :
    F.combination (c • a) = c • F.combination a := by
  simp only [combination, Pi.smul_apply, smul_eq_mul, mul_smul,
    Finset.smul_sum]

/-- A solution of equation (30), represented on all labels with the
distinguished coefficient forced to zero. -/
def IsNonnegativeSolution (a : M → ℝ) : Prop :=
  a F.distinguished = 0 ∧
    (∀ m, 0 ≤ a m) ∧
      F.combination a = F.vector F.distinguished

/-- The set whose boundedness is assumed in Section 7. -/
def nonnegativeSolutions : Set (M → ℝ) :=
  {a | F.IsNonnegativeSolution a}

/-- If every vector of the configuration lies in the affine hyperplane
`∑ i, x i = 1`, then the coefficients of every nonnegative solution of
equation (30) sum to one.  This is the coordinate-sum calculation used in
Lemma 9.1. -/
theorem sum_coefficients_eq_one_of_sum_vector_eq_one
    (hunit : ∀ m, ∑ i, F.vector m i = 1)
    {a : M → ℝ} (ha : F.IsNonnegativeSolution a) :
    ∑ m, a m = 1 := by
  calc
    ∑ m, a m = ∑ m, ∑ i, a m * F.vector m i := by
      simp_rw [← Finset.mul_sum, hunit, mul_one]
    _ = ∑ i, ∑ m, a m * F.vector m i := Finset.sum_comm
    _ = ∑ i, F.combination a i := by
      simp [combination]
    _ = ∑ i, F.vector F.distinguished i := by
      rw [ha.2.2]
    _ = 1 := hunit F.distinguished

/-- Pointwise form of Lemma 9.1: every coefficient of a nonnegative
solution is at most one. -/
theorem coefficient_le_one_of_sum_vector_eq_one
    (hunit : ∀ m, ∑ i, F.vector m i = 1)
    {a : M → ℝ} (ha : F.IsNonnegativeSolution a) (m : M) :
    a m ≤ 1 := by
  rw [← F.sum_coefficients_eq_one_of_sum_vector_eq_one hunit ha]
  exact Finset.single_le_sum (fun j _ ↦ ha.2.1 j) (Finset.mem_univ m)

/-- Boundedness conclusion of Lemma 9.1.  It is proved as containment in
the finite product of intervals `[0,1]`, rather than postulated as part of
the vector framework. -/
theorem isBounded_nonnegativeSolutions_of_sum_vector_eq_one
    (hunit : ∀ m, ∑ i, F.vector m i = 1) :
    Bornology.IsBounded F.nonnegativeSolutions := by
  apply (Bornology.IsBounded.pi fun _ ↦ Metric.isBounded_Icc (0 : ℝ) 1).subset
  intro a ha
  rw [Set.mem_pi]
  intro m _
  exact ⟨ha.2.1 m,
    F.coefficient_le_one_of_sum_vector_eq_one hunit ha m⟩

/-- Acyclicity stated directly for a real vector configuration: zero is
not a nontrivial nonnegative linear combination of its vectors.  This is
the realizable meaning of oriented-matroid acyclicity used in Lemma 7.1. -/
def IsAcyclic : Prop :=
  ∀ z : M → ℝ, (∀ m, 0 ≤ z m) → F.combination z = 0 → z = 0

/-- The canonical solution of (30) supplied by equation (29). -/
noncomputable def canonicalSolution : M → ℝ :=
  fun m ↦ ∑ i, if F.basis i = m then F.distinguishedCoordinates i else 0

@[simp]
theorem canonicalSolution_apply_distinguished :
    F.canonicalSolution F.distinguished = 0 := by
  simp only [canonicalSolution]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  intro h
  exact F.distinguished_notMem_basis ⟨i, h⟩

theorem canonicalSolution_nonneg (m : M) :
    0 ≤ F.canonicalSolution m := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact F.distinguishedCoordinates_nonneg i
  · exact le_rfl

theorem combination_canonicalSolution :
    F.combination F.canonicalSolution = F.vector F.distinguished := by
  rw [F.distinguished_eq_sum]
  simp only [combination, canonicalSolution, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem canonicalSolution_isNonnegativeSolution :
    F.IsNonnegativeSolution F.canonicalSolution :=
  ⟨F.canonicalSolution_apply_distinguished,
    F.canonicalSolution_nonneg,
    F.combination_canonicalSolution⟩

/-- The distinguished coordinates really are the coordinates of the
distinguished vector in the standard basis. -/
theorem distinguishedCoordinates_eq_apply (i : I) :
    F.distinguishedCoordinates i = F.vector F.distinguished i := by
  have hi := congrFun F.distinguished_eq_sum i
  simp only [F.basis_vector, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, Pi.single_apply] at hi
  simpa using hi.symm

/-- Because the distinguished vector is nonzero and its coordinates are
nonnegative, at least one displayed coefficient is strictly positive. -/
theorem exists_distinguishedCoordinate_pos :
    ∃ i, 0 < F.distinguishedCoordinates i := by
  have hne : ∃ i, F.vector F.distinguished i ≠ 0 := by
    simpa [Function.ne_iff] using F.distinguished_ne_zero
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, lt_of_le_of_ne
    (F.distinguishedCoordinates_nonneg i) ?_⟩
  intro hzero
  apply hi
  rw [← F.distinguishedCoordinates_eq_apply i, hzero]

/-- Eliminate the distinguished coefficient from a nonnegative dependence
using the canonical nonnegative representation (29). -/
noncomputable def eliminatedDirection (z : M → ℝ) : M → ℝ :=
  z + z F.distinguished • F.canonicalSolution -
    Pi.single F.distinguished (z F.distinguished)

@[simp]
theorem eliminatedDirection_apply_distinguished (z : M → ℝ) :
    F.eliminatedDirection z F.distinguished = 0 := by
  simp [eliminatedDirection]

theorem eliminatedDirection_apply_of_ne (z : M → ℝ) {m : M}
    (hm : m ≠ F.distinguished) :
    F.eliminatedDirection z m =
      z m + z F.distinguished * F.canonicalSolution m := by
  simp [eliminatedDirection, hm]

theorem eliminatedDirection_nonneg {z : M → ℝ}
    (hz : ∀ m, 0 ≤ z m) (m : M) :
    0 ≤ F.eliminatedDirection z m := by
  by_cases hm : m = F.distinguished
  · subst m
    simp
  · rw [F.eliminatedDirection_apply_of_ne z hm]
    exact add_nonneg (hz m)
      (mul_nonneg (hz F.distinguished)
        (F.canonicalSolution_nonneg m))

theorem combination_single_distinguished (c : ℝ) :
    F.combination (Pi.single F.distinguished c) =
      c • F.vector F.distinguished := by
  simp [combination]

theorem combination_eliminatedDirection {z : M → ℝ}
    (hz : F.combination z = 0) :
    F.combination (F.eliminatedDirection z) = 0 := by
  change F.combination
    (z + z F.distinguished • F.canonicalSolution -
      Pi.single F.distinguished (z F.distinguished)) = 0
  have hsub : z + z F.distinguished • F.canonicalSolution -
      Pi.single F.distinguished (z F.distinguished) =
      (z + z F.distinguished • F.canonicalSolution) +
        (-Pi.single F.distinguished (z F.distinguished)) := by
    rfl
  rw [hsub, F.combination_add]
  rw [F.combination_add, F.combination_smul,
    F.combination_canonicalSolution]
  have hneg : F.combination
      (-Pi.single F.distinguished (z F.distinguished)) =
        -(z F.distinguished • F.vector F.distinguished) := by
    rw [show -Pi.single F.distinguished (z F.distinguished) =
      (-1 : ℝ) • Pi.single F.distinguished (z F.distinguished) by
        ext m
        simp]
    rw [F.combination_smul,
      F.combination_single_distinguished]
    simp
  rw [hneg, hz]
  abel

/-- A nontrivial nonnegative dependence remains nontrivial after
eliminating the distinguished coefficient. -/
theorem eliminatedDirection_ne_zero {z : M → ℝ}
    (hzNonneg : ∀ m, 0 ≤ z m) (hzNe : z ≠ 0) :
    F.eliminatedDirection z ≠ 0 := by
  intro hzero
  obtain ⟨i, hiPos⟩ := F.exists_distinguishedCoordinate_pos
  have hbi : F.basis i ≠ F.distinguished := by
    intro h
    exact F.distinguished_notMem_basis ⟨i, h⟩
  have hcanonical :
      F.canonicalSolution (F.basis i) =
        F.distinguishedCoordinates i := by
    simp [canonicalSolution, F.basis.injective.eq_iff]
  have hAtBasis := congrFun hzero (F.basis i)
  rw [F.eliminatedDirection_apply_of_ne z hbi,
    hcanonical] at hAtBasis
  change z (F.basis i) + z F.distinguished *
    F.distinguishedCoordinates i = 0 at hAtBasis
  have hzDist : z F.distinguished = 0 := by
    have hprod : z F.distinguished *
        F.distinguishedCoordinates i = 0 := by
      nlinarith [hzNonneg (F.basis i),
        hzNonneg F.distinguished]
    exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hiPos)
  apply hzNe
  funext m
  by_cases hm : m = F.distinguished
  · simpa [hm] using hzDist
  · have hmEq := congrFun hzero m
    rw [F.eliminatedDirection_apply_of_ne z hm, hzDist,
      zero_mul, add_zero] at hmEq
    exact hmEq

/-- Adding a nonnegative multiple of an eliminated dependence to a
solution stays inside the nonnegative solution set. -/
theorem canonicalSolution_add_smul_eliminated_isSolution
    {z : M → ℝ} (hzNonneg : ∀ m, 0 ≤ z m)
    (hzComb : F.combination z = 0) {c : ℝ} (hc : 0 ≤ c) :
    F.IsNonnegativeSolution
      (F.canonicalSolution + c • F.eliminatedDirection z) := by
  constructor
  · simp
  constructor
  · intro m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (F.canonicalSolution_nonneg m)
      (mul_nonneg hc (F.eliminatedDirection_nonneg hzNonneg m))
  · rw [F.combination_add, F.combination_smul,
      F.combination_canonicalSolution,
      F.combination_eliminatedDirection hzComb]
    simp

/-- Lemma 7.1, in its exact realizable linear-algebraic form.  If the set
of nonnegative solutions of (30) is bounded, the vector configuration is
acyclic.  The proof constructs the unbounded ray described in the paper. -/
theorem isAcyclic_of_isBounded_nonnegativeSolutions
    (hbounded : Bornology.IsBounded F.nonnegativeSolutions) :
    F.IsAcyclic := by
  intro z hzNonneg hzComb
  by_contra hzNe
  have hdNe : F.eliminatedDirection z ≠ 0 :=
    F.eliminatedDirection_ne_zero hzNonneg hzNe
  obtain ⟨m, hmNe⟩ : ∃ m, F.eliminatedDirection z m ≠ 0 := by
    simpa [Function.ne_iff] using hdNe
  have hdPos : 0 < F.eliminatedDirection z m :=
    lt_of_le_of_ne (F.eliminatedDirection_nonneg hzNonneg m)
      (Ne.symm hmNe)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  have hcanonicalMem : F.canonicalSolution ∈ F.nonnegativeSolutions :=
    F.canonicalSolution_isNonnegativeSolution
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg F.canonicalSolution).trans (hC _ hcanonicalMem)
  let c : ℝ := (C + 1) / F.eliminatedDirection z m
  have hc : 0 ≤ c := div_nonneg (by linarith) hdPos.le
  let y : M → ℝ :=
    F.canonicalSolution + c • F.eliminatedDirection z
  have hyMem : y ∈ F.nonnegativeSolutions :=
    F.canonicalSolution_add_smul_eliminated_isSolution
      hzNonneg hzComb hc
  have hyBound : ‖y‖ ≤ C := hC y hyMem
  have hymNonneg : 0 ≤ y m := hyMem.2.1 m
  have hymEq : y m = F.canonicalSolution m + (C + 1) := by
    dsimp [y, c]
    rw [div_mul_cancel₀ _ (ne_of_gt hdPos)]
  have hymGt : C < y m := by
    rw [hymEq]
    linarith [F.canonicalSolution_nonneg m]
  have hnormCoord : y m ≤ ‖y‖ := by
    calc
      y m = |y m| := (abs_of_nonneg hymNonneg).symm
      _ = ‖y m‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖y‖ := norm_le_pi_norm y m
  linarith

/-- The realizable oriented-matroid framework attached to the vector data.

Every field is discharged by a proved compatibility theorem: the standard
basis is a matroid basis, Lemma 7.1 supplies acyclicity, and equation (29)
supplies oriented-convex-hull membership. -/
noncomputable def toMatroidFramework
    (hbounded : Bornology.IsBounded F.nonnegativeSolutions) :
    MatroidColoring.Framework I M where
  matroid := RealizableOrientedMatroid.data F.vector
  vertex := F.basis
  distinguished := F.distinguished
  basis_isBasis := by
    apply RealizableOrientedMatroid.isBasis_range_of_basis F.vector F.basis
      (Pi.basisFun ℝ I)
    intro i
    rw [F.basis_vector, Pi.basisFun_apply]
  distinguished_notMem_basis := F.distinguished_notMem_basis
  acyclic := by
    apply (RealizableOrientedMatroid.isAcyclic_iff_no_nonnegative_dependence
      F.vector).2
    intro a ha hcomb
    apply F.isAcyclic_of_isBounded_nonnegativeSolutions hbounded a ha
    simpa [RealizableOrientedMatroid.combination, combination] using hcomb
  distinguished_mem_convexHull := by
    apply (RealizableOrientedMatroid.memConvexHull_iff_exists_nonnegative_combination
      F.vector F.distinguished_notMem_basis).2
    refine ⟨F.canonicalSolution, F.canonicalSolution_nonneg, ?_, ?_⟩
    · intro m hm
      by_contra hmRange
      have hmZero : F.canonicalSolution m = 0 := by
        simp only [canonicalSolution]
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg]
        intro him
        exact hmRange ⟨i, him⟩
      exact (RealizableOrientedMatroid.mem_coefficientSupport.mp hm) hmZero
    · simpa [RealizableOrientedMatroid.combination, combination] using
        F.combination_canonicalSolution

section LinearConclusion

variable [DecidableEq I] [DecidableEq M]

/-- The actual finite set of vectors represented by a finite label set. -/
noncomputable def vectorImage (S : Finset M) : Finset (I → ℝ) :=
  S.image F.vector

/-- Injectivity of the configuration identifies a finite label set with
its literal vector image. -/
noncomputable def labelVectorEquiv (S : Finset M) :
    (S : Set M) ≃ (F.vectorImage S : Set (I → ℝ)) :=
  Equiv.ofBijective
    (fun m ↦ ⟨F.vector m, Finset.mem_image.mpr ⟨m, m.2, rfl⟩⟩)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      apply F.vector_injective
      exact congrArg Subtype.val hxy,
    by
      intro w
      obtain ⟨m, hmS, hmw⟩ := Finset.mem_image.mp w.2
      refine ⟨⟨m, hmS⟩, ?_⟩
      apply Subtype.ext
      exact hmw⟩

omit [DecidableEq I] in
/-- Translate a good basis of the realizable oriented matroid back into
the two literal linear-algebra conclusions used in Section 7.

The explicit hypothesis `b ∉ S` selects the nontrivial circuit branch of
the proved convex-hull compatibility theorem.  In both applications below
it is derived from the coloring codomain and is not an extra assumption on
the theorem statement. -/
theorem exists_linearBasis_and_nonnegativeCombination
    (hbounded : Bornology.IsBounded F.nonnegativeSolutions)
    (S : Finset M) (hbNotS : F.distinguished ∉ S)
    (hgood : (F.toMatroidFramework hbounded).matroid.IsGoodBasis
      F.distinguished (S : Set M)) :
    ∃ B : Module.Basis (S : Set M) ℝ (I → ℝ),
      (∀ m, B m = F.vector m) ∧
        ∃ a : M → ℝ,
          (∀ m, 0 ≤ a m) ∧
            RealizableOrientedMatroid.coefficientSupport a ⊆ (S : Set M) ∧
            F.combination a = F.vector F.distinguished := by
  let MF : MatroidColoring.Framework I M := F.toMatroidFramework hbounded
  have hLinearIndependent :
      LinearIndependent ℝ (fun m : (S : Set M) ↦ F.vector m) :=
    (RealizableOrientedMatroid.isIndependent_iff_linearIndependent
      F.vector (S : Set M)).mp hgood.1.1
  have hScard : S.card = Fintype.card I := by
    exact MF.card_eq_card_index_of_isBasis S hgood.1
  have hSNonempty : Nonempty (S : Set M) := by
    have hSpos : 0 < S.card := by
      rw [hScard]
      exact Fintype.card_pos_iff.mpr MF.index_nonempty
    obtain ⟨m, hm⟩ := Finset.card_pos.mp hSpos
    exact ⟨⟨m, hm⟩⟩
  let : Nonempty (S : Set M) := hSNonempty
  have hDimension :
      Fintype.card (S : Set M) = Module.finrank ℝ (I → ℝ) := by
    simp [hScard]
  let B : Module.Basis (S : Set M) ℝ (I → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hLinearIndependent hDimension
  have hBapply : ∀ m, B m = F.vector m := by
    intro m
    exact congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank
        hLinearIndependent hDimension) m
  obtain ⟨a, haNonneg, haSupport, haCombination⟩ :=
    (RealizableOrientedMatroid.memConvexHull_iff_exists_nonnegative_combination
      F.vector hbNotS).mp hgood.2
  refine ⟨B, hBapply, a, haNonneg, haSupport, ?_⟩
  simpa [RealizableOrientedMatroid.combination, combination] using haCombination

omit [DecidableEq I] in
/-- Literal set-valued version of the preceding bridge: the index type of
`B` is now the actual finite vector image, and `B w = w` for every vector
in that image. -/
theorem exists_vectorImageBasis_and_nonnegativeCombination
    (hbounded : Bornology.IsBounded F.nonnegativeSolutions)
    (S : Finset M) (hbNotS : F.distinguished ∉ S)
    (hgood : (F.toMatroidFramework hbounded).matroid.IsGoodBasis
      F.distinguished (S : Set M)) :
    ∃ B : Module.Basis (F.vectorImage S : Set (I → ℝ)) ℝ (I → ℝ),
      (∀ w, B w = w.1) ∧
        ∃ a : M → ℝ,
          (∀ m, 0 ≤ a m) ∧
            RealizableOrientedMatroid.coefficientSupport a ⊆ (S : Set M) ∧
            F.combination a = F.vector F.distinguished := by
  obtain ⟨B, hB, a, haNonneg, haSupport, haCombination⟩ :=
    F.exists_linearBasis_and_nonnegativeCombination hbounded S hbNotS hgood
  let e := F.labelVectorEquiv S
  refine ⟨B.reindex e, ?_, a, haNonneg, haSupport, haCombination⟩
  intro w
  rw [B.reindex_apply e, hB]
  have heq := congrArg Subtype.val (e.apply_symm_apply w)
  change F.vector ((e.symm w).1) = w.1 at heq
  exact heq

omit [DecidableEq I] in
/-- Fully literal version of the Section 7 conclusion: both the basis and
the coefficient function are indexed by the actual finite vector image,
with no label-level representation left in the statement. -/
theorem exists_literalVectorBasis_and_nonnegativeCombination
    (hbounded : Bornology.IsBounded F.nonnegativeSolutions)
    (S : Finset M) (hbNotS : F.distinguished ∉ S)
    (hgood : (F.toMatroidFramework hbounded).matroid.IsGoodBasis
      F.distinguished (S : Set M)) :
    ∃ B : Module.Basis (F.vectorImage S : Set (I → ℝ)) ℝ (I → ℝ),
      (∀ w, B w = w.1) ∧
        ∃ q : {w : I → ℝ // w ∈ F.vectorImage S} → ℝ,
          (∀ w, 0 ≤ q w) ∧
            ∑ w, q w • w.1 = F.vector F.distinguished := by
  obtain ⟨B, hB, a, haNonneg, haSupport, haCombination⟩ :=
    F.exists_vectorImageBasis_and_nonnegativeCombination
      hbounded S hbNotS hgood
  let e := F.labelVectorEquiv S
  let q : {w : I → ℝ // w ∈ F.vectorImage S} → ℝ :=
    fun w ↦ a ((e.symm w).1)
  have hqNonneg : ∀ w, 0 ≤ q w := by
    intro w
    exact haNonneg _
  have hsumLabels :
      F.combination a = ∑ m : (S : Set M), a m • F.vector m := by
    calc
      F.combination a = ∑ m ∈ S, a m • F.vector m := by
        rw [combination]
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro m _ hmS
        have ham : a m = 0 := by
          by_contra ham
          exact hmS (haSupport
            (RealizableOrientedMatroid.mem_coefficientSupport.mpr ham))
        simp [ham]
      _ = ∑ m : (S : Set M), a m • F.vector m := by
        exact (Finset.sum_attach S (fun m ↦ a m • F.vector m)).symm
  have hsumEquiv :
      (∑ m : (S : Set M), a m • F.vector m) =
        ∑ w : (F.vectorImage S : Set (I → ℝ)), q w • w.1 := by
    apply Fintype.sum_equiv e
    intro m
    have heval : (e m).1 = F.vector m.1 := rfl
    simp only [q, e.symm_apply_apply, heval]
  refine ⟨B, hB, q, hqNonneg, ?_⟩
  calc
    (∑ w, q w • w.1) = ∑ m : (S : Set M), a m • F.vector m := hsumEquiv.symm
    _ = F.combination a := hsumLabels.symm
    _ = F.vector F.distinguished := haCombination

end LinearConclusion

section MainTheorem

variable {V : Type*} [Fintype V] [DecidableEq I] [DecidableEq V]
  [DecidableEq M]

/-- A coloring of the vertices of a chain-simplex family by labels other
than the distinguished label. -/
abbrev Coloring (D : SimplexFamily I V) :=
  D.Vertex → {m : M // m ≠ F.distinguished}

/-- Image of a simplex under a vector coloring, defined without passing
through an oriented-matroid framework. -/
def colorImage (D : SimplexFamily I V) (c : Coloring F D)
    {C : Finset I} (τ : Finset V) (hτ : τ ∈ D.complex C) : Finset M :=
  τ.attach.image fun v ↦
    (c ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D hτ v.2⟩).1

/-- Formula (31), expressed natively in the vector framework. -/
def completedImage (D : SimplexFamily I V) (c : Coloring F D)
    (C : Finset I) (τ : Finset V) (hτ : τ ∈ D.complex C) : Finset M :=
  F.colorImage D c τ hτ ∪ (Finset.univ \ C).image F.basis

omit [Fintype V] in
/-- The vector-native completed image agrees exactly with the one used by
the oriented-matroid coloring theorem. -/
theorem completedImage_toMatroidFramework
    (hbounded : Bornology.IsBounded F.nonnegativeSolutions)
    (D : SimplexFamily I V) (c : Coloring F D)
    (C : Finset I) (τ : Finset V) (hτ : τ ∈ D.complex C) :
    F.completedImage D c C τ hτ =
      MatroidColoring.completedImage D
        (F.toMatroidFramework hbounded) c C τ hτ :=
  rfl

/-- The exact vector conclusion attached to `(C, τ)` in Theorem 7.2.

The completed colored set is not merely declared to be a matroid basis:
`B` is indexed by the literal set of vectors in formula (31), and every
basis vector is explicitly identified with the vector indexing it.
The final conjunct is the nonnegative representation of the distinguished
vector supported on that same completed colored set. -/
def IsSolution (D : SimplexFamily I V) (c : Coloring F D)
    (C : Finset I) (τ : Finset V) : Prop :=
  ∃ hτ : τ ∈ D.complex C,
    C.Nonempty ∧ τ.card = C.card ∧
      ∃ B : Module.Basis
          (F.vectorImage (F.completedImage D c C τ hτ) : Set (I → ℝ))
          ℝ (I → ℝ),
        (∀ w, B w = w.1) ∧
          ∃ q : {w : I → ℝ //
              w ∈ F.vectorImage (F.completedImage D c C τ hτ)} → ℝ,
            (∀ w, 0 ≤ q w) ∧
              ∑ w, q w • w.1 = F.vector F.distinguished

/-- Theorem 7.2 in its vector form.  Its proof is a composition of the
general oriented-matroid coloring theorem with the realizability
compatibility theorems above; the last step reconstructs an actual linear
basis and an actual nonnegative coefficient vector. -/
theorem theorem7_2
    (hbounded : Bornology.IsBounded F.nonnegativeSolutions)
    (D : SimplexFamily I V) (hchain : D.IsChainSimplex)
    (c : Coloring F D) :
    ∃ C : Finset I, ∃ τ : Finset V, F.IsSolution D c C τ := by
  let MF : MatroidColoring.Framework I M := F.toMatroidFramework hbounded
  obtain ⟨C, τ, hτ, hC, hcard, hgood⟩ :=
    MatroidColoring.theorem8_5 D MF hchain c
  let S : Finset M := F.completedImage D c C τ hτ
  have hgoodS : MF.matroid.IsGoodBasis F.distinguished (S : Set M) := by
    simpa [MF, S, toMatroidFramework,
      F.completedImage_toMatroidFramework hbounded D c C τ hτ]
      using hgood
  have hbNotS : F.distinguished ∉ S := by
    intro hb
    change F.distinguished ∈ F.completedImage D c C τ hτ at hb
    rcases Finset.mem_union.mp hb with hbColor | hbBasis
    · obtain ⟨v, _, hvb⟩ := Finset.mem_image.mp hbColor
      exact (c ⟨v.1,
        MatroidColoring.mem_vertexSet_of_mem_simplex D hτ v.2⟩).2 hvb
    · obtain ⟨i, _, hib⟩ := Finset.mem_image.mp hbBasis
      exact F.distinguished_notMem_basis ⟨i, hib⟩
  obtain ⟨B, hBapply, q, hqNonneg, hqCombination⟩ :=
    F.exists_literalVectorBasis_and_nonnegativeCombination
      hbounded S hbNotS hgoodS
  exact ⟨C, τ, hτ, hC, hcard, B, hBapply,
    q, hqNonneg, hqCombination⟩

end MainTheorem

end Framework

end VectorColoring

end BeyondSperner
