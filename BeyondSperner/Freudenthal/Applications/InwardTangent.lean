import BeyondSperner.Coloring.InwardTangent
import BeyondSperner.Freudenthal.Boundary

/-!
# Theorem 10.10 on the concrete Freudenthal--Scarf triangulation

This file discharges the abstract face, ambient-inclusion, and purity
obligations of `AffineColoring.theorem10_10` for the positive-scale integer
simplex.  Integer vertices are realized in an arbitrary reference simplex by
their normalized coordinates.  Lemma 4.7 supplies the boundary-face
condition, the iterated coordinate-face theorem supplies inclusion in the
full complex, and Theorem 4.8 plus Freudenthal purity supplies extension to a
top simplex.
-/

namespace BeyondSperner

open Classical Set
open scoped BigOperators

namespace IntegerSimplex

variable {P : Type*} [AddCommGroup P] [Module ℝ P]

/-- The normalized barycentric weight of an integer-simplex point. -/
noncomputable def normalizedPointWeight {N n : ℕ}
    (a : Point N n) (i : Fin (n + 1)) : ℝ :=
  (pointCoords a i : ℝ) / (N : ℝ)

/-- At positive scale the normalized integer coordinates have total mass
one. -/
theorem sum_normalizedPointWeight {N n : ℕ} (hN : 0 < N)
    (a : Point N n) :
    ∑ i, normalizedPointWeight a i = 1 := by
  rw [show (∑ i, normalizedPointWeight a i) =
      (∑ i, (pointCoords a i : ℝ)) / (N : ℝ) by
    simp [normalizedPointWeight, Finset.sum_div]]
  have hsum : ∑ i, (pointCoords a i : ℝ) = (N : ℝ) := by
    exact_mod_cast (pointCoords_isPoint a).2
  rw [hsum, div_self]
  exact_mod_cast (ne_of_gt hN)

/-- Normalized integer coordinates are nonnegative. -/
theorem normalizedPointWeight_nonneg {N n : ℕ}
    (a : Point N n) (i : Fin (n + 1)) :
    0 ≤ normalizedPointWeight a i := by
  apply div_nonneg
  · exact_mod_cast (pointCoords_isPoint a).1 i
  · exact_mod_cast (Nat.zero_le N)

/-- Affine realization of a positive-scale integer point in the reference
simplex spanned by `b`. -/
noncomputable def affinePointPosition {N n : ℕ}
    (b : AffineBasis (Fin (n + 1)) ℝ P) (a : Point N n) : P :=
  Finset.univ.affineCombination ℝ b (normalizedPointWeight a)

/-- The affine realization is genuinely a point of the reference simplex,
not merely a point with a convenient coordinate formula. -/
theorem affinePointPosition_mem_referenceSimplex {N n : ℕ} (hN : 0 < N)
    (b : AffineBasis (Fin (n + 1)) ℝ P) (a : Point N n) :
    affinePointPosition b a ∈ convexHull ℝ (Set.range b) := by
  exact affineCombination_mem_convexHull
    (fun i _ ↦ normalizedPointWeight_nonneg a i)
    (sum_normalizedPointWeight hN a)

/-- The barycentric coordinates of the affine realization are literally the
normalized integer coordinates. -/
theorem coord_affinePointPosition {N n : ℕ} (hN : 0 < N)
    (b : AffineBasis (Fin (n + 1)) ℝ P) (a : Point N n)
    (i : Fin (n + 1)) :
    b.coord i (affinePointPosition b a) = normalizedPointWeight a i := by
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i)
    (sum_normalizedPointWeight hN a)

/-- The affine realization does not identify distinct integer vertices at
positive scale. -/
theorem affinePointPosition_injective {N n : ℕ} (hN : 0 < N)
    (b : AffineBasis (Fin (n + 1)) ℝ P) :
    Function.Injective (affinePointPosition (N := N) (n := n) b) := by
  intro a d had
  apply pointCoords_injective
  funext i
  have hcoord := congrArg (fun q : P ↦ b.coord i q) had
  rw [coord_affinePointPosition hN, coord_affinePointPosition hN] at hcoord
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hN)
  have hreal : (pointCoords a i : ℝ) = (pointCoords d i : ℝ) :=
    (div_left_inj' hNne).mp hcoord
  exact_mod_cast hreal

/-- Every vertex of a `C`-associated simplex is realized on every reference
face indexed outside `C`. -/
theorem coord_affinePointPosition_eq_zero_of_mem_associatedComplex
    {N n : ℕ} (hN : 0 < N)
    (b : AffineBasis (Fin (n + 1)) ℝ P)
    {C : Finset (Fin (n + 1))} {tau : Finset (Point N n)}
    (htau : tau ∈ (pointOrders N n).associatedComplex C)
    {a : Point N n} (ha : a ∈ tau)
    {i : Fin (n + 1)} (hiC : i ∉ C) :
    b.coord i (affinePointPosition b a) = 0 := by
  rw [coord_affinePointPosition hN]
  have hcoord :=
    coord_eq_zero_of_mem_associatedComplex_of_not_mem htau ha hiC
  simp [normalizedPointWeight, hcoord]

/-- Theorem 10.10 instantiated on the positive-scale Freudenthal--Scarf
triangulation.  Unlike the abstract theorem, no face-compatibility,
ambient-inclusion, or purity hypothesis remains: all three are derived from
the concrete cyclic orders and integer realization. -/
theorem freudenthal_theorem10_10
    {N n : ℕ} (hN : 0 < N)
    (b : AffineBasis (Fin (n + 1)) ℝ P)
    (hb : AffineColoring.IsCenteredAffineBasis b)
    (c : ((pointOrders N n).associatedFamily).Vertex → P)
    (hinward : AffineColoring.IsInwardTangentColoring
      ((pointOrders N n).associatedFamily) b
      (fun v ↦ affinePointPosition b v.1) c) :
    ∃ sigma : Finset (Point N n),
      ∃ hsigma : sigma ∈
          ((pointOrders N n).associatedFamily).complex Finset.univ,
        sigma.card = n + 1 ∧
          (0 : P) ∈ convexHull ℝ
            (AffineColoring.affineSimplexColorPoints
              ((pointOrders N n).associatedFamily) c Finset.univ sigma hsigma :
                Set P) := by
  let D := (pointOrders N n).associatedFamily
  let p : D.Vertex → P := fun v ↦ affinePointPosition b v.1
  have hface : ∀ (C : Finset (Fin (n + 1)))
      (tau : Finset (Point N n)) (htau : tau ∈ D.complex C)
      (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0 := by
    intro C tau htau v hv i hi
    have hiC : i ∉ C := (Finset.mem_sdiff.mp hi).2
    exact coord_affinePointPosition_eq_zero_of_mem_associatedComplex
      hN b htau hv hiC
  have hAmbient : ∀ (C : Finset (Fin (n + 1)))
      (tau : Finset (Point N n)), tau ∈ D.complex C →
        tau ∈ D.complex Finset.univ := by
    intro C tau htau
    exact associatedComplex_subset_full_of_pos hN C htau
  have hPure :
      (D.complex Finset.univ).IsPureOfCardinality
        (Fintype.card (Fin (n + 1))) := by
    change FiniteSimplicialComplex.IsPureOfCardinality
      ((pointOrders N n).associatedComplex Finset.univ)
      (Fintype.card (Fin (n + 1)))
    simpa using associatedComplex_isPureOfCardinality_of_pos
      (N := N) (n := n) hN
  obtain ⟨sigma, hsigma, hcard, hzero⟩ :=
    AffineColoring.theorem10_10 D b hb p c
      (pointOrders N n).associatedFamily_isChainSimplex
      hface hinward hAmbient hPure
  refine ⟨sigma, hsigma, ?_, hzero⟩
  simpa using hcard

end IntegerSimplex
end BeyondSperner
