import BeyondSperner.FixedPoint.ScarfBrouwer
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Brouwer's theorem on an arbitrary affine simplex

This file transports the Scarf--Brouwer theorem proved on the standard
coordinate simplex to the convex hull of an arbitrary finite affine basis.
The transport is explicit: barycentric coordinates and affine reconstruction
are proved to be mutually inverse continuous maps.

No pre-existing Brouwer fixed-point theorem is used here.
-/

namespace BeyondSperner
namespace ScarfBrouwer

open Classical Set

variable {I P : Type*} [Fintype I]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The closed affine simplex spanned by an affine basis. -/
def affineSimplex (b : AffineBasis I ℝ P) : Set P :=
  convexHull ℝ (Set.range b)

/-- The simultaneous barycentric-coordinate map of an affine basis. -/
noncomputable def affineCoordinateMap (b : AffineBasis I ℝ P) :
    P →ᵃ[ℝ] (I → ℝ) :=
  AffineMap.pi fun i ↦ b.coord i

omit [Fintype I] in
@[simp] theorem affineCoordinateMap_apply
    (b : AffineBasis I ℝ P) (q : P) (i : I) :
    affineCoordinateMap b q i = b.coord i q := rfl

/-- Reconstruct a point from a family of affine coordinates. -/
noncomputable def pointOfAffineCoordinates
    (b : AffineBasis I ℝ P) (w : I → ℝ) : P :=
  Finset.univ.affineCombination ℝ b w

/-- Coordinate reconstruction is a right inverse on the affine hyperplane
where the coefficients sum to one. -/
theorem affineCoordinateMap_pointOfAffineCoordinates
    (b : AffineBasis I ℝ P) (w : I → ℝ) (hw : ∑ i, w i = 1) :
    affineCoordinateMap b (pointOfAffineCoordinates b w) = w := by
  funext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw

/-- Reconstructing a point from its barycentric coordinates returns the
original point. -/
@[simp] theorem pointOfAffineCoordinates_affineCoordinateMap
    (b : AffineBasis I ℝ P) (q : P) :
    pointOfAffineCoordinates b (affineCoordinateMap b q) = q := by
  exact b.affineCombination_coord_eq_self q

/-- A point belongs to the affine simplex exactly when all its barycentric
coordinates are nonnegative (their sum is automatically one). -/
theorem affineCoordinateMap_mem_standardSimplex_iff
    (b : AffineBasis I ℝ P) (q : P) :
    affineCoordinateMap b q ∈ (standardSimplex : Set (I → ℝ)) ↔
      q ∈ affineSimplex b := by
  rw [affineSimplex, b.convexHull_eq_nonneg_coord]
  constructor
  · exact fun h i ↦ h.1 i
  · intro h
    exact ⟨h, b.sum_coord_apply_eq_one q⟩

/-- Nonnegative coordinates summing to one reconstruct a point in the
affine simplex. -/
theorem pointOfAffineCoordinates_mem_affineSimplex
    (b : AffineBasis I ℝ P) (w : I → ℝ)
    (hw : w ∈ (standardSimplex : Set (I → ℝ))) :
    pointOfAffineCoordinates b w ∈ affineSimplex b := by
  rw [← affineCoordinateMap_mem_standardSimplex_iff b]
  rw [affineCoordinateMap_pointOfAffineCoordinates b w hw.2]
  exact hw

/-- Barycentric coordinates give a homeomorphism from an arbitrary affine
simplex to the standard coordinate simplex. -/
noncomputable def affineSimplexHomeomorphStandard
    (b : AffineBasis I ℝ P) :
    (affineSimplex b) ≃ₜ (standardSimplex : Set (I → ℝ)) := by
  let _ : FiniteDimensional ℝ P := b.finiteDimensional
  let reconstruct : (I → ℝ) →ᵃ[ℝ] P :=
    Finset.univ.affineCombination ℝ b
  refine
    { toEquiv :=
        { toFun := fun q ↦
            ⟨affineCoordinateMap b q.1,
              (affineCoordinateMap_mem_standardSimplex_iff b q.1).2 q.2⟩
          invFun := fun w ↦
            ⟨pointOfAffineCoordinates b w.1,
              pointOfAffineCoordinates_mem_affineSimplex b w.1 w.2⟩
          left_inv := ?_
          right_inv := ?_ }
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro q
    apply Subtype.ext
    exact pointOfAffineCoordinates_affineCoordinateMap b q.1
  · intro w
    apply Subtype.ext
    exact affineCoordinateMap_pointOfAffineCoordinates b w.1 w.2.2
  · apply Continuous.subtype_mk
    exact (affineCoordinateMap b).continuous_of_finiteDimensional.comp
      continuous_subtype_val
  · apply Continuous.subtype_mk
    exact reconstruct.continuous_of_finiteDimensional.comp continuous_subtype_val

/-- Brouwer's fixed-point theorem on the convex hull of an arbitrary finite
real affine basis, obtained by conjugating with barycentric coordinates and
applying the formalized Scarf--Brouwer theorem on the standard simplex. -/
theorem scarf_brouwer_fixedPoint_affineSimplex
    (b : AffineBasis I ℝ P)
    (f : affineSimplex b → affineSimplex b)
    (hcont : Continuous f) : ∃ x, f x = x := by
  classical
  let _ : Nonempty I := Fintype.card_pos_iff.mp (by
    rw [b.card_eq_finrank_add_one]
    omega)
  let e := affineSimplexHomeomorphStandard b
  let g : standardSimplex (I := I) → standardSimplex (I := I) :=
    fun x ↦ e (f (e.symm x))
  have hg : Continuous g :=
    e.continuous.comp (hcont.comp e.symm.continuous)
  obtain ⟨y, hy⟩ := scarf_brouwer_fixedPoint_subtype g hg
  refine ⟨e.symm y, ?_⟩
  apply e.injective
  simpa [g] using hy

end ScarfBrouwer
end BeyondSperner
