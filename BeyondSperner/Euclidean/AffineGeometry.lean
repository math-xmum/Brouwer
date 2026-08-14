import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Real.Basic

/-!
# Affine geometry for Section 10

This file begins the geometric part of Section 10 of Ivanov's
*Beyond Sperner's Lemma*.  In particular, it records the finite-face form
of Carathéodory's theorem used in Lemma 10.3, with affine dimension measured
by the finrank of `vectorSpan`.
-/

namespace BeyondSperner
namespace AffineGeometry

open Set
open Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Carathéodory's theorem in the face language used in Section 10: a point
of the convex hull of a finite simplex lies in the convex hull of an
affinely independent face. -/
theorem exists_affineIndependent_face {sigma : Finset E} {x : E}
    (hx : x ∈ convexHull ℝ (sigma : Set E)) :
    ∃ tau : Finset E, tau ⊆ sigma ∧
      AffineIndependent ℝ ((↑) : tau → E) ∧
      x ∈ convexHull ℝ (tau : Set E) := by
  rw [convexHull_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨tau, htau, hind, hx⟩ := hx
  exact ⟨tau, by simpa using htau, hind, hx⟩

/-- The affinely independent, at-most-`m + 1` form of Carathéodory used to
prove Lemma 10.3. -/
theorem lemma10_3_atMost {sigma : Finset E} {x : E} {m : ℕ}
    (hdim : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) = m)
    (hx : x ∈ convexHull ℝ (sigma : Set E)) :
    ∃ tau : Finset E, tau ⊆ sigma ∧ tau.card ≤ m + 1 ∧
      AffineIndependent ℝ ((↑) : tau → E) ∧
      x ∈ convexHull ℝ (tau : Set E) := by
  rw [convexHull_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨tau, htau, hind, hx⟩ := hx
  have hsubset : (tau : Set E) ⊆ (sigma : Set E) := by simpa using htau
  let : FiniteDimensional ℝ (vectorSpan ℝ (sigma : Set E)) :=
    finiteDimensional_vectorSpan_of_finite ℝ (Finset.finite_toSet sigma)
  have hspan : vectorSpan ℝ (tau : Set E) ≤ vectorSpan ℝ (sigma : Set E) :=
    vectorSpan_mono ℝ hsubset
  have hrange : Set.range ((↑) : tau → E) = (tau : Set E) := by
    ext y
    simp
  have hcard : tau.card ≤ m + 1 := by
    calc
      tau.card = Fintype.card tau := by simp
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : tau → E))) + 1 :=
        hind.card_le_finrank_succ
      _ = Module.finrank ℝ (vectorSpan ℝ (tau : Set E)) + 1 := by
        rw [hrange]
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) + 1 := by
        exact Nat.add_le_add_right (Submodule.finrank_mono hspan) 1
      _ = m + 1 := by rw [hdim]
  exact ⟨tau, by simpa using htau, hcard, hind, hx⟩

/-- Lemma 10.3 in the paper's exact face-cardinality form.  If the affine
dimension of the convex hull of `sigma` is `m`, every point of that convex
hull lies in the convex hull of a subset of exactly `m + 1` vertices. -/
theorem lemma10_3 {sigma : Finset E} {x : E} {m : ℕ}
    (hdim : Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) = m)
    (hx : x ∈ convexHull ℝ (sigma : Set E)) :
    ∃ tau : Finset E, tau ⊆ sigma ∧ tau.card = m + 1 ∧
      x ∈ convexHull ℝ (tau : Set E) := by
  obtain ⟨tau, htau, htauCard, _htauIndependent, hxTau⟩ :=
    lemma10_3_atMost hdim hx
  have hsigmaNonempty : sigma.Nonempty := by
    by_contra hsigma
    have hsigmaEmpty : sigma = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsigma
    subst sigma
    simp at hx
  let : Nonempty sigma := hsigmaNonempty.to_subtype
  have hrange : Set.range ((↑) : sigma → E) = (sigma : Set E) := by
    ext y
    simp
  have hsigmaCard : m + 1 ≤ sigma.card := by
    calc
      m + 1 = Module.finrank ℝ (vectorSpan ℝ (sigma : Set E)) + 1 := by rw [hdim]
      _ = Module.finrank ℝ (vectorSpan ℝ
          (Set.range ((↑) : sigma → E))) + 1 := by rw [hrange]
      _ ≤ Fintype.card sigma := finrank_vectorSpan_range_add_one_le ℝ ((↑) : sigma → E)
      _ = sigma.card := by simp
  obtain ⟨rho, htauRho, hrhoSigma, hrhoCard⟩ :=
    Finset.exists_subsuperset_card_eq htau htauCard hsigmaCard
  refine ⟨rho, hrhoSigma, hrhoCard, ?_⟩
  exact convexHull_mono (by simpa using htauRho) hxTau

end AffineGeometry
end BeyondSperner
