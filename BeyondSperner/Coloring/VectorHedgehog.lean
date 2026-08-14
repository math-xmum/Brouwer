import BeyondSperner.Coloring.InwardTangent
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Vector hedgehog colorings

This file formalizes the cyclic relabeling argument in the interior case of
Theorem 10.9.  The boundary extension is kept separate: it additionally
requires the finite closed-cover argument from the last paragraph of the
paper's proof.
-/

namespace BeyondSperner
namespace AffineColoring

open Classical Set

/-- Successive cyclic rotation of a nonempty proper subset of `Fin (n+1)`
must leave the subset somewhere. -/
theorem exists_mem_finRotate_not_mem_of_nonempty_ne_univ
    {n : ℕ} {C : Finset (Fin (n + 1))}
    (hC : C.Nonempty) (hCne : C ≠ Finset.univ) :
    ∃ i ∈ C, finRotate (n + 1) i ∉ C := by
  by_contra hcontra
  have h : ∀ i ∈ C, finRotate (n + 1) i ∈ C := by
    intro i hiC
    by_contra hiRotate
    exact hcontra ⟨i, hiC, hiRotate⟩
  obtain ⟨i, hiC⟩ := hC
  have hcycle : ∀ j : Fin (n + 1), finCycle i j ∈ C := by
    intro j
    induction j using Fin.induction with
    | zero =>
        simpa [finCycle_apply] using hiC
    | succ j ih =>
        have hstep := h (finCycle i j.castSucc) ih
        have heq : finCycle i j.succ =
            finRotate (n + 1) (finCycle i j.castSucc) := by
          have hsucc : j.succ = j.castSucc + 1 := by
            apply Fin.ext
            simp
          rw [hsucc]
          simp only [finCycle_apply, finRotate_apply]
          abel
        rw [heq]
        exact hstep
  apply hCne
  apply Finset.eq_univ_of_forall
  intro k
  simpa using hcycle ((finCycle i).symm k)

variable {V P : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup P] [Module ℝ P]

/-- Strict barycentric interior of the simplex spanned by `b`.  The separate
membership hypothesis in Theorem 10.9 makes explicit which closed simplex is
being used. -/
def IsStrictInteriorPoint {n : ℕ}
    (b : AffineBasis (Fin (n + 1)) ℝ P) (z : P) : Prop :=
  ∀ i, 0 < b.coord i z

/-- A vector hedgehog coloring: at a vertex on the `i`th reference face,
the `i`th barycentric coordinate of its color is nonpositive. -/
def IsVectorHedgehogColoring {n : ℕ}
    (D : SimplexFamily (Fin (n + 1)) V)
    (b : AffineBasis (Fin (n + 1)) ℝ P)
    (p c : D.Vertex → P) : Prop :=
  ∀ v i, b.coord i (p v) = 0 → b.coord i (c v) ≤ 0

omit [Fintype V] in
/-- The strict-interior core of Theorem 10.9, parameterized by a provider
for the exact `IsAffineSolution` conclusion of Theorem 10.8.

The cyclically shifted affine basis is essential: if Theorem 10.8 selects a
proper nonempty `C`, choose `i ∈ C` whose successor leaves `C`.  All selected
colors and all artificial basis vertices then lie in the closed half-space
`b.coord (succ i) ≤ 0`, contradicting strict positivity of the target point.
-/
theorem theorem10_9_interior_of_solution_provider {n : ℕ}
    (D : SimplexFamily (Fin (n + 1)) V)
    (b : AffineBasis (Fin (n + 1)) ℝ P)
    (p c : D.Vertex → P)
    (hface : ∀ (C : Finset (Fin (n + 1))) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hhedgehog : IsVectorHedgehogColoring D b p c)
    (solve : ∀ (b' : AffineBasis (Fin (n + 1)) ℝ P) (q : P),
      q ∈ convexHull ℝ (Set.range b') →
        ∃ C : Finset (Fin (n + 1)), ∃ tau : Finset V,
          IsAffineSolution D b' c q C tau)
    (z : P) (hz : z ∈ convexHull ℝ (Set.range b))
    (hzInterior : IsStrictInteriorPoint b z) :
    ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
      sigma.card = n + 1 ∧
        z ∈ convexHull ℝ
          (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set P) := by
  let rotate : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1)
  let b' : AffineBasis (Fin (n + 1)) ℝ P := b.reindex rotate.symm
  have hrange : Set.range b' = Set.range b := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨rotate i, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨rotate.symm i, ?_⟩
      simp [b', rotate]
  have hz' : z ∈ convexHull ℝ (Set.range b') := by
    rw [hrange]
    exact hz
  obtain ⟨C, tau, hsol⟩ := solve b' z hz'
  rcases hsol with ⟨htau, hC, htauCard, hdata⟩
  dsimp only at hdata
  rcases hdata with ⟨_hSetCard, hzCompleted, _hAffineIndependent⟩
  by_cases hCuniv : C = Finset.univ
  · subst C
    refine ⟨tau, htau, ?_, ?_⟩
    · simpa using htauCard
    · simpa [affineCompletedPointFormula, affineSimplexColorPoints] using
        hzCompleted
  · obtain ⟨i, hiC, hiRotateC⟩ :=
      exists_mem_finRotate_not_mem_of_nonempty_ne_univ hC hCuniv
    let k : Fin (n + 1) := rotate i
    have hkC : k ∉ C := by simpa [k, rotate] using hiRotateC
    let H : Set P := (b.coord k) ⁻¹' Set.Iic 0
    have hCompletedSubset :
        (affineCompletedPointFormula D b' c C tau htau : Set P) ⊆ H := by
      intro q hq
      change q ∈ affineCompletedPointFormula D b' c C tau htau at hq
      rw [affineCompletedPointFormula] at hq
      rcases Finset.mem_union.mp hq with hqColor | hqBasis
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hqColor
        change b.coord k
            (c ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩) ≤ 0
        apply hhedgehog
        exact hface C tau htau
          ⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D htau v.2⟩
          v.2 k (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hkC⟩)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hqBasis
        have hjC : j ∉ C := (Finset.mem_sdiff.mp hj).2
        have hji : j ≠ i := fun hji ↦ hjC (hji ▸ hiC)
        have hkj : k ≠ rotate j := by
          intro hEq
          exact hji (rotate.injective hEq.symm)
        change b.coord k (b (rotate j)) ≤ 0
        rw [b.coord_apply_ne hkj]
    have hHConvex : Convex ℝ H := by
      exact (convex_Iic (0 : ℝ)).affine_preimage (b.coord k)
    have hzH : z ∈ H :=
      convexHull_min hCompletedSubset hHConvex hzCompleted
    exact False.elim ((not_le_of_gt (hzInterior k)) hzH)

/-- The strict-interior core of Theorem 10.9 using the default
oriented-matroid proof of Theorem 10.8. -/
theorem theorem10_9_interior {n : ℕ}
    (D : SimplexFamily (Fin (n + 1)) V)
    (b : AffineBasis (Fin (n + 1)) ℝ P)
    (p c : D.Vertex → P)
    (hchain : D.IsChainSimplex)
    (hface : ∀ (C : Finset (Fin (n + 1))) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hhedgehog : IsVectorHedgehogColoring D b p c)
    (z : P) (hz : z ∈ convexHull ℝ (Set.range b))
    (hzInterior : IsStrictInteriorPoint b z) :
    ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
      sigma.card = n + 1 ∧
        z ∈ convexHull ℝ
          (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set P) := by
  exact theorem10_9_interior_of_solution_provider D b p c hface hhedgehog
    (fun b' q hq ↦ theorem10_8 D b' c q hq hchain) z hz hzInterior

/-- Proof-independent color set of an abstract simplex.  The subtype in the
domain remembers that the colored vertex belongs to the ambient family. -/
def simplexVertexColorSet {I : Type*} [Fintype I]
    (D : SimplexFamily I V) (c : D.Vertex → P) (sigma : Finset V) : Set P :=
  c '' {v : D.Vertex | v.1 ∈ sigma}

omit [Fintype V] [AddCommGroup P] [Module ℝ P] in
/-- The proof-indexed finite color set used in Theorems 10.8--10.10 is
literally the proof-independent image of the simplex's vertices. -/
theorem coe_affineSimplexColorPoints_eq_simplexVertexColorSet
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : SimplexFamily I V) (c : D.Vertex → P)
    (C : Finset I) (sigma : Finset V) (hsigma : sigma ∈ D.complex C) :
    (affineSimplexColorPoints D c C sigma hsigma : Set P) =
      simplexVertexColorSet D c sigma := by
  ext q
  constructor
  · intro hq
    change q ∈ affineSimplexColorPoints D c C sigma hsigma at hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨⟨v.1, MatroidColoring.mem_vertexSet_of_mem_simplex D hsigma v.2⟩,
      v.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    change c v ∈ affineSimplexColorPoints D c C sigma hsigma
    apply Finset.mem_image.mpr
    refine ⟨⟨v.1, hv⟩, Finset.mem_attach _ _, ?_⟩
    rfl

/-- Full simplices of the ambient complex, packaged so that finite unions
over them can be handled without proof-dependent set expressions. -/
def FullSimplex {I : Type*} [Fintype I]
    (D : SimplexFamily I V) :=
  {sigma : Finset V //
    sigma ∈ D.complex Finset.univ ∧ sigma.card = Fintype.card I}

/-- Union of the color hulls of all full simplices. -/
def fullSimplexColorRegion {I : Type*} [Fintype I]
    (D : SimplexFamily I V) (c : D.Vertex → P) : Set P :=
  ⋃ sigma : FullSimplex D,
    convexHull ℝ (simplexVertexColorSet D c sigma.1)

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The color region of the full simplices is closed.  This is the detailed
form of the paper's statement that a finite union of finite convex hulls is
"obviously closed". -/
theorem isClosed_fullSimplexColorRegion {I : Type*} [Fintype I]
    [DecidableEq I] (D : SimplexFamily I V) (c : D.Vertex → E) :
    IsClosed (fullSimplexColorRegion D c) := by
  rw [fullSimplexColorRegion]
  let _ : Finite (FullSimplex D) :=
    Finite.of_injective (fun sigma : FullSimplex D ↦ sigma.1)
      Subtype.val_injective
  apply isClosed_iUnion_of_finite
  intro sigma
  have hfinite : (simplexVertexColorSet D c sigma.1).Finite := by
    exact (Set.toFinite {v : D.Vertex | v.1 ∈ sigma.1}).image c
  exact hfinite.isClosed_convexHull ℝ

/-- The finite-closed-union boundary extension in Theorem 10.9,
parameterized by a proof of the strict-interior case.

The supplied theorem covers `interior Γ`.  The target color region is
a finite union of closed finite convex hulls, hence closed.  Since a simplex
is the closure of its nonempty interior, that region covers the whole
reference simplex. -/
theorem theorem10_9_of_interior_provider {n : ℕ}
    (D : SimplexFamily (Fin (n + 1)) V)
    (b : AffineBasis (Fin (n + 1)) ℝ E)
    (c : D.Vertex → E)
    (interiorCover : ∀ (q : E),
      q ∈ convexHull ℝ (Set.range b) → IsStrictInteriorPoint b q →
        ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
          sigma.card = n + 1 ∧
            q ∈ convexHull ℝ
              (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set E))
    (z : E) (hz : z ∈ convexHull ℝ (Set.range b)) :
    ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
      sigma.card = n + 1 ∧
        z ∈ convexHull ℝ
          (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set E) := by
  let Gamma : Set E := convexHull ℝ (Set.range b)
  let U : Set E := fullSimplexColorRegion D c
  have hUClosed : IsClosed U := by
    exact isClosed_fullSimplexColorRegion D c
  have hInteriorSubset : interior Gamma ⊆ U := by
    intro q hq
    have hqGamma : q ∈ convexHull ℝ (Set.range b) := interior_subset hq
    have hqPositive : IsStrictInteriorPoint b q := by
      rw [b.interior_convexHull] at hq
      exact hq
    obtain ⟨sigma, hsigma, hsigmaCard, hqHull⟩ :=
      interiorCover q hqGamma hqPositive
    change q ∈ fullSimplexColorRegion D c
    rw [fullSimplexColorRegion]
    apply Set.mem_iUnion.mpr
    refine ⟨⟨sigma, hsigma, by simpa using hsigmaCard⟩, ?_⟩
    rw [← coe_affineSimplexColorPoints_eq_simplexVertexColorSet
      D c Finset.univ sigma hsigma]
    exact hqHull
  have hGammaClosed : IsClosed Gamma := by
    exact (Set.finite_range b).isClosed_convexHull ℝ
  have hGammaConvex : Convex ℝ Gamma := by
    exact convex_convexHull ℝ (Set.range b)
  have hGammaInteriorNonempty : (interior Gamma).Nonempty := by
    exact ⟨Finset.univ.centroid ℝ b, b.centroid_mem_interior_convexHull⟩
  have hclosure : closure (interior Gamma) = Gamma := by
    calc
      closure (interior Gamma) = closure Gamma :=
        hGammaConvex.closure_interior_eq_closure_of_nonempty_interior
          hGammaInteriorNonempty
      _ = Gamma := hGammaClosed.closure_eq
  have hzU : z ∈ U := by
    have hzClosure : z ∈ closure (interior Gamma) := by
      rw [hclosure]
      exact hz
    exact closure_minimal hInteriorSubset hUClosed hzClosure
  change z ∈ fullSimplexColorRegion D c at hzU
  rw [fullSimplexColorRegion] at hzU
  obtain ⟨sigma, hzHull⟩ := Set.mem_iUnion.mp hzU
  refine ⟨sigma.1, sigma.2.1, by simpa using sigma.2.2, ?_⟩
  rw [coe_affineSimplexColorPoints_eq_simplexVertexColorSet
    D c Finset.univ sigma.1 sigma.2.1]
  exact hzHull

/-- The full vector-hedgehog Theorem 10.9, including boundary points, using
the default oriented-matroid proof of Theorem 10.8. -/
theorem theorem10_9 {n : ℕ}
    (D : SimplexFamily (Fin (n + 1)) V)
    (b : AffineBasis (Fin (n + 1)) ℝ E)
    (p c : D.Vertex → E)
    (hchain : D.IsChainSimplex)
    (hface : ∀ (C : Finset (Fin (n + 1))) (tau : Finset V)
      (_htau : tau ∈ D.complex C) (v : D.Vertex), v.1 ∈ tau →
      ∀ i ∈ Finset.univ \ C, b.coord i (p v) = 0)
    (hhedgehog : IsVectorHedgehogColoring D b p c)
    (z : E) (hz : z ∈ convexHull ℝ (Set.range b)) :
    ∃ sigma : Finset V, ∃ hsigma : sigma ∈ D.complex Finset.univ,
      sigma.card = n + 1 ∧
        z ∈ convexHull ℝ
          (affineSimplexColorPoints D c Finset.univ sigma hsigma : Set E) := by
  exact theorem10_9_of_interior_provider D b c
    (fun q hq hqInterior ↦
      theorem10_9_interior D b p c hchain hface hhedgehog
        q hq hqInterior) z hz

end Normed

end AffineColoring
end BeyondSperner
