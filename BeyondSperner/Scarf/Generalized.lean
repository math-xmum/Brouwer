import BeyondSperner.Orders.LinearOrders
import BeyondSperner.Coloring.Matroid.General

/-!
# The generalized Scarf theorem

The final “families of linear orders” formulation following Theorem 8.5.  The statement uses the
disjoint union `X ⊕ I` to make the paper's assumption `X ∩ I = ∅` true by construction.
-/

namespace BeyondSperner

open Classical
open Set

namespace GeneralizedScarf

variable {I X M : Type*} [Fintype I] [Fintype X] [Nonempty I] [Nonempty X]
  [DecidableEq I] [DecidableEq X] [DecidableEq M] [LinearOrder I]

/-- A coloring `c : X → M-b`. -/
abbrev Coloring (X : Type*) (F : MatroidColoring.Framework I M) :=
  X → {m : M // m ≠ F.distinguished}

/-- Extend the coloring by `φ(i)=v_i`. -/
def extendedColoring (F : MatroidColoring.Framework I M) (c : Coloring X F) :
    X ⊕ I → M :=
  Sum.elim (fun x ↦ (c x).1) F.vertex

/-- Image of a finite subset of `X ⊕ I` under the extended coloring. -/
def colorImage (F : MatroidColoring.Framework I M) (c : Coloring X F)
    (S : Finset (X ⊕ I)) : Finset M :=
  S.image (extendedColoring F c)

/-- The full conclusion of the generalized Scarf theorem. -/
def IsSolution (orders : IndexedLinearOrders I X)
    (F : MatroidColoring.Framework I M) (c : Coloring X F)
    (S : Finset (X ⊕ I)) : Prop :=
  orders.extend.IsDominant S Finset.univ ∧
    S.card = Fintype.card I ∧
      F.matroid.IsGoodBasis F.distinguished (colorImage F c S : Set M)

/-- Formula (33) in the cell presentation. -/
def completedCellImage (F : MatroidColoring.Framework I M) (c : Coloring X F)
    (τ : Finset X) (C : Finset I) : Finset M :=
  τ.image (fun x ↦ (c x).1) ∪ (Finset.univ \ C).image F.vertex

/-- A cell-form solution, the intermediate conclusion obtained from Theorem 8.5. -/
def IsCellSolution (orders : IndexedLinearOrders I X)
    (F : MatroidColoring.Framework I M) (c : Coloring X F)
    (τ : Finset X) (C : Finset I) : Prop :=
  orders.IsCell τ C ∧
    F.matroid.IsGoodBasis F.distinguished
      (completedCellImage F c τ C : Set M)

omit [Nonempty I] in
/-- Cell-form solutions give the final dominant subset via Lemma 7.3. -/
theorem IsCellSolution.toSolution
    {orders : IndexedLinearOrders I X} {F : MatroidColoring.Framework I M}
    {c : Coloring X F} {τ : Finset X} {C : Finset I}
    (h : IsCellSolution orders F c τ C) :
    IsSolution orders F c (IndexedLinearOrders.extendCell τ C) := by
  rcases h with ⟨⟨hdom, hcard⟩, hgood⟩
  refine ⟨(orders.dominant_extendCell_iff τ C).2 hdom, ?_, ?_⟩
  · have hdisj : Disjoint (τ.image Sum.inl)
        ((Finset.univ \ C).image Sum.inr) := by
      rw [Finset.disjoint_left]
      intro z hzleft hzright
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hzleft
      obtain ⟨i, _, hEq⟩ := Finset.mem_image.mp hzright
      exact Sum.inr_ne_inl hEq
    rw [IndexedLinearOrders.extendCell, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective, hcard]
    simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    exact Nat.add_sub_of_le (Finset.card_le_univ C)
  · simpa [colorImage, completedCellImage, IndexedLinearOrders.extendCell,
      extendedColoring, Finset.image_union, Finset.image_image] using hgood

omit [Nonempty I] in
/-- The generalized Scarf theorem stated after Theorem 8.5. -/
theorem generalizedScarf
    [Fintype M] (orders : IndexedLinearOrders I X)
    (F : MatroidColoring.Framework I M) (c : Coloring X F) :
    ∃ S : Finset (X ⊕ I), IsSolution orders F c S := by
  let c' : MatroidColoring.Coloring orders.associatedFamily F :=
    fun x ↦ c x.1
  obtain ⟨C, τ, hτ, hC, hcard, hgood⟩ :=
    MatroidColoring.theorem8_5 orders.associatedFamily F
      orders.associatedFamily_isChainSimplex c'
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
  have hcolor :
      MatroidColoring.colorImage orders.associatedFamily F c' τ hτ =
        τ.image (fun x ↦ (c x).1) := by
    ext m
    simp [MatroidColoring.colorImage, c']
  have hcellSolution : IsCellSolution orders F c τ C := by
    refine ⟨hcell, ?_⟩
    simpa [MatroidColoring.completedImage, completedCellImage, hcolor] using hgood
  exact ⟨IndexedLinearOrders.extendCell τ C, hcellSolution.toSolution⟩

end GeneralizedScarf

end BeyondSperner
