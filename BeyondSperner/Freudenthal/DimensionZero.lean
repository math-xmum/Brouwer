import BeyondSperner.Freudenthal.Complex

/-!
# The zero-dimensional Freudenthal base case

The proof of Theorem 4.8 starts an induction at `n = 0`.  This file checks
that base case from the concrete definitions: `Point N 0` has one element,
the Freudenthal complex has one facet, and the facet set satisfies all three
combinatorial hypotheses used by the top-chain uniqueness theorem.
-/

namespace BeyondSperner

open Classical

namespace IntegerSimplex

/-- The unique integer point of the zero-dimensional simplex. -/
def zeroDimPoint (N : ℕ) : Point N 0 :=
  ⟨fun _ ↦ ⟨N, Nat.lt_succ_self N⟩, by simp⟩

theorem point_eq_zeroDimPoint (a : Point N 0) :
    a = zeroDimPoint N := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simpa [zeroDimPoint] using a.2

theorem point_zero_subsingleton (a b : Point N 0) : a = b := by
  rw [point_eq_zeroDimPoint a, point_eq_zeroDimPoint b]

@[simp]
theorem univ_point_zero :
    (Finset.univ : Finset (Point N 0)) = {zeroDimPoint N} := by
  ext a
  simp [point_eq_zeroDimPoint a]

theorem zeroDimPoint_isFreudenthalTopSimplex :
    IsFreudenthalTopSimplex ({zeroDimPoint N} : Finset (Point N 0)) := by
  refine ⟨zeroDimPoint N, Equiv.refl (Fin 0), ?_⟩
  rw [Finset.image_singleton]
  simp [stepSimplex, stepSequence, permutationList]

/-- In dimension zero there is exactly one Freudenthal facet. -/
theorem freudenthalFacets_zero_dim :
    freudenthalFacets N 0 = {{zeroDimPoint N}} := by
  ext rho
  constructor
  · intro hrho
    have hcard := ((mem_freudenthalFacets_iff rho).1 hrho).card
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (by simpa using hcard)
    simp [point_eq_zeroDimPoint a]
  · intro hrho
    have heq : rho = {zeroDimPoint N} := by simpa using hrho
    subst rho
    exact (mem_freudenthalFacets_iff _).2
      zeroDimPoint_isFreudenthalTopSimplex

theorem freudenthalFacets_zero_dim_nonbranching :
    FacetChain.Nonbranching (freudenthalFacets N 0) 0 := by
  intro rho hrho
  have hrhoEmpty : rho = ∅ := Finset.card_eq_zero.mp hrho
  subst rho
  rw [freudenthalFacets_zero_dim]
  simp

theorem freudenthalFacets_zero_dim_stronglyConnected :
    FacetChain.StronglyFacetConnected (freudenthalFacets N 0) 0 := by
  intro sigma hsigma tau htau
  rw [freudenthalFacets_zero_dim] at hsigma htau
  simp only [Finset.mem_singleton] at hsigma htau
  subst sigma
  subst tau
  exact Relation.ReflTransGen.refl

theorem freudenthalFacets_zero_dim_hasNonemptyBoundary :
    FacetChain.HasNonemptyBoundary (freudenthalFacets N 0) 0 := by
  refine ⟨∅, by simp, ?_⟩
  rw [freudenthalFacets_zero_dim]
  simp

/-- The unique zero-dimensional vertex is the unique full cell. -/
theorem zeroDimPoint_isFullCell :
    (pointOrders N 0).IsCell ({zeroDimPoint N} : Finset (Point N 0))
      Finset.univ := by
  constructor
  · constructor
    · exact ⟨0, Finset.mem_univ 0⟩
    · intro y
      refine ⟨0, Finset.mem_univ 0, ?_⟩
      intro x hx
      rw [point_eq_zeroDimPoint y, point_eq_zeroDimPoint x]
      exact @le_refl (Point N 0) ((pointOrders N 0) 0).toPreorder
        (zeroDimPoint N)
  · simp

private theorem eq_singleton_zeroDimPoint_of_card_one
    {sigma : Finset (Point N 0)} (hcard : sigma.card = 1) :
    sigma = {zeroDimPoint N} := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  simp [point_eq_zeroDimPoint a]

private theorem singleton_zeroDimPoint_mem_associatedComplex :
    ({zeroDimPoint N} : Finset (Point N 0)) ∈
      (pointOrders N 0).associatedComplex Finset.univ := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg]
  · exact Or.inr ⟨{zeroDimPoint N}, zeroDimPoint_isFullCell,
      Finset.Subset.rfl⟩
  · simp

/-- The simplicial-complex part of Theorem 4.8 in the `n = 0` base case. -/
theorem associatedComplex_eq_freudenthalComplex_zero_dim :
    (pointOrders N 0).associatedComplex Finset.univ =
      freudenthalComplex N 0 := by
  apply FiniteSimplicialComplex.ext
  ext tau
  constructor
  · intro htau
    exact associatedComplex_subset_freudenthalComplex htau
  · intro htau
    have hsimp := (mem_freudenthalComplex_iff tau).1 htau
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [IndexedLinearOrders.IsAssociatedSimplex, if_neg (by simp)]
    rcases hsimp with rfl | ⟨rho, hrho, hsub⟩
    · exact Or.inl rfl
    · right
      have hrhoSingleton : rho = {zeroDimPoint N} :=
        eq_singleton_zeroDimPoint_of_card_one (by simpa using hrho.card)
      exact ⟨{zeroDimPoint N}, zeroDimPoint_isFullCell,
        hrhoSingleton ▸ hsub⟩

/-- Equation (20) in the `n = 0` base case, proved by identifying the unique
coefficient-one simplex on both sides. -/
theorem associatedTopChain_eq_freudenthalTopChain_zero_dim :
    associatedTopChain N 0 = freudenthalTopChain N 0 := by
  ext sigma
  rw [associatedTopChain, SimplexFamily.topChain_apply,
    freudenthalTopChain_apply]
  by_cases hsigma : sigma = {zeroDimPoint N}
  · subst sigma
    rw [if_pos]
    · rw [if_pos zeroDimPoint_isFreudenthalTopSimplex]
    · exact ⟨singleton_zeroDimPoint_mem_associatedComplex, by simp⟩
  · rw [if_neg, if_neg]
    · intro htop
      exact hsigma (eq_singleton_zeroDimPoint_of_card_one htop.card)
    · rintro ⟨hsimplex, hcard⟩
      exact hsigma (eq_singleton_zeroDimPoint_of_card_one (by simpa using hcard))

end IntegerSimplex

end BeyondSperner
