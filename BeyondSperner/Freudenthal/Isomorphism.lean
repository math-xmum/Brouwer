import BeyondSperner.Freudenthal.Boundary

/-!
# The cumulative-coordinate simplicial isomorphism

Ivanov's Theorem 4.8 is stated as an isomorphism
`phi : T(I) -> F(I)` induced by the cumulative-coordinate map `s`.  The
earlier files prove the equivalent equality after pulling the Freudenthal
complex back to `Point N n`.  This file restores the literal target vertex
type: the integer points of the monotone simplex `Gamma`.

The target complex below is defined independently from standard
Freudenthal vertex sets in cumulative coordinates.  It is not defined by
relabeling the source complex, so the subsequent relabeling equality carries
genuine mathematical content.
-/

namespace BeyondSperner

open Classical

namespace IntegerSimplex

/-- Integer points of the monotone simplex `Gamma`, as an actual vertex
type. -/
abbrev GammaPoint (N n : ℕ) :=
  {y : Fin n → ℤ // IsGammaPoint (N : ℤ) y}

/-- Finiteness is transported from the bounded integer simplex through the
proved cumulative-coordinate equivalence. -/
noncomputable instance gammaPointFintype (N n : ℕ) :
    Fintype (GammaPoint N n) :=
  Fintype.ofEquiv (Point N n) (pointGammaEquiv N n)

private theorem image_symm_image_equiv {A B : Type*}
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (s : Finset B) :
    (s.image e.symm).image e = s := by
  ext y
  simp

/-- A genuine top-dimensional Freudenthal simplex on the integer vertices
of `Gamma`.  Containment in `Gamma` is enforced by the vertex subtype; the
displayed equality is the standard translated-permutation presentation. -/
def IsGammaFreudenthalTopSimplex {N n : ℕ}
    (rho : Finset (GammaPoint N n)) : Prop :=
  ∃ u : Fin n → ℤ, ∃ omega : Equiv.Perm (Fin n),
    rho.image Subtype.val =
      freudenthalSimplex u (permutationList omega)

/-- Faces of top-dimensional Freudenthal simplices in `Gamma`, including
the empty face. -/
def IsGammaFreudenthalSimplex {N n : ℕ}
    (tau : Finset (GammaPoint N n)) : Prop :=
  tau = ∅ ∨ ∃ rho : Finset (GammaPoint N n),
    IsGammaFreudenthalTopSimplex rho ∧ tau ⊆ rho

theorem IsGammaFreudenthalSimplex.of_subset {N n : ℕ}
    {sigma tau : Finset (GammaPoint N n)}
    (hsigma : IsGammaFreudenthalSimplex sigma) (htau : tau ⊆ sigma) :
    IsGammaFreudenthalSimplex tau := by
  rcases hsigma with rfl | ⟨rho, hrho, hsigma⟩
  · left
    exact Finset.Subset.antisymm htau (Finset.empty_subset tau)
  · exact Or.inr ⟨rho, hrho, htau.trans hsigma⟩

/-- The abstract simplicial complex of the Freudenthal triangulation on the
integer vertices of `Gamma`. -/
noncomputable def gammaFreudenthalComplex (N n : ℕ) :
    FiniteSimplicialComplex (GammaPoint N n) where
  simplices := Finset.univ.filter IsGammaFreudenthalSimplex
  empty_mem := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, Or.inl rfl⟩
  downward_closed := by
    intro sigma tau hsigma htau
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, IsGammaFreudenthalSimplex.of_subset
      (Finset.mem_filter.mp hsigma).2 htau⟩

theorem mem_gammaFreudenthalComplex_iff {N n : ℕ}
    (tau : Finset (GammaPoint N n)) :
    tau ∈ gammaFreudenthalComplex N n ↔
      IsGammaFreudenthalSimplex tau := by
  change tau ∈ Finset.univ.filter IsGammaFreudenthalSimplex ↔ _
  simp

/-- Top-dimensional Freudenthal simplices in the literal `Gamma` vertex
type. -/
noncomputable def gammaFreudenthalFacets (N n : ℕ) :
    Finset (Finset (GammaPoint N n)) :=
  Finset.univ.filter IsGammaFreudenthalTopSimplex

theorem mem_gammaFreudenthalFacets_iff {N n : ℕ}
    (rho : Finset (GammaPoint N n)) :
    rho ∈ gammaFreudenthalFacets N n ↔
      IsGammaFreudenthalTopSimplex rho := by
  simp [gammaFreudenthalFacets]

theorem IsGammaFreudenthalTopSimplex.card {N n : ℕ}
    {rho : Finset (GammaPoint N n)}
    (hrho : IsGammaFreudenthalTopSimplex rho) :
    rho.card = n + 1 := by
  obtain ⟨u, omega, heq⟩ := hrho
  rw [← Finset.card_image_of_injective rho Subtype.val_injective,
    heq, card_freudenthalSimplex_of_nodup u
      (nodup_permutationList omega), length_permutationList]

theorem IsGammaFreudenthalTopSimplex.mem_complex {N n : ℕ}
    {rho : Finset (GammaPoint N n)}
    (hrho : IsGammaFreudenthalTopSimplex rho) :
    rho ∈ gammaFreudenthalComplex N n := by
  exact (mem_gammaFreudenthalComplex_iff rho).2
    (Or.inr ⟨rho, hrho, Finset.Subset.rfl⟩)

theorem gammaFreudenthalFacets_eq_topSimplices {N n : ℕ} :
    gammaFreudenthalFacets N n =
      (gammaFreudenthalComplex N n).topSimplices (n + 1) := by
  ext tau
  constructor
  · intro htau
    have htop := (mem_gammaFreudenthalFacets_iff tau).1 htau
    exact Finset.mem_filter.mpr ⟨htop.mem_complex, htop.card⟩
  · intro htau
    have hdata := Finset.mem_filter.mp htau
    have hsimp := (mem_gammaFreudenthalComplex_iff tau).1 hdata.1
    apply (mem_gammaFreudenthalFacets_iff tau).2
    rcases hsimp with hzero | ⟨rho, hrho, hsub⟩
    · subst tau
      simp at hdata
    · have heq : tau = rho := Finset.eq_of_subset_of_card_le hsub (by
        rw [hrho.card, hdata.2])
      simpa [heq] using hrho

/-- The target chain `F[[I]]` in the literal `Gamma` vertex type. -/
noncomputable def gammaFreudenthalTopChain (N n : ℕ) :
    SimplexFamily.Chain (GammaPoint N n) :=
  FacetChain.sum (gammaFreudenthalFacets N n)

theorem gammaFreudenthalTopChain_eq_complexCardChain (N n : ℕ) :
    gammaFreudenthalTopChain N n =
      SimplexFamily.complexCardChain
        (gammaFreudenthalComplex N n) (n + 1) := by
  rw [gammaFreudenthalTopChain, FacetChain.sum,
    SimplexFamily.complexCardChain,
    gammaFreudenthalFacets_eq_topSimplices]

/-- Applying the integer cumulative-coordinate equivalence and then
forgetting its `Gamma` certificate is exactly `pointPrefix`. -/
theorem image_pointGammaEquiv_image_val {N n : ℕ}
    (rho : Finset (Point N n)) :
    (rho.image (pointGammaEquiv N n)).image Subtype.val =
      rho.image pointPrefix := by
  ext y
  simp [pointGammaEquiv]

/-- A source Freudenthal facet is carried to, and reflected from, a literal
target Freudenthal facet by the cumulative-coordinate equivalence. -/
theorem isGammaFreudenthalTopSimplex_image_pointGammaEquiv_iff
    {N n : ℕ} (rho : Finset (Point N n)) :
    IsGammaFreudenthalTopSimplex
        (rho.image (pointGammaEquiv N n)) ↔
      IsFreudenthalTopSimplex rho := by
  rw [isFreudenthalTopSimplex_iff_cumulative]
  change
    (∃ u : Fin n → ℤ, ∃ omega : Equiv.Perm (Fin n),
      (rho.image (pointGammaEquiv N n)).image Subtype.val =
        freudenthalSimplex u (permutationList omega)) ↔
      ∃ u : Fin n → ℤ, ∃ omega : Equiv.Perm (Fin n),
        rho.image pointPrefix =
          freudenthalSimplex u (permutationList omega)
  rw [image_pointGammaEquiv_image_val]

/-- Lemma 4.6 at complex level: the independently defined target
Freudenthal complex is exactly the relabeling of the pulled-back complex by
the cumulative-coordinate equivalence. -/
theorem freudenthalComplex_relabel_pointGammaEquiv {N n : ℕ} :
    (freudenthalComplex N n).relabel (pointGammaEquiv N n) =
      gammaFreudenthalComplex N n := by
  apply FiniteSimplicialComplex.ext
  ext tau
  constructor
  · intro htau
    obtain ⟨sigma, hsigma, rfl⟩ :=
      (FiniteSimplicialComplex.mem_relabel_iff
        (freudenthalComplex N n) (pointGammaEquiv N n) _).1 htau
    apply (mem_gammaFreudenthalComplex_iff _).2
    rcases (mem_freudenthalComplex_iff sigma).1 hsigma with
      hzero | ⟨rho, hrho, hsub⟩
    · subst sigma
      exact Or.inl (by simp)
    · exact Or.inr
        ⟨rho.image (pointGammaEquiv N n),
          (isGammaFreudenthalTopSimplex_image_pointGammaEquiv_iff rho).2
            hrho,
          Finset.image_mono _ hsub⟩
  · intro htau
    have hsimp := (mem_gammaFreudenthalComplex_iff tau).1 htau
    rcases hsimp with rfl | ⟨rho, hrho, hsub⟩
    · exact (freudenthalComplex N n).relabel
        (pointGammaEquiv N n) |>.empty_mem
    · let sigma : Finset (Point N n) :=
        rho.image (pointGammaEquiv N n).symm
      let eta : Finset (Point N n) :=
        tau.image (pointGammaEquiv N n).symm
      have hsigmaImage : sigma.image (pointGammaEquiv N n) = rho := by
        exact image_symm_image_equiv (pointGammaEquiv N n) rho
      have hetaImage : eta.image (pointGammaEquiv N n) = tau := by
        exact image_symm_image_equiv (pointGammaEquiv N n) tau
      have hsigmaTop : IsFreudenthalTopSimplex sigma := by
        apply (isGammaFreudenthalTopSimplex_image_pointGammaEquiv_iff
          sigma).1
        simpa [hsigmaImage] using hrho
      have hetaSub : eta ⊆ sigma := by
        intro x hx
        have hxImage : (pointGammaEquiv N n) x ∈ tau := by
          rw [← hetaImage]
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        have hxRho := hsub hxImage
        rw [← hsigmaImage] at hxRho
        obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hxRho
        have hzx' : z = x := (pointGammaEquiv N n).injective hzx
        simpa [hzx'] using hz
      apply (FiniteSimplicialComplex.mem_relabel_iff
        (freudenthalComplex N n) (pointGammaEquiv N n) tau).2
      refine ⟨eta, (mem_freudenthalComplex_iff eta).2
        (Or.inr ⟨sigma, hsigmaTop, hetaSub⟩), hetaImage⟩

/-- The cumulative-coordinate equivalence as an actual isomorphism from the
pulled-back Freudenthal complex to the literal target complex. -/
noncomputable def freudenthalChangeOfCoordinatesIso (N n : ℕ) :
    FiniteSimplicialComplex.Iso (freudenthalComplex N n)
      (gammaFreudenthalComplex N n) where
  vertexEquiv := pointGammaEquiv N n
  relabel_eq := freudenthalComplex_relabel_pointGammaEquiv

/-- Literal abstract-complex form of Theorem 4.8: at positive scale the
cumulative-coordinate map `s` carries the Scarf complex exactly to the
independently defined Freudenthal complex on integer points of `Gamma`. -/
theorem associatedComplex_relabel_pointGammaEquiv_eq_gamma_of_pos
    {N n : ℕ} (hN : 0 < N) :
    ((pointOrders N n).associatedComplex Finset.univ).relabel
        (pointGammaEquiv N n) =
      gammaFreudenthalComplex N n := by
  rw [associatedComplex_eq_freudenthalComplex_of_pos hN,
    freudenthalComplex_relabel_pointGammaEquiv]

/-- The simplicial isomorphism `phi` in Theorem 4.8, not merely an equality
of complexes after identifying their vertex types. -/
noncomputable def scarfFreudenthalIsoOfPos {N n : ℕ} (hN : 0 < N) :
    FiniteSimplicialComplex.Iso
      ((pointOrders N n).associatedComplex Finset.univ)
      (gammaFreudenthalComplex N n) where
  vertexEquiv := pointGammaEquiv N n
  relabel_eq :=
    associatedComplex_relabel_pointGammaEquiv_eq_gamma_of_pos hN

/-- Equation (20) in the literal codomain chain group on integer points of
`Gamma`: pushing the Scarf top chain through `phi` gives `F[[I]]`. -/
theorem relabel_associatedTopChain_eq_gammaFreudenthalTopChain_of_pos
    {N n : ℕ} (hN : 0 < N) :
    SimplexFamily.relabelChainHom (pointGammaEquiv N n)
        (associatedTopChain N n) =
      gammaFreudenthalTopChain N n := by
  rw [associatedTopChain_eq_complexCardChain,
    SimplexFamily.relabelChainHom_complexCardChain,
    associatedComplex_relabel_pointGammaEquiv_eq_gamma_of_pos hN,
    gammaFreudenthalTopChain_eq_complexCardChain]

end IntegerSimplex

end BeyondSperner
