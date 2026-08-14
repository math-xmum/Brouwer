import BeyondSperner.Simplicial.ChainSimplex

/-!
# Uniqueness of a top chain from its boundary

Ivanov uses the following finite combinatorial fact in Theorem 4.8 without
proof: in a non-branching, strongly facet-connected pure complex with a
nonempty boundary, the sum of all top simplices is the unique top-dimensional
chain with its boundary.  This file proves exactly that statement over
`ZMod 2`, in a form independent of any geometric realization.
-/

namespace BeyondSperner

open Classical

namespace FacetChain

variable {V : Type*} [DecidableEq V]

/-- The `F₂`-chain which is the sum of a specified finite set of facets. -/
noncomputable def sum (S : Finset (Finset V)) : SimplexFamily.Chain V :=
  ∑ sigma ∈ S, SimplexFamily.singletonChain sigma

@[simp]
theorem sum_apply (S : Finset (Finset V)) (sigma : Finset V) :
    sum S sigma = if sigma ∈ S then 1 else 0 := by
  simp [sum, SimplexFamily.singletonChain, Finsupp.single_apply]

/-- A chain has no coefficients outside the specified facet set. -/
def SupportedOn (c : SimplexFamily.Chain V)
    (S : Finset (Finset V)) : Prop :=
  ∀ sigma, sigma ∉ S → c sigma = 0

theorem supportedOn_sum (S : Finset (Finset V)) :
    SupportedOn (sum S) S := by
  intro sigma hsigma
  simp [hsigma]

/-- Two facets are adjacent when they are distinct members of `S` sharing a
codimension-one face. -/
def Adjacent (S : Finset (Finset V)) (n : ℕ)
    (sigma tau : Finset V) : Prop :=
  sigma ∈ S ∧ tau ∈ S ∧ sigma ≠ tau ∧
    (sigma ∩ tau).card = n

/-- Strong connectivity through codimension-one facet adjacencies. -/
def StronglyFacetConnected (S : Finset (Finset V)) (n : ℕ) : Prop :=
  ∀ sigma ∈ S, ∀ tau ∈ S,
    Relation.ReflTransGen (Adjacent S n) sigma tau

/-- Every codimension-one face belongs to at most two selected facets. -/
def Nonbranching (S : Finset (Finset V)) (n : ℕ) : Prop :=
  ∀ rho : Finset V, rho.card = n →
    (S.filter fun sigma ↦ rho ⊆ sigma).card ≤ 2

/-- There is a codimension-one face belonging to exactly one selected facet. -/
def HasNonemptyBoundary (S : Finset (Finset V)) (n : ℕ) : Prop :=
  ∃ rho : Finset V, rho.card = n ∧
    (S.filter fun sigma ↦ rho ⊆ sigma).card = 1

/-- Purity of the selected facet set. -/
def IsPure (S : Finset (Finset V)) (n : ℕ) : Prop :=
  ∀ sigma ∈ S, sigma.card = n + 1

private theorem boundary_apply_of_supportedOn
    {S : Finset (Finset V)} {n : ℕ}
    {c : SimplexFamily.Chain V} (hpure : IsPure S n)
    (hsupp : SupportedOn c S) {rho : Finset V} (hrho : rho.card = n) :
    SimplexFamily.boundary c rho =
      ∑ sigma ∈ S.filter (fun tau ↦ rho ⊆ tau), c sigma := by
  change (c.sum fun sigma a ↦
    a • SimplexFamily.boundarySimplex sigma) rho = _
  rw [Finsupp.sum_apply]
  classical
  rw [Finsupp.sum]
  calc
    ∑ sigma ∈ c.support,
          (c sigma • SimplexFamily.boundarySimplex sigma) rho =
        ∑ sigma ∈ c.support,
          if rho ⊆ sigma then c sigma else 0 := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      have hsigmaS : sigma ∈ S := by
        by_contra hnot
        exact (Finsupp.mem_support_iff.mp hsigma) (hsupp sigma hnot)
      rw [Finsupp.smul_apply, SimplexFamily.boundarySimplex_apply]
      simp [hrho, hpure sigma hsigmaS]
    _ = ∑ sigma ∈ c.support.filter (fun tau ↦ rho ⊆ tau), c sigma := by
      rw [Finset.sum_filter]
    _ = ∑ sigma ∈ S.filter (fun tau ↦ rho ⊆ tau), c sigma := by
      apply Finset.sum_subset
      · intro sigma hsigma
        simp only [Finset.mem_filter] at hsigma ⊢
        refine ⟨?_, hsigma.2⟩
        by_contra hnot
        exact (Finsupp.mem_support_iff.mp hsigma.1) (hsupp sigma hnot)
      · intro sigma hsigmaS hsigmaSupport
        have hsigmaSub : rho ⊆ sigma := (Finset.mem_filter.mp hsigmaS).2
        have hnotSupport : sigma ∉ c.support := by
          intro hmem
          exact hsigmaSupport (Finset.mem_filter.mpr ⟨hmem, hsigmaSub⟩)
        simpa only [Finsupp.mem_support_iff, not_ne_iff] using hnotSupport

/-- For a pure facet set, the coefficient of a codimension-one simplex in
the boundary of the all-facets chain is the coface count reduced modulo two.
This exposes the exact local incidence quantity used in pseudomanifold
boundary computations. -/
theorem boundary_sum_apply_of_card
    {S : Finset (Finset V)} {n : ℕ}
    (hpure : IsPure S n) {rho : Finset V} (hrho : rho.card = n) :
    SimplexFamily.boundary (sum S) rho =
      ((S.filter fun sigma ↦ rho ⊆ sigma).card : ZMod 2) := by
  rw [boundary_apply_of_supportedOn hpure (supportedOn_sum S) hrho]
  calc
    (∑ sigma ∈ S.filter (fun tau ↦ rho ⊆ tau), sum S sigma) =
        ∑ _sigma ∈ S.filter (fun tau ↦ rho ⊆ tau), (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      rw [sum_apply, if_pos (Finset.mem_filter.mp hsigma).1]
    _ = ((S.filter fun sigma ↦ rho ⊆ sigma).card : ZMod 2) := by
      simp

/-- The boundary of a pure `n`-dimensional facet chain has no coefficient
outside cardinality `n`. -/
theorem boundary_sum_apply_of_card_ne
    {S : Finset (Finset V)} {n : ℕ}
    (hpure : IsPure S n) {rho : Finset V} (hrho : rho.card ≠ n) :
    SimplexFamily.boundary (sum S) rho = 0 := by
  change (SimplexFamily.boundaryHom
    (∑ sigma ∈ S, SimplexFamily.singletonChain sigma)) rho = 0
  simp only [map_sum, SimplexFamily.boundaryHom_singletonChain]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro sigma hsigma
  rw [SimplexFamily.boundarySimplex_apply, if_neg]
  rintro ⟨_, hcard⟩
  have hsigmaCard := hpure sigma hsigma
  omega

private theorem cofaces_eq_pair_of_adjacent
    {S : Finset (Finset V)} {n : ℕ}
    (hnb : Nonbranching S n)
    {sigma tau : Finset V} (hadj : Adjacent S n sigma tau) :
    S.filter (fun omega ↦ sigma ∩ tau ⊆ omega) = {sigma, tau} := by
  let rho := sigma ∩ tau
  have hrho : rho.card = n := hadj.2.2.2
  have hsigma : sigma ∈ S.filter (fun omega ↦ rho ⊆ omega) := by
    simp [rho, hadj.1]
  have htau : tau ∈ S.filter (fun omega ↦ rho ⊆ omega) := by
    simp [rho, hadj.2.1]
  have hsub : {sigma, tau} ⊆
      S.filter (fun omega ↦ rho ⊆ omega) := by
    intro omega homega
    simp only [Finset.mem_insert, Finset.mem_singleton] at homega
    rcases homega with rfl | rfl
    · exact hsigma
    · exact htau
  have hpairCard : ({sigma, tau} : Finset (Finset V)).card = 2 := by
    simp [hadj.2.2.1]
  change S.filter (fun omega ↦ rho ⊆ omega) = {sigma, tau}
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hpairCard]
  exact hnb rho hrho

private theorem coeff_eq_of_adjacent_cycle
    {S : Finset (Finset V)} {n : ℕ}
    {c : SimplexFamily.Chain V} (hpure : IsPure S n)
    (hnb : Nonbranching S n) (hsupp : SupportedOn c S)
    (hcycle : SimplexFamily.boundary c = 0)
    {sigma tau : Finset V} (hadj : Adjacent S n sigma tau) :
    c sigma = c tau := by
  let rho := sigma ∩ tau
  have hrho : rho.card = n := hadj.2.2.2
  have hcoeff := (Finsupp.ext_iff.mp hcycle) rho
  rw [boundary_apply_of_supportedOn hpure hsupp hrho] at hcoeff
  rw [cofaces_eq_pair_of_adjacent hnb hadj] at hcoeff
  simp only [Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, hadj.2.2.1, not_false_eq_true] at hcoeff
  have : c sigma + c tau = 0 := by simpa using hcoeff
  exact eq_neg_of_add_eq_zero_left this |>.trans (ZMod.neg_eq_self_mod_two _)

private theorem coeff_eq_of_connected_cycle
    {S : Finset (Finset V)} {n : ℕ}
    {c : SimplexFamily.Chain V} (hpure : IsPure S n)
    (hnb : Nonbranching S n) (hsupp : SupportedOn c S)
    (hcycle : SimplexFamily.boundary c = 0)
    {sigma tau : Finset V}
    (hpath : Relation.ReflTransGen (Adjacent S n) sigma tau) :
    c sigma = c tau := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl _ => rfl
  | single hadj => exact coeff_eq_of_adjacent_cycle hpure hnb hsupp hcycle hadj
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- The finite chain-uniqueness fact used in Ivanov's proof of Theorem 4.8.
No topological theorem is assumed: coefficients propagate across adjacent
facets, and the unique coface at a boundary face forces the common coefficient
of the difference cycle to vanish. -/
theorem eq_sum_of_boundary_eq
    {S : Finset (Finset V)} {n : ℕ}
    (hpure : IsPure S n) (hnb : Nonbranching S n)
    (hconn : StronglyFacetConnected S n)
    (hboundary : HasNonemptyBoundary S n)
    {c : SimplexFamily.Chain V} (hsupp : SupportedOn c S)
    (hboundaryEq : SimplexFamily.boundary c =
      SimplexFamily.boundary (sum S)) :
    c = sum S := by
  let d : SimplexFamily.Chain V := c + sum S
  have hdsupp : SupportedOn d S := by
    intro sigma hsigma
    simp [d, hsupp sigma hsigma, hsigma]
  have hdcycle : SimplexFamily.boundary d = 0 := by
    change SimplexFamily.boundaryHom d = 0
    rw [show d = c + sum S by rfl, map_add]
    change SimplexFamily.boundaryHom c =
      SimplexFamily.boundaryHom (sum S) at hboundaryEq
    rw [hboundaryEq]
    ext rho
    exact CharTwo.add_self_eq_zero
      ((SimplexFamily.boundaryHom (sum S)) rho)
  obtain ⟨rho, hrho, hcofaces⟩ := hboundary
  obtain ⟨sigma0, hfilterSingleton⟩ := Finset.card_eq_one.mp hcofaces
  have hsigma0 : sigma0 ∈ S.filter (fun sigma ↦ rho ⊆ sigma) := by
    rw [hfilterSingleton]
    simp
  have hd0 : d sigma0 = 0 := by
    have hcoeff := (Finsupp.ext_iff.mp hdcycle) rho
    rw [boundary_apply_of_supportedOn hpure hdsupp hrho,
      hfilterSingleton] at hcoeff
    simpa using hcoeff
  have hsigma0S : sigma0 ∈ S := by
    have := hsigma0
    simp only [Finset.mem_filter] at this
    exact this.1
  have hdall : ∀ sigma, sigma ∈ S → d sigma = 0 := by
    intro sigma hsigma
    have hpath := hconn sigma hsigma sigma0 hsigma0S
    exact (coeff_eq_of_connected_cycle hpure hnb hdsupp hdcycle hpath).trans hd0
  have hdzero : d = 0 := by
    ext sigma
    by_cases hsigma : sigma ∈ S
    · simpa using hdall sigma hsigma
    · exact hdsupp sigma hsigma
  have hcadd : c + sum S = 0 := by exact hdzero
  exact eq_neg_of_add_eq_zero_left hcadd |>.trans (by
    ext sigma
    exact ZMod.neg_eq_self_mod_two _)

end FacetChain

end BeyondSperner
