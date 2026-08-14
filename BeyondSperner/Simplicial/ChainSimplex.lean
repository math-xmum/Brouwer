import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.ZMod.Basic

/-!
# Finite simplex-families, pseudo-simplices, and chain-simplices

This file models Section 1.  We use a small native notion of finite abstract simplicial complex
because Ivanov includes the empty simplex (of dimension `-1`), whereas mathlib's current
`AbstractSimplicialComplex` stores only nonempty faces.

Dimension bounds are encoded by cardinalities: “dimension at most `|A|-1`” means that every
simplex has cardinality at most `|A|`.  Chains have coefficients in `ZMod 2`.
-/

namespace BeyondSperner

open Classical
open scoped BigOperators

/-- A finite abstract simplicial complex, including the empty simplex. -/
structure FiniteSimplicialComplex (V : Type*) [DecidableEq V] where
  simplices : Finset (Finset V)
  empty_mem : ∅ ∈ simplices
  downward_closed : ∀ ⦃σ τ : Finset V⦄, σ ∈ simplices → τ ⊆ σ → τ ∈ simplices

namespace FiniteSimplicialComplex

variable {V : Type*} [DecidableEq V]

instance : Membership (Finset V) (FiniteSimplicialComplex V) :=
  ⟨fun K σ ↦ σ ∈ K.simplices⟩

@[ext]
theorem ext {K L : FiniteSimplicialComplex V}
    (h : K.simplices = L.simplices) : K = L := by
  cases K
  cases L
  cases h
  rfl

/-- Relabel every vertex of a finite complex along an equivalence. -/
noncomputable def relabel {W : Type*} [DecidableEq W]
    (K : FiniteSimplicialComplex V) (e : V ≃ W) :
    FiniteSimplicialComplex W where
  simplices := K.simplices.image fun sigma ↦ sigma.image e
  empty_mem := by
    apply Finset.mem_image.mpr
    exact ⟨∅, K.empty_mem, by simp⟩
  downward_closed := by
    intro sigma tau hsigma htau
    obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp hsigma
    let eta : Finset V := tau.image e.symm
    have hetaSub : eta ⊆ rho := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      have hyImage : y ∈ rho.image e := htau hy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hyImage
      have : x = z := by
        rw [← hyx, ← hzy]
        simp
      simpa [this] using hz
    apply Finset.mem_image.mpr
    refine ⟨eta, K.downward_closed hrho hetaSub, ?_⟩
    ext y
    simp [eta]

theorem mem_relabel_iff {W : Type*} [DecidableEq W]
    (K : FiniteSimplicialComplex V) (e : V ≃ W) (tau : Finset W) :
    tau ∈ K.relabel e ↔
      ∃ sigma ∈ K, sigma.image e = tau := by
  change tau ∈ K.simplices.image (fun sigma ↦ sigma.image e) ↔ _
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨sigma, hsigma, heq⟩
    exact ⟨sigma, hsigma, heq⟩
  · rintro ⟨sigma, hsigma, heq⟩
    exact ⟨sigma, hsigma, heq⟩

/-- Relabeling by an equivalence and then by its inverse recovers the
original complex exactly. -/
theorem relabel_symm_relabel {W : Type*} [DecidableEq W]
    (K : FiniteSimplicialComplex V) (e : V ≃ W) :
    (K.relabel e).relabel e.symm = K := by
  apply ext
  ext sigma
  constructor
  · intro hsigma
    obtain ⟨tau, htau, htausigma⟩ :=
      (mem_relabel_iff (K.relabel e) e.symm sigma).1 hsigma
    obtain ⟨rho, hrho, hrhotau⟩ :=
      (mem_relabel_iff K e tau).1 htau
    have : rho = sigma := by
      rw [← htausigma, ← hrhotau]
      ext x
      simp
    change rho ∈ K.simplices at hrho
    simpa [this] using hrho
  · intro hsigma
    apply (mem_relabel_iff (K.relabel e) e.symm sigma).2
    refine ⟨sigma.image e, (mem_relabel_iff K e _).2
      ⟨sigma, hsigma, rfl⟩, ?_⟩
    ext x
    simp

/-- An isomorphism of finite abstract simplicial complexes.  The vertex
equivalence must carry the entire simplex finset to the target complex; this
is stronger than merely mapping vertices or top-dimensional simplices. -/
structure Iso {W : Type*} [DecidableEq W]
    (K : FiniteSimplicialComplex V)
    (L : FiniteSimplicialComplex W) where
  vertexEquiv : V ≃ W
  relabel_eq : K.relabel vertexEquiv = L

namespace Iso

variable {W : Type*} [DecidableEq W]
  {K : FiniteSimplicialComplex V} {L : FiniteSimplicialComplex W}

/-- A simplicial-complex isomorphism preserves and reflects membership of
every finite simplex. -/
theorem map_mem_iff (e : Iso K L) (sigma : Finset V) :
    sigma.image e.vertexEquiv ∈ L ↔ sigma ∈ K := by
  rcases e with ⟨e, rfl⟩
  constructor
  · intro hsigma
    obtain ⟨tau, htau, htauImage⟩ :=
      (mem_relabel_iff K e _).1 hsigma
    have hEq : tau = sigma := by
      apply Finset.image_injective e.injective
      exact htauImage
    simpa [hEq] using htau
  · intro hsigma
    exact (mem_relabel_iff K e _).2
      ⟨sigma, hsigma, rfl⟩

/-- Inverting the vertex equivalence inverts the simplicial-complex
isomorphism. -/
noncomputable def symm (e : Iso K L) : Iso L K where
  vertexEquiv := e.vertexEquiv.symm
  relabel_eq := by
    cases e with
    | mk vertexEquiv relabel_eq =>
        subst L
        exact relabel_symm_relabel K vertexEquiv

end Iso

/-- The induced subcomplex on the vertices satisfying `P`, with those
vertices bundled as a subtype. -/
noncomputable def inducedOn [Fintype V] (K : FiniteSimplicialComplex V)
    (P : V → Prop) : FiniteSimplicialComplex {v // P v} where
  simplices := Finset.univ.filter fun sigma ↦ sigma.image Subtype.val ∈ K
  empty_mem := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (∅ : Finset V) ∈ K.simplices
    exact K.empty_mem
  downward_closed := by
    intro sigma tau hsigma htau
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsigmaK := (Finset.mem_filter.mp hsigma).2
    apply K.downward_closed hsigmaK
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨y, htau hy, rfl⟩

theorem mem_inducedOn_iff [Fintype V] (K : FiniteSimplicialComplex V)
    (P : V → Prop) (sigma : Finset {v // P v}) :
    sigma ∈ K.inducedOn P ↔ sigma.image Subtype.val ∈ K := by
  change sigma ∈ Finset.univ.filter
      (fun tau ↦ tau.image Subtype.val ∈ K) ↔ _
  simp

@[simp]
theorem empty_mem' (K : FiniteSimplicialComplex V) : (∅ : Finset V) ∈ K := K.empty_mem

/-- Bridge between the bundled membership notation and the stored simplex finset. -/
theorem mem_simplices_iff (K : FiniteSimplicialComplex V) (σ : Finset V) :
    σ ∈ K.simplices ↔ σ ∈ K := by
  constructor
  · intro hσ
    exact K.downward_closed hσ Finset.Subset.rfl
  · intro hσ
    exact K.downward_closed hσ Finset.Subset.rfl

/-- The vertices actually occurring in the complex. -/
def vertexSet (K : FiniteSimplicialComplex V) : Set V :=
  {v | ({v} : Finset V) ∈ K}

/-- All simplices have cardinality at most `n`, and at least one has cardinality `n`. -/
def HasMaxCardinality (K : FiniteSimplicialComplex V) (n : ℕ) : Prop :=
  (∀ ⦃σ : Finset V⦄, σ ∈ K → σ.card ≤ n) ∧
    ∃ σ : Finset V, σ ∈ K ∧ σ.card = n

/-- Every simplex has cardinality at most `n`; a simplex of cardinality `n` need not exist. -/
def HasCardinalityAtMost (K : FiniteSimplicialComplex V) (n : ℕ) : Prop :=
  ∀ ⦃σ : Finset V⦄, σ ∈ K → σ.card ≤ n

/-- Every simplex is a face of a simplex of cardinality exactly `n`.
This is the finite-complex purity property needed when a lower-dimensional
face is extended to a top-dimensional simplex. -/
def IsPureOfCardinality (K : FiniteSimplicialComplex V) (n : ℕ) : Prop :=
  ∀ σ : Finset V, σ ∈ K →
    ∃ τ : Finset V, τ ∈ K ∧ σ ⊆ τ ∧ τ.card = n

/-- The top-dimensional simplices when the maximal cardinality is `n`. -/
def topSimplices (K : FiniteSimplicialComplex V) (n : ℕ) : Finset (Finset V) :=
  K.simplices.filter fun σ ↦ σ.card = n

/-- Relabeling carries the exact fixed-cardinality simplex set to its image. -/
theorem topSimplices_relabel {W : Type*} [DecidableEq W]
    (K : FiniteSimplicialComplex V) (e : V ≃ W) (n : ℕ) :
    (K.relabel e).topSimplices n =
      (K.topSimplices n).image (fun sigma ↦ sigma.image e) := by
  ext tau
  simp only [topSimplices, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨htau, htauCard⟩
    obtain ⟨sigma, hsigma, himage⟩ :=
      (mem_relabel_iff K e tau).1 htau
    refine ⟨sigma, ⟨hsigma, ?_⟩, himage⟩
    rw [← htauCard, ← himage,
      Finset.card_image_of_injective]
    exact e.injective
  · rintro ⟨sigma, ⟨hsigma, hsigmaCard⟩, rfl⟩
    constructor
    · exact (mem_relabel_iff K e _).2 ⟨sigma, hsigma, rfl⟩
    · rw [Finset.card_image_of_injective]
      · exact hsigmaCard
      · exact e.injective

/-- If every vertex of every simplex of `K` satisfies `P`, then bundling the
vertices by `P` and forgetting the certificates gives a bijection on the
fixed-cardinality simplices.  This is the finite-set statement which prevents
an induced face complex from losing or duplicating terms in its ambient
chain. -/
theorem topSimplices_inducedOn_image [Fintype V]
    (K : FiniteSimplicialComplex V) (P : V → Prop) (n : ℕ)
    (hP : ∀ sigma : Finset V, sigma ∈ K → ∀ v ∈ sigma, P v) :
    ((K.inducedOn P).topSimplices n).image
        (fun sigma ↦ sigma.image Subtype.val) =
      K.topSimplices n := by
  ext tau
  constructor
  · intro htau
    obtain ⟨sigma, hsigma, rfl⟩ := Finset.mem_image.mp htau
    have hsigmaData := Finset.mem_filter.mp hsigma
    apply Finset.mem_filter.mpr
    constructor
    · exact (mem_inducedOn_iff K P sigma).1 hsigmaData.1
    · rw [Finset.card_image_of_injective]
      · exact hsigmaData.2
      · exact Subtype.val_injective
  · intro htau
    have htauData := Finset.mem_filter.mp htau
    let sigma : Finset {v // P v} := tau.subtype P
    have himage : sigma.image Subtype.val = tau := by
      ext v
      simp only [sigma, Finset.mem_image, Finset.mem_subtype]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hv
        exact ⟨⟨v, hP tau
          ((mem_simplices_iff K tau).1 htauData.1) v hv⟩, hv, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨sigma, Finset.mem_filter.mpr ⟨?_, ?_⟩, himage⟩
    · apply (mem_inducedOn_iff K P sigma).2
      rw [himage]
      exact (mem_simplices_iff K tau).1 htauData.1
    · rw [← htauData.2, ← himage,
        Finset.card_image_of_injective]
      exact Subtype.val_injective

end FiniteSimplicialComplex

section Family

variable (I V : Type*) [DecidableEq I] [DecidableEq V]

/-- A simplex-family `A ↦ D(A)` based on `I`, with the universally valid
cardinality bound `|σ| ≤ |A|` for every `σ ∈ D(A)`.

Existence of a simplex with cardinality exactly `|A|` is deliberately not a
field: it is false for arbitrary indexed order families (for example, two
identical orders on a two-point set).  Statements that need a top simplex or
purity use `IsTopSimplex`, `HasMaxCardinality`, or `IsPureOfCardinality`
explicitly. -/
structure SimplexFamily where
  complex : Finset I → FiniteSimplicialComplex V
  dimension : ∀ A : Finset I, (complex A).HasCardinalityAtMost A.card

end Family

namespace SimplexFamily

variable {I V : Type*} [DecidableEq I] [DecidableEq V]

/-- The universal vertex set `V_D`, the union of the vertex sets of all `D(A)`. -/
def vertexSet (D : SimplexFamily I V) : Set V :=
  {v | ∃ A : Finset I, v ∈ (D.complex A).vertexSet}

/-- A vertex of the simplex-family, bundled with its membership proof. -/
abbrev Vertex (D : SimplexFamily I V) := D.vertexSet

/-- A top-dimensional (`d(A)`) simplex of `D(A)`. -/
def IsTopSimplex (D : SimplexFamily I V) (A : Finset I) (σ : Finset V) : Prop :=
  σ ∈ D.complex A ∧ σ.card = A.card

/-- An `e(A)`-simplex has cardinality `|A|-1`. -/
def HasCodimensionOneCardinality (A : Finset I) (σ : Finset V) : Prop :=
  σ.card + 1 = A.card

/-- The number `r_A(σ)` of top simplices of `D(A)` having `σ` as a face. -/
def cofaceCount (D : SimplexFamily I V) (A : Finset I) (σ : Finset V) : ℕ :=
  ((D.complex A).topSimplices A.card).filter (fun τ ↦ σ ⊆ τ) |>.card

/-- The codimension-one subsets of `A`. -/
def boundaryIndices (A : Finset I) : Finset (Finset I) :=
  A.powerset.filter fun B ↦ B.card + 1 = A.card

/-- The codimension-one subsets of a finite set are exactly the subsets
obtained by erasing one of its elements.  This is the combinatorial form of
the facet decomposition used by the boundary operator. -/
theorem boundaryIndices_eq_image_erase (A : Finset I) :
    boundaryIndices A = A.image (fun i ↦ A.erase i) := by
  ext B
  constructor
  · intro hB
    have hdata := Finset.mem_filter.mp hB
    have hsub := Finset.mem_powerset.mp hdata.1
    have hlt : B.card < A.card := by omega
    obtain ⟨i, hiA, hiB⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    apply Finset.mem_image.mpr
    refine ⟨i, hiA, ?_⟩
    have hsubErase : B ⊆ A.erase i := by
      intro x hx
      apply Finset.mem_erase.mpr
      refine ⟨?_, hsub hx⟩
      intro hxi
      subst x
      exact hiB hx
    symm
    apply Finset.eq_of_subset_of_card_le hsubErase
    rw [Finset.card_erase_of_mem hiA]
    omega
  · intro hB
    obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.mp hB
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.erase_subset i A), ?_⟩
    rw [Finset.card_erase_of_mem hiA]
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨i, hiA⟩
    omega

/-- The number `s_A(σ)` of boundary-index complexes `D(B)` containing `σ`. -/
noncomputable def boundaryMembershipCount (D : SimplexFamily I V) (A : Finset I)
    (σ : Finset V) : ℕ :=
  (boundaryIndices A).filter (fun B ↦ σ ∈ D.complex B) |>.card

/-- The codimension-one simplices to which the pseudo-simplex incidence axiom applies. -/
def IsRelevantCodimOne (D : SimplexFamily I V) (A : Finset I)
    (σ : Finset V) : Prop :=
  HasCodimensionOneCardinality A σ ∧
    (σ ∈ D.complex A ∨ ∃ B ∈ boundaryIndices A, σ ∈ D.complex B)

/-- Equation (1): `r_A(σ) + s_A(σ) = 2`. -/
def IsPseudoSimplex (D : SimplexFamily I V) : Prop :=
  ∀ (A : Finset I) (σ : Finset V), D.IsRelevantCodimOne A σ →
    D.cofaceCount A σ + D.boundaryMembershipCount A σ = 2

/-- A finite chain of abstract simplices with coefficients in `F₂`. -/
abbrev Chain (V : Type*) [DecidableEq V] := (Finset V) →₀ ZMod 2

/-- The basis chain supported on one simplex. -/
noncomputable def singletonChain (σ : Finset V) : Chain V := Finsupp.single σ 1

/-- The chain with coefficient one on every simplex of a fixed cardinality
in a finite complex. -/
noncomputable def complexCardChain (K : FiniteSimplicialComplex V)
    (n : ℕ) : Chain V :=
  ∑ sigma ∈ K.topSimplices n, singletonChain sigma

@[simp]
theorem complexCardChain_apply (K : FiniteSimplicialComplex V)
    (n : ℕ) (sigma : Finset V) :
    complexCardChain K n sigma =
      if sigma ∈ K ∧ sigma.card = n then 1 else 0 := by
  by_cases hsigmaK : sigma ∈ K
  · have hsigma : sigma ∈ K.simplices :=
      (FiniteSimplicialComplex.mem_simplices_iff K sigma).2 hsigmaK
    simp [complexCardChain, singletonChain, Finsupp.single_apply,
      FiniteSimplicialComplex.topSimplices, hsigma, hsigmaK]
  · have hsigma : sigma ∉ K.simplices := by
      intro h
      exact hsigmaK
        ((FiniteSimplicialComplex.mem_simplices_iff K sigma).1 h)
    simp [complexCardChain, singletonChain, Finsupp.single_apply,
      FiniteSimplicialComplex.topSimplices, hsigma, hsigmaK]

/-- Evaluation of a finite `F₂`-cochain on a chain. -/
noncomputable def cochainEval (φ : Finset V → ZMod 2) : Chain V →+ ZMod 2 :=
  Finsupp.liftAddHom fun σ ↦
    { toFun := fun a ↦ a * φ σ
      map_zero' := zero_mul _
      map_add' := fun a b ↦ add_mul a b (φ σ) }

@[simp]
theorem cochainEval_singleton (φ : Finset V → ZMod 2) (σ : Finset V) :
    cochainEval φ (singletonChain σ) = φ σ := by
  simp [cochainEval, singletonChain]

/-- Boundary of one abstract simplex, with coefficients in `F₂`. -/
noncomputable def boundarySimplex (σ : Finset V) : Chain V :=
  ∑ v ∈ σ, singletonChain (σ.erase v)

@[simp]
theorem cochainEval_boundarySimplex (φ : Finset V → ZMod 2) (σ : Finset V) :
    cochainEval φ (boundarySimplex σ) = ∑ v ∈ σ, φ (σ.erase v) := by
  simp [boundarySimplex]

/-- Boundary operator on finite `F₂`-chains, as an additive homomorphism. -/
noncomputable def boundaryHom : Chain V →+ Chain V :=
  Finsupp.liftAddHom fun σ ↦
    { toFun := fun a ↦ a • boundarySimplex σ
      map_zero' := zero_smul _ _
      map_add' := fun a b ↦ add_smul a b _ }

/-- Boundary operator on finite `F₂`-chains. -/
noncomputable def boundary (c : Chain V) : Chain V := boundaryHom c

@[simp]
theorem boundaryHom_singletonChain (σ : Finset V) :
    boundaryHom (singletonChain σ) = boundarySimplex σ := by
  simp [boundaryHom, singletonChain]

@[simp]
theorem boundary_singletonChain (σ : Finset V) :
    boundary (singletonChain σ) = boundarySimplex σ := by
  simp [boundary]

@[simp]
theorem boundary_zero : boundary (0 : Chain V) = 0 := by
  exact map_zero boundaryHom

@[simp]
theorem boundary_add (c d : Chain V) :
    boundary (c + d) = boundary c + boundary d := by
  exact map_add boundaryHom c d

/-- Relabel a chain by applying a vertex equivalence to every simplex in its
support.  This is the chain-level counterpart of
`FiniteSimplicialComplex.relabel`. -/
noncomputable def relabelChainHom {W : Type*} [DecidableEq W]
    (e : V ≃ W) : Chain V →+ Chain W :=
  Finsupp.mapDomain.addMonoidHom (fun sigma ↦ sigma.image e)

@[simp]
theorem relabelChainHom_singletonChain {W : Type*} [DecidableEq W]
    (e : V ≃ W) (sigma : Finset V) :
    relabelChainHom e (singletonChain sigma) =
      singletonChain (sigma.image e) := by
  simp [relabelChainHom, singletonChain]

/-- Relabeling a chain and then relabeling by the inverse equivalence loses
no coefficient. -/
theorem relabelChainHom_symm_relabel {W : Type*} [DecidableEq W]
    (e : V ≃ W) (c : Chain V) :
    relabelChainHom e.symm (relabelChainHom e c) = c := by
  change Finsupp.mapDomain (fun tau ↦ tau.image e.symm)
      (Finsupp.mapDomain (fun sigma ↦ sigma.image e) c) = c
  rw [← Finsupp.mapDomain_comp]
  have hcomp :
      (fun tau : Finset V ↦
        ((tau.image e).image e.symm)) = id := by
    funext tau
    ext v
    simp
  change Finsupp.mapDomain
      (fun tau : Finset V ↦ (tau.image e).image e.symm) c = c
  rw [hcomp, Finsupp.mapDomain_id]

/-- Relabeling commutes with taking the boundary of one simplex. -/
theorem relabelChainHom_boundarySimplex {W : Type*} [DecidableEq W]
    (e : V ≃ W) (sigma : Finset V) :
    relabelChainHom e (boundarySimplex sigma) =
      boundarySimplex (sigma.image e) := by
  rw [boundarySimplex, boundarySimplex]
  simp only [map_sum, relabelChainHom_singletonChain]
  rw [Finset.sum_image e.injective.injOn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.image_erase e.injective]

/-- Vertex relabeling is a chain map: the abstract `F₂` boundary operator is
independent of vertex names. -/
theorem relabelChainHom_boundary {W : Type*} [DecidableEq W]
    (e : V ≃ W) (c : Chain V) :
    relabelChainHom e (boundary c) =
      boundary (relabelChainHom e c) := by
  induction c using Finsupp.induction with
  | zero => simp [boundary, relabelChainHom]
  | single_add sigma a c hsigma ha ih =>
      have haOne : a = 1 := by
        apply ZMod.val_injective 2
        have hapos : 0 < a.val := by
          by_contra hnot
          have hzeroVal : a.val = 0 := by omega
          apply ha
          apply ZMod.val_injective 2
          simp [hzeroVal]
        have halt := ZMod.val_lt a
        have haval : a.val = 1 := by omega
        exact haval.trans (ZMod.val_one 2).symm
      subst a
      change relabelChainHom e
          (boundary (singletonChain sigma + c)) =
        boundary (relabelChainHom e (singletonChain sigma + c))
      simp only [boundary_add, map_add]
      rw [ih, boundary_singletonChain,
        relabelChainHom_boundarySimplex,
        relabelChainHom_singletonChain, boundary_singletonChain]

/-- Push a chain forward along an injective vertex map.  Unlike
`relabelChainHom`, this permits a face subtype to be embedded into a larger
ambient vertex type, which is exactly the chain map needed in formula (21). -/
noncomputable def mapChainHom {W : Type*} [DecidableEq W]
    (f : V ↪ W) : Chain V →+ Chain W :=
  Finsupp.mapDomain.addMonoidHom (fun sigma ↦ sigma.image f)

@[simp]
theorem mapChainHom_singletonChain {W : Type*} [DecidableEq W]
    (f : V ↪ W) (sigma : Finset V) :
    mapChainHom f (singletonChain sigma) =
      singletonChain (sigma.image f) := by
  simp [mapChainHom, singletonChain]

/-- Evaluation of an injective chain pushforward on the image of a simplex
recovers the original coefficient exactly. -/
@[simp]
theorem mapChainHom_apply_image {W : Type*} [DecidableEq W]
    (f : V ↪ W) (c : Chain V) (sigma : Finset V) :
    mapChainHom f c (sigma.image f) = c sigma := by
  exact Finsupp.mapDomain_apply
    (Finset.image_injective f.injective) c sigma

/-- A pushed-forward chain has coefficient zero on every ambient simplex
which is not the image of a source simplex. -/
theorem mapChainHom_apply_eq_zero_of_not_exists
    {W : Type*} [DecidableEq W]
    (f : V ↪ W) (c : Chain V) (tau : Finset W)
    (h : ¬∃ sigma : Finset V, sigma.image f = tau) :
    mapChainHom f c tau = 0 := by
  apply Finsupp.mapDomain_of_notMem_range c tau
  rintro ⟨sigma, hsigma⟩
  exact h ⟨sigma, hsigma⟩

/-- An injective vertex map commutes with the boundary of one simplex. -/
theorem mapChainHom_boundarySimplex {W : Type*} [DecidableEq W]
    (f : V ↪ W) (sigma : Finset V) :
    mapChainHom f (boundarySimplex sigma) =
      boundarySimplex (sigma.image f) := by
  rw [boundarySimplex, boundarySimplex]
  simp only [map_sum, mapChainHom_singletonChain]
  rw [Finset.sum_image f.injective.injOn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.image_erase f.injective]

/-- Pushforward along a vertex embedding is a chain map. -/
theorem mapChainHom_boundary {W : Type*} [DecidableEq W]
    (f : V ↪ W) (c : Chain V) :
    mapChainHom f (boundary c) = boundary (mapChainHom f c) := by
  induction c using Finsupp.induction with
  | zero => simp [boundary, mapChainHom]
  | single_add sigma a c hsigma ha ih =>
      have haOne : a = 1 := by
        apply ZMod.val_injective 2
        have hapos : 0 < a.val := by
          by_contra hnot
          have hzeroVal : a.val = 0 := by omega
          apply ha
          apply ZMod.val_injective 2
          simp [hzeroVal]
        have halt := ZMod.val_lt a
        have haval : a.val = 1 := by omega
        exact haval.trans (ZMod.val_one 2).symm
      subst a
      change mapChainHom f
          (boundary (singletonChain sigma + c)) =
        boundary (mapChainHom f (singletonChain sigma + c))
      simp only [boundary_add, map_add]
      rw [ih, boundary_singletonChain,
        mapChainHom_boundarySimplex,
        mapChainHom_singletonChain, boundary_singletonChain]

/-- Pushforwards compose exactly. -/
theorem mapChainHom_comp {U W : Type*}
    [DecidableEq U] [DecidableEq W]
    (f : V ↪ U) (g : U ↪ W) (c : Chain V) :
    mapChainHom g (mapChainHom f c) =
      mapChainHom (f.trans g) c := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add sigma a c hsigma ha ih =>
      have haOne : a = 1 := by
        apply ZMod.val_injective 2
        have hapos : 0 < a.val := by
          by_contra hnot
          have hzeroVal : a.val = 0 := by omega
          apply ha
          apply ZMod.val_injective 2
          simp [hzeroVal]
        have halt := ZMod.val_lt a
        have haval : a.val = 1 := by omega
        exact haval.trans (ZMod.val_one 2).symm
      subst a
      simp only [map_add, ih]
      congr 1
      change mapChainHom g (mapChainHom f (singletonChain sigma)) =
        mapChainHom (f.trans g) (singletonChain sigma)
      simp only [mapChainHom_singletonChain]
      congr 1
      ext w
      simp

/-- An equivalence viewed as an embedding gives the same chain map as
relabeling. -/
theorem mapChainHom_equiv_toEmbedding {W : Type*} [DecidableEq W]
    (e : V ≃ W) (c : Chain V) :
    mapChainHom e.toEmbedding c = relabelChainHom e c := rfl

/-- Fixed-cardinality chains are natural under vertex relabeling. -/
theorem relabelChainHom_complexCardChain
    {W : Type*} [DecidableEq W]
    (e : V ≃ W) (K : FiniteSimplicialComplex V) (n : ℕ) :
    relabelChainHom e (complexCardChain K n) =
      complexCardChain (K.relabel e) n := by
  rw [complexCardChain, complexCardChain,
    FiniteSimplicialComplex.topSimplices_relabel]
  simp only [map_sum, relabelChainHom_singletonChain]
  rw [Finset.sum_image]
  exact (Finset.image_injective e.injective).injOn

/-- When a complex already lies entirely in a predicate-defined vertex
subtype, its fixed-cardinality chain pushes forward to the original ambient
chain.  The hypothesis quantifies over every simplex, so the statement does
not silently assume that `inducedOn` is surjective. -/
theorem mapChainHom_complexCardChain_inducedOn [Fintype V]
    (K : FiniteSimplicialComplex V) (P : V → Prop) (n : ℕ)
    (hP : ∀ sigma : Finset V, sigma ∈ K → ∀ v ∈ sigma, P v) :
    mapChainHom (Function.Embedding.subtype P)
        (complexCardChain (K.inducedOn P) n) =
      complexCardChain K n := by
  rw [complexCardChain, complexCardChain]
  simp only [map_sum, mapChainHom_singletonChain]
  change (∑ sigma ∈ (K.inducedOn P).topSimplices n,
      singletonChain (sigma.image Subtype.val)) = _
  rw [← Finset.sum_image
    ((Finset.image_injective Subtype.val_injective).injOn),
    FiniteSimplicialComplex.topSimplices_inducedOn_image K P n hP]

private theorem card_filter_erase_eq (σ τ : Finset V) :
    (τ.filter fun v ↦ τ.erase v = σ).card =
      if σ ⊆ τ ∧ σ.card + 1 = τ.card then 1 else 0 := by
  by_cases h : σ ⊆ τ ∧ σ.card + 1 = τ.card
  · rw [if_pos h]
    obtain ⟨v, hvσ, hvinsert⟩ := Finset.exists_eq_insert_iff.mpr h
    have hvτ : v ∈ τ := by rw [← hvinsert]; simp
    have herase : τ.erase v = σ := by
      rw [← hvinsert]
      simp [hvσ]
    have hfilter : τ.filter (fun u ↦ τ.erase u = σ) = {v} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨huτ, hu⟩
        exact (Finset.erase_inj τ huτ).mp (hu.trans herase.symm)
      · rintro rfl
        exact ⟨hvτ, herase⟩
    rw [hfilter]
    simp
  · rw [if_neg h]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hv' := Finset.mem_filter.mp hv
    apply h
    constructor
    · rw [← hv'.2]
      exact Finset.erase_subset v τ
    · have hcard := Finset.card_erase_add_one hv'.1
      rw [hv'.2] at hcard
      exact hcard

@[simp]
theorem boundarySimplex_apply (τ σ : Finset V) :
    boundarySimplex τ σ =
      if σ ⊆ τ ∧ σ.card + 1 = τ.card then 1 else 0 := by
  calc
    boundarySimplex τ σ =
        ∑ v ∈ τ, if τ.erase v = σ then (1 : ZMod 2) else 0 := by
      simp [boundarySimplex, singletonChain, Finsupp.single_apply]
    _ = ((τ.filter fun v ↦ τ.erase v = σ).card : ZMod 2) := by
      rw [Finset.sum_boole]
    _ = if σ ⊆ τ ∧ σ.card + 1 = τ.card then 1 else 0 := by
      rw [card_filter_erase_eq]
      split <;> simp

/-- The chain `D[[A]]`, the sum of all `d(A)`-simplices of `D(A)`. -/
noncomputable def topChain (D : SimplexFamily I V) (A : Finset I) : Chain V :=
  ∑ σ ∈ (D.complex A).topSimplices A.card, singletonChain σ

omit [DecidableEq I] in
/-- `topChain` is exactly the fixed-cardinality chain of the selected
complex; this lemma exposes the definitional identification used when a
family face is compared with an induced subcomplex. -/
theorem topChain_eq_complexCardChain (D : SimplexFamily I V)
    (A : Finset I) :
    D.topChain A = complexCardChain (D.complex A) A.card := rfl

omit [DecidableEq I] in @[simp]
theorem cochainEval_topChain (φ : Finset V → ZMod 2)
    (D : SimplexFamily I V) (A : Finset I) :
    cochainEval φ (D.topChain A) =
      ∑ σ ∈ (D.complex A).topSimplices A.card, φ σ := by
  simp [topChain]

omit [DecidableEq I] in @[simp]
theorem cochainEval_boundary_topChain (φ : Finset V → ZMod 2)
    (D : SimplexFamily I V) (A : Finset I) :
    cochainEval φ (boundary (D.topChain A)) =
      ∑ σ ∈ (D.complex A).topSimplices A.card,
        ∑ v ∈ σ, φ (σ.erase v) := by
  simp [boundary, topChain]

omit [DecidableEq I] in @[simp]
theorem topChain_apply (D : SimplexFamily I V) (A : Finset I) (σ : Finset V) :
    D.topChain A σ =
      if σ ∈ (D.complex A).simplices ∧ σ.card = A.card then 1 else 0 := by
  simp [topChain, singletonChain, Finsupp.single_apply,
    FiniteSimplicialComplex.topSimplices]

/-- The right-hand side of equation (2). -/
noncomputable def boundaryIndexChain (D : SimplexFamily I V) (A : Finset I) : Chain V :=
  ∑ B ∈ boundaryIndices A, D.topChain B

omit [DecidableEq I] in @[simp]
theorem cochainEval_boundaryIndexChain (φ : Finset V → ZMod 2)
    (D : SimplexFamily I V) (A : Finset I) :
    cochainEval φ (D.boundaryIndexChain A) =
      ∑ B ∈ boundaryIndices A,
        ∑ σ ∈ (D.complex B).topSimplices B.card, φ σ := by
  simp [boundaryIndexChain]

omit [DecidableEq I] in private theorem boundary_topChain_apply_of_card (D : SimplexFamily I V)
    (A : Finset I) (σ : Finset V) (hcard : σ.card + 1 = A.card) :
    boundary (D.topChain A) σ = (D.cofaceCount A σ : ZMod 2) := by
  simp [boundary, topChain, boundaryHom, boundarySimplex_apply, hcard, cofaceCount,
    FiniteSimplicialComplex.topSimplices, singletonChain]
  congr 1
  congr 1
  ext τ
  simp
  aesop

omit [DecidableEq I] in private theorem boundaryIndexChain_apply_of_card (D : SimplexFamily I V)
    (A : Finset I) (σ : Finset V) (hcard : σ.card + 1 = A.card) :
    D.boundaryIndexChain A σ = (D.boundaryMembershipCount A σ : ZMod 2) := by
  simp [boundaryIndexChain, topChain_apply, boundaryMembershipCount, boundaryIndices]
  congr 1
  congr 1
  ext B
  simp [FiniteSimplicialComplex.mem_simplices_iff]
  omega

omit [DecidableEq I] in private theorem boundary_topChain_apply_of_not_card (D : SimplexFamily I V)
    (A : Finset I) (σ : Finset V) (hcard : σ.card + 1 ≠ A.card) :
    boundary (D.topChain A) σ = 0 := by
  simp [boundary, topChain, boundaryHom, boundarySimplex_apply,
    FiniteSimplicialComplex.topSimplices, singletonChain]
  have hempty : ((D.complex A).simplices.filter (fun τ ↦ τ.card = A.card)).filter
      (fun τ ↦ σ ⊆ τ ∧ σ.card + 1 = τ.card) = ∅ := by
    ext τ
    simp
    omega
  rw [hempty]
  simp

omit [DecidableEq I] in private theorem boundaryIndexChain_apply_of_not_card (D : SimplexFamily I V)
    (A : Finset I) (σ : Finset V) (hcard : σ.card + 1 ≠ A.card) :
    D.boundaryIndexChain A σ = 0 := by
  simp [boundaryIndexChain, topChain_apply, boundaryIndices]
  have hempty : (A.powerset.filter (fun B ↦ B.card + 1 = A.card)).filter
      (fun B ↦ σ ∈ (D.complex B).simplices ∧ σ.card = B.card) = ∅ := by
    ext B
    simp
    omega
  rw [hempty]
  simp

/-- Equation (2), for every `A ⊆ I`. -/
def IsChainSimplex (D : SimplexFamily I V) : Prop :=
  ∀ A : Finset I, boundary (D.topChain A) = D.boundaryIndexChain A

omit [DecidableEq I] in
/-- The chain-simplex equation is equivalent to equality, modulo two, of the two
incidence counts at every codimension-one simplex. -/
theorem isChainSimplex_iff_incidenceParity (D : SimplexFamily I V) :
    D.IsChainSimplex ↔
      ∀ (A : Finset I) (σ : Finset V), σ.card + 1 = A.card →
        (D.cofaceCount A σ : ZMod 2) =
          (D.boundaryMembershipCount A σ : ZMod 2) := by
  constructor
  · intro hD A σ hcard
    have hcoeff : boundary (D.topChain A) σ = D.boundaryIndexChain A σ := by
      rw [hD A]
    simpa [boundary_topChain_apply_of_card D A σ hcard,
      boundaryIndexChain_apply_of_card D A σ hcard] using hcoeff
  · intro hD A
    ext σ
    by_cases hcard : σ.card + 1 = A.card
    · rw [boundary_topChain_apply_of_card D A σ hcard,
        boundaryIndexChain_apply_of_card D A σ hcard]
      exact hD A σ hcard
    · rw [boundary_topChain_apply_of_not_card D A σ hcard,
        boundaryIndexChain_apply_of_not_card D A σ hcard]

omit [DecidableEq I] in
/-- Theorem 1.2: every pseudo-simplex is a chain-simplex. -/
theorem IsPseudoSimplex.isChainSimplex {D : SimplexFamily I V}
    (hD : D.IsPseudoSimplex) : D.IsChainSimplex := by
  intro A
  ext σ
  by_cases hcard : σ.card + 1 = A.card
  · rw [boundary_topChain_apply_of_card D A σ hcard,
      boundaryIndexChain_apply_of_card D A σ hcard]
    by_cases hrel : D.IsRelevantCodimOne A σ
    · have hcount := congrArg (fun n : ℕ ↦ (n : ZMod 2)) (hD A σ hrel)
      have hsum : (D.cofaceCount A σ : ZMod 2) +
          (D.boundaryMembershipCount A σ : ZMod 2) = 0 := by
        simpa only [Nat.cast_add, ZMod.natCast_self] using hcount
      calc
        (D.cofaceCount A σ : ZMod 2) =
            -(D.boundaryMembershipCount A σ : ZMod 2) :=
          eq_neg_of_add_eq_zero_left hsum
        _ = (D.boundaryMembershipCount A σ : ZMod 2) :=
          ZMod.neg_eq_self_mod_two _
    · have hr : D.cofaceCount A σ = 0 := by
        unfold cofaceCount
        rw [Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro τ hτ
        have hτ' := Finset.mem_filter.mp hτ
        have htop : τ ∈ (D.complex A).simplices ∧ τ.card = A.card := by
          simpa [FiniteSimplicialComplex.topSimplices] using hτ'.1
        apply hrel
        refine ⟨hcard, Or.inl ?_⟩
        exact (FiniteSimplicialComplex.mem_simplices_iff (D.complex A) σ).mp
          ((D.complex A).downward_closed htop.1 hτ'.2)
      have hs : D.boundaryMembershipCount A σ = 0 := by
        unfold boundaryMembershipCount
        rw [Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro B hB
        have hB' := Finset.mem_filter.mp hB
        exact hrel ⟨hcard, Or.inr ⟨B, hB'.1, hB'.2⟩⟩
      simp [hr, hs]
  · rw [boundary_topChain_apply_of_not_card D A σ hcard,
      boundaryIndexChain_apply_of_not_card D A σ hcard]

end SimplexFamily

namespace Envelope

variable {I V : Type*} [Fintype I] [Fintype V] [Nonempty I]
  [DecidableEq I] [DecidableEq V]

/-- Embed an old simplex into the disjoint union `V_D ⊕ I`. -/
def oldSimplex (σ : Finset V) : Finset (V ⊕ I) := σ.image Sum.inl

/-- Embed a formal basis face into the disjoint union `V_D ⊕ I`. -/
def indexSimplex (K : Finset I) : Finset (V ⊕ I) := K.image Sum.inr

/-- The old vertices of a finite subset of `V ⊕ I`. -/
def oldPart (ρ : Finset (V ⊕ I)) : Finset V :=
  Finset.univ.filter fun v ↦ Sum.inl v ∈ ρ

/-- The formal index vertices of a finite subset of `V ⊕ I`. -/
def indexPart (ρ : Finset (V ⊕ I)) : Finset I :=
  Finset.univ.filter fun i ↦ Sum.inr i ∈ ρ

/-- Every finite subset of the disjoint union splits into its old and formal parts. -/
theorem old_index_decomposition (ρ : Finset (V ⊕ I)) :
    ρ = oldSimplex (oldPart ρ) ∪ indexSimplex (indexPart ρ) := by
  ext z
  cases z <;> simp [oldPart, indexPart, oldSimplex, indexSimplex]

omit [Fintype I] in @[simp]
theorem oldPart_oldSimplex_union_indexSimplex (σ : Finset V) (K : Finset I) :
    oldPart (oldSimplex σ ∪ indexSimplex K) = σ := by
  ext v
  simp [oldPart, oldSimplex, indexSimplex]

omit [Fintype V] [Nonempty I] in @[simp]
theorem indexPart_oldSimplex_union_indexSimplex (σ : Finset V) (K : Finset I) :
    indexPart (oldSimplex σ ∪ indexSimplex K) = K := by
  ext i
  simp [indexPart, oldSimplex, indexSimplex]

omit [Fintype I] in @[simp]
theorem oldPart_indexSimplex (K : Finset I) :
    oldPart (V := V) (indexSimplex K) = ∅ := by
  ext v
  simp [oldPart, indexSimplex]

omit [Fintype V] [Nonempty I] in @[simp]
theorem indexPart_indexSimplex (K : Finset I) :
    indexPart (V := V) (indexSimplex K) = K := by
  ext i
  simp [indexPart, indexSimplex]

theorem oldSimplex_union_indexSimplex_injective :
    Function.Injective (fun p : Finset V × Finset I ↦ oldSimplex p.1 ∪ indexSimplex p.2) := by
  rintro ⟨σ, K⟩ ⟨τ, L⟩ h
  have hold := congrArg oldPart h
  have hindex := congrArg indexPart h
  simp only [oldPart_oldSimplex_union_indexSimplex] at hold
  simp only [indexPart_oldSimplex_union_indexSimplex] at hindex
  exact Prod.ext hold hindex

omit [Fintype I] [Fintype V] [Nonempty I] in theorem oldSimplex_injective :
    Function.Injective (oldSimplex (I := I) : Finset V → Finset (V ⊕ I)) := by
  intro σ τ h
  unfold oldSimplex at h
  exact Finset.image_injective Sum.inl_injective h

omit [Fintype I] [Fintype V] [Nonempty I] in theorem indexSimplex_injective :
    Function.Injective (indexSimplex (V := V) : Finset I → Finset (V ⊕ I)) := by
  intro K L h
  unfold indexSimplex at h
  exact Finset.image_injective Sum.inr_injective h

omit [Fintype I] [Fintype V] [Nonempty I] in @[simp]
theorem indexSimplex_subset_iff (K L : Finset I) :
    indexSimplex (V := V) K ⊆ indexSimplex L ↔ K ⊆ L := by
  constructor
  · intro h i hi
    have himage : Sum.inr i ∈ indexSimplex (V := V) K := by
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (h himage)
    exact Sum.inr_injective hji ▸ hj
  · intro h z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨i, h hi, rfl⟩

omit [Fintype I] [Fintype V] [Nonempty I] in theorem disjoint_oldSimplex_indexSimplex (σ : Finset V) (K : Finset I) :
    Disjoint (oldSimplex σ) (indexSimplex K) := by
  rw [Finset.disjoint_left]
  intro z hzold hzindex
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hzold
  obtain ⟨i, _, hEq⟩ := Finset.mem_image.mp hzindex
  exact Sum.inr_ne_inl hEq

omit [Fintype I] [Fintype V] [Nonempty I] in @[simp]
theorem card_oldSimplex (σ : Finset V) : (oldSimplex (I := I) σ).card = σ.card :=
  Finset.card_image_of_injective σ Sum.inl_injective

omit [Fintype I] [Fintype V] [Nonempty I] in @[simp]
theorem card_indexSimplex (K : Finset I) : (indexSimplex (V := V) K).card = K.card :=
  Finset.card_image_of_injective K Sum.inr_injective

omit [Fintype I] [Fintype V] [Nonempty I] in @[simp]
theorem card_oldSimplex_union_indexSimplex (σ : Finset V) (K : Finset I) :
    (oldSimplex σ ∪ indexSimplex K).card = σ.card + K.card := by
  rw [Finset.card_union_of_disjoint (disjoint_oldSimplex_indexSimplex σ K),
    card_oldSimplex (I := I), card_indexSimplex (V := V)]

theorem card_oldPart_add_card_indexPart (ρ : Finset (V ⊕ I)) :
    (oldPart ρ).card + (indexPart ρ).card = ρ.card := by
  conv_rhs => rw [old_index_decomposition ρ]
  exact (card_oldSimplex_union_indexSimplex (oldPart ρ) (indexPart ρ)).symm

omit [Nonempty I] in theorem card_complement_add_card (K : Finset I) :
    (Finset.univ \ K).card + K.card = Fintype.card I := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  exact Nat.sub_add_cancel (Finset.card_le_univ K)

theorem codim_card_complement (ρ : Finset (V ⊕ I))
    (hcard : ρ.card + 1 = Fintype.card I) :
    (oldPart ρ).card + 1 = (Finset.univ \ indexPart ρ).card := by
  have hsplit := card_oldPart_add_card_indexPart ρ
  have hcomp := card_complement_add_card (indexPart ρ)
  omega

/--
The simplex predicate defining the envelope.  On a proper index set `A`, `E(A)=Δ(A)`.  At
`A=I`, its simplices are exactly `σ ∗ K` with `σ ∈ D(C)`, `K ⊆ I\C`, and `K` proper in `I`.
-/
def IsSimplex (D : SimplexFamily I V) (A : Finset I) (ρ : Finset (V ⊕ I)) : Prop :=
  if A = Finset.univ then
    ∃ (C : Finset I) (σ : Finset V) (K : Finset I),
      σ ∈ D.complex C ∧ K ⊆ Finset.univ \ C ∧ K ≠ Finset.univ ∧
        ρ = oldSimplex σ ∪ indexSimplex K
  else
    ∃ K : Finset I, K ⊆ A ∧ ρ = indexSimplex K

/-- The finite complex `E(A)` of the envelope. -/
noncomputable def complex (D : SimplexFamily I V) (A : Finset I) :
    FiniteSimplicialComplex (V ⊕ I) where
  simplices := Finset.univ.filter fun ρ ↦ IsSimplex D A ρ
  empty_mem := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hA : A = Finset.univ
    · rw [IsSimplex, if_pos hA]
      refine ⟨∅, ∅, ∅, (D.complex ∅).empty_mem, by simp, ?_, by simp [oldSimplex,
        indexSimplex]⟩
      exact Finset.univ_nonempty.ne_empty.symm
    · rw [IsSimplex, if_neg hA]
      exact ⟨∅, by simp, by simp [indexSimplex]⟩
  downward_closed := by
    intro ρ ρ' hρ hsub
    have hρsimp : IsSimplex D A ρ := (Finset.mem_filter.mp hρ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hA : A = Finset.univ
    · rw [IsSimplex, if_pos hA] at hρsimp ⊢
      obtain ⟨C, σ, K, hσ, hKC, hKproper, rfl⟩ := hρsimp
      let σ' := oldPart ρ'
      let K' := indexPart ρ'
      have hσ'sub : σ' ⊆ σ := by
        intro v hv
        have hv' : Sum.inl v ∈ ρ' := by simpa [σ', oldPart] using hv
        have := hsub hv'
        simpa [oldSimplex, indexSimplex] using this
      have hK'sub : K' ⊆ K := by
        intro i hi
        have hi' : Sum.inr i ∈ ρ' := by simpa [K', indexPart] using hi
        have := hsub hi'
        simpa [oldSimplex, indexSimplex] using this
      refine ⟨C, σ', K',
        (D.complex C).downward_closed hσ hσ'sub, hK'sub.trans hKC, ?_, ?_⟩
      · intro hK'univ
        apply hKproper
        apply Finset.Subset.antisymm (Finset.subset_univ K)
        intro i _
        apply hK'sub
        simp [hK'univ]
      · exact old_index_decomposition ρ'
    · rw [IsSimplex, if_neg hA] at hρsimp ⊢
      obtain ⟨K, hKA, rfl⟩ := hρsimp
      let K' := indexPart ρ'
      have hK'sub : K' ⊆ K := by
        intro i hi
        have hi' : Sum.inr i ∈ ρ' := by simpa [K', indexPart] using hi
        have := hsub hi'
        simpa [indexSimplex] using this
      refine ⟨K', hK'sub.trans hKA, ?_⟩
      have hdecomp := old_index_decomposition ρ'
      have holdEmpty : oldPart ρ' = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hv' : Sum.inl v ∈ ρ' := by simpa [oldPart] using hv
        have := hsub hv'
        simp [indexSimplex] at this
      simpa [holdEmpty, oldSimplex, K'] using hdecomp

@[simp]
theorem mem_complex_iff (D : SimplexFamily I V) (A : Finset I) (ρ : Finset (V ⊕ I)) :
    ρ ∈ complex D A ↔ IsSimplex D A ρ := by
  constructor
  · intro hρ
    have hraw : ρ ∈ (complex D A).simplices :=
      (FiniteSimplicialComplex.mem_simplices_iff (complex D A) ρ).mpr hρ
    exact (Finset.mem_filter.mp hraw).2
  · intro hρ
    apply (FiniteSimplicialComplex.mem_simplices_iff (complex D A) ρ).mp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρ⟩

theorem isTopSimplex_of_ne_univ (D : SimplexFamily I V) {A : Finset I}
    (hA : A ≠ Finset.univ) (ρ : Finset (V ⊕ I)) :
    (ρ ∈ complex D A ∧ ρ.card = A.card) ↔ ρ = indexSimplex A := by
  constructor
  · rintro ⟨hρ, hcard⟩
    have hsimp : IsSimplex D A ρ := (mem_complex_iff D A ρ).mp hρ
    rw [IsSimplex, if_neg hA] at hsimp
    obtain ⟨K, hKA, rfl⟩ := hsimp
    rw [card_indexSimplex] at hcard
    have hKAeq : K = A := Finset.eq_of_subset_of_card_le hKA (by omega)
    rw [hKAeq]
  · rintro rfl
    refine ⟨(mem_complex_iff D A (indexSimplex A)).mpr ?_, card_indexSimplex A⟩
    rw [IsSimplex, if_neg hA]
    exact ⟨A, Finset.Subset.rfl, rfl⟩

theorem topSimplices_of_ne_univ (D : SimplexFamily I V) {A : Finset I}
    (hA : A ≠ Finset.univ) :
    (complex D A).topSimplices A.card = {indexSimplex A} := by
  ext τ
  simp only [FiniteSimplicialComplex.topSimplices, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hτ, hτcard⟩
    apply (isTopSimplex_of_ne_univ D hA τ).mp
    exact ⟨(FiniteSimplicialComplex.mem_simplices_iff (complex D A) τ).mp hτ, hτcard⟩
  · intro hτ
    have htop := (isTopSimplex_of_ne_univ D hA τ).mpr hτ
    exact ⟨(FiniteSimplicialComplex.mem_simplices_iff (complex D A) τ).mpr htop.1,
      htop.2⟩

theorem isTopSimplex_univ_iff (D : SimplexFamily I V) (ρ : Finset (V ⊕ I)) :
    (ρ ∈ complex D Finset.univ ∧ ρ.card = (Finset.univ : Finset I).card) ↔
      ∃ C : Finset I, C.Nonempty ∧ D.IsTopSimplex C (oldPart ρ) ∧
        indexPart ρ = Finset.univ \ C := by
  constructor
  · rintro ⟨hρ, hcard⟩
    have hsimp : IsSimplex D Finset.univ ρ :=
      (mem_complex_iff D Finset.univ ρ).mp hρ
    rw [IsSimplex, if_pos rfl] at hsimp
    obtain ⟨C, σ, K, hσ, hKC, hKproper, rfl⟩ := hsimp
    rw [card_oldSimplex_union_indexSimplex, Finset.card_univ] at hcard
    have hσle : σ.card ≤ C.card := D.dimension C hσ
    have hKle : K.card ≤ (Finset.univ \ C).card := Finset.card_le_card hKC
    have hcomp := card_complement_add_card C
    have hσcard : σ.card = C.card := by omega
    have hKcard : K.card = (Finset.univ \ C).card := by omega
    have hKeq : K = Finset.univ \ C :=
      Finset.eq_of_subset_of_card_le hKC (by omega)
    have hC : C.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hCempty
      subst C
      apply hKproper
      simpa using hKeq
    refine ⟨C, hC, ?_, ?_⟩
    · exact ⟨by simpa using hσ, by simpa using hσcard⟩
    · simpa using hKeq
  · rintro ⟨C, hC, ⟨hρ, hρcard⟩, hindex⟩
    constructor
    · apply (mem_complex_iff D Finset.univ ρ).mpr
      rw [IsSimplex, if_pos rfl]
      refine ⟨C, oldPart ρ, indexPart ρ, hρ, ?_, ?_, old_index_decomposition ρ⟩
      · simp [hindex]
      · intro hindexUniv
        have hcomp := card_complement_add_card C
        have hcompcard : (Finset.univ \ C).card = Fintype.card I := by
          simpa using congrArg Finset.card (hindex.symm.trans hindexUniv)
        have hCcard : C.card = 0 := by
          omega
        exact (Finset.card_ne_zero.mpr hC) hCcard
    · have hsplit := card_oldPart_add_card_indexPart ρ
      have hcomp := card_complement_add_card C
      rw [hindex, hρcard] at hsplit
      rw [Finset.card_univ]
      omega

/-- The envelope simplex-family. -/
noncomputable def family (D : SimplexFamily I V) : SimplexFamily I (V ⊕ I) where
  complex := complex D
  dimension := by
    intro A ρ hρ
    have hρsimp : IsSimplex D A ρ := (Finset.mem_filter.mp hρ).2
    by_cases hA : A = Finset.univ
    · rw [IsSimplex, if_pos hA] at hρsimp
      obtain ⟨C, σ, K, hσ, hKC, _, rfl⟩ := hρsimp
      rw [card_oldSimplex_union_indexSimplex, hA]
      calc
        σ.card + K.card ≤ C.card + (Finset.univ \ C).card :=
          Nat.add_le_add (D.dimension C hσ) (Finset.card_le_card hKC)
        _ = Finset.univ.card := by
          rw [Finset.card_sdiff, Finset.inter_univ]
          exact Nat.add_sub_of_le (Finset.card_le_univ C)
    · rw [IsSimplex, if_neg hA] at hρsimp
      obtain ⟨K, hKA, rfl⟩ := hρsimp
      rw [card_indexSimplex (V := V)]
      exact Finset.card_le_card hKA

/-- On a proper index face, the envelope has exactly one top simplex, so its
top chain is the basis chain of the formal index simplex. -/
theorem topChain_eq_singleton_indexSimplex_of_ne_univ
    (D : SimplexFamily I V) {A : Finset I} (hA : A ≠ Finset.univ) :
    (family D).topChain A =
      SimplexFamily.singletonChain (indexSimplex (V := V) A) := by
  rw [SimplexFamily.topChain, show (family D).complex A = complex D A from rfl,
    topSimplices_of_ne_univ D hA]
  simp

/-- The boundary-index chain of the full envelope is literally the boundary
of its formal reference simplex.  Together with `chain_family`, this gives
the paper's identity `∂ E[[I]] = ∂ I`. -/
theorem boundaryIndexChain_univ_eq_boundary_indexSimplex
    (D : SimplexFamily I V) :
    (family D).boundaryIndexChain Finset.univ =
      SimplexFamily.boundary
        (SimplexFamily.singletonChain
          (indexSimplex (V := V) Finset.univ)) := by
  rw [SimplexFamily.boundaryIndexChain,
    SimplexFamily.boundaryIndices_eq_image_erase]
  rw [Finset.sum_image]
  · rw [SimplexFamily.boundary_singletonChain, SimplexFamily.boundarySimplex]
    rw [indexSimplex]
    rw [Finset.sum_image Sum.inr_injective.injOn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [topChain_eq_singleton_indexSimplex_of_ne_univ D (by
      intro heq
      have hiErase : i ∉ Finset.univ.erase i := Finset.notMem_erase i _
      exact hiErase (by simp [heq]))]
    congr 1
    exact Finset.image_erase Sum.inr_injective Finset.univ i
  · intro i hi j hj hij
    exact (Finset.erase_inj Finset.univ hi).mp hij

private theorem relevant_proper_has_index (D : SimplexFamily I V)
    {A : Finset I} (hA : A ≠ Finset.univ) {ρ : Finset (V ⊕ I)}
    (hrel : (family D).IsRelevantCodimOne A ρ) :
    ∃ B ∈ SimplexFamily.boundaryIndices A, ρ = indexSimplex B := by
  rcases hrel with ⟨hcard, hρA | ⟨B, hBboundary, hρB⟩⟩
  change ρ.card + 1 = A.card at hcard
  · change ρ ∈ complex D A at hρA
    have hsimp := (mem_complex_iff D A ρ).mp hρA
    rw [IsSimplex, if_neg hA] at hsimp
    obtain ⟨K, hKA, rfl⟩ := hsimp
    have hKcard : K.card + 1 = A.card := by
      simpa using hcard
    exact ⟨K, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hKA, hKcard⟩, rfl⟩
  · have hBdata := Finset.mem_filter.mp hBboundary
    have hBsub : B ⊆ A := Finset.mem_powerset.mp hBdata.1
    have hBne : B ≠ Finset.univ := by
      intro hBuniv
      apply hA
      exact Finset.Subset.antisymm (Finset.subset_univ A) (by
        simpa [hBuniv] using hBsub)
    change ρ ∈ complex D B at hρB
    have hsimp := (mem_complex_iff D B ρ).mp hρB
    rw [IsSimplex, if_neg hBne] at hsimp
    obtain ⟨K, hKB, rfl⟩ := hsimp
    have hKcodim : K.card + 1 = A.card := by
      change (indexSimplex (V := V) K).card + 1 = A.card at hcard
      simpa using hcard
    have hKcard : K.card = B.card := by
      omega
    have hKeq : K = B := Finset.eq_of_subset_of_card_le hKB (by omega)
    exact ⟨B, hBboundary, congrArg indexSimplex hKeq⟩

private theorem proper_incidence_counts (D : SimplexFamily I V)
    {A : Finset I} (hA : A ≠ Finset.univ)
    {B : Finset I} (hBboundary : B ∈ SimplexFamily.boundaryIndices A) :
    (family D).cofaceCount A (indexSimplex B) = 1 ∧
      (family D).boundaryMembershipCount A (indexSimplex B) = 1 := by
  have hBdata := Finset.mem_filter.mp hBboundary
  have hBsub : B ⊆ A := Finset.mem_powerset.mp hBdata.1
  have hBne : B ≠ Finset.univ := by
    intro hBuniv
    apply hA
    exact Finset.Subset.antisymm (Finset.subset_univ A) (by
      simpa [hBuniv] using hBsub)
  have htop : ((family D).complex A).topSimplices A.card = {indexSimplex A} := by
    change (complex D A).topSimplices A.card = _
    ext τ
    simp only [FiniteSimplicialComplex.topSimplices, Finset.mem_filter,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hτ, hτcard⟩
      apply (isTopSimplex_of_ne_univ D hA τ).mp
      exact ⟨(FiniteSimplicialComplex.mem_simplices_iff (complex D A) τ).mp hτ,
        hτcard⟩
    · intro hτ
      have htopdata := (isTopSimplex_of_ne_univ D hA τ).mpr hτ
      exact ⟨(FiniteSimplicialComplex.mem_simplices_iff (complex D A) τ).mpr
        htopdata.1, htopdata.2⟩
  constructor
  · unfold SimplexFamily.cofaceCount
    rw [htop]
    have hsubset : indexSimplex (V := V) B ⊆ indexSimplex A :=
      (indexSimplex_subset_iff B A).2 hBsub
    change (({indexSimplex (V := V) A} : Finset (Finset (V ⊕ I))).filter
      (fun τ ↦ indexSimplex B ⊆ τ)).card = 1
    rw [Finset.filter_eq_self.mpr]
    · simp
    · intro τ hτ
      have hτeq : τ = indexSimplex A := Finset.mem_singleton.mp hτ
      simpa [hτeq] using hsubset
  · have hboundary :
        (SimplexFamily.boundaryIndices A).filter
          (fun C ↦ indexSimplex B ∈ (family D).complex C) = {B} := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hCboundary, hBC⟩
        have hCdata := Finset.mem_filter.mp hCboundary
        have hCsub : C ⊆ A := Finset.mem_powerset.mp hCdata.1
        have hCne : C ≠ Finset.univ := by
          intro hCuniv
          apply hA
          exact Finset.Subset.antisymm (Finset.subset_univ A) (by
            simpa [hCuniv] using hCsub)
        change indexSimplex B ∈ complex D C at hBC
        have hsimp := (mem_complex_iff D C (indexSimplex B)).mp hBC
        rw [IsSimplex, if_neg hCne] at hsimp
        obtain ⟨K, hKC, hindex⟩ := hsimp
        have hBK : B = K := indexSimplex_injective hindex
        have hBCsub : B ⊆ C := by simpa [hBK] using hKC
        exact (Finset.eq_of_subset_of_card_le hBCsub (by omega)).symm
      · intro hCB
        subst C
        refine ⟨hBboundary, ?_⟩
        change indexSimplex B ∈ complex D B
        apply (mem_complex_iff D B (indexSimplex B)).mpr
        rw [IsSimplex, if_neg hBne]
        exact ⟨B, Finset.Subset.rfl, rfl⟩
    unfold SimplexFamily.boundaryMembershipCount
    rw [hboundary]
    simp

private theorem pseudo_family_proper (D : SimplexFamily I V)
    {A : Finset I} (hA : A ≠ Finset.univ) :
    ∀ ρ : Finset (V ⊕ I), (family D).IsRelevantCodimOne A ρ →
      (family D).cofaceCount A ρ +
        (family D).boundaryMembershipCount A ρ = 2 := by
  intro ρ hrel
  obtain ⟨B, hBboundary, rfl⟩ := relevant_proper_has_index D hA hrel
  obtain ⟨hr, hs⟩ := proper_incidence_counts D hA hBboundary
  omega

private theorem relevant_univ_to_original (D : SimplexFamily I V)
    {ρ : Finset (V ⊕ I)} (hrel :
      (family D).IsRelevantCodimOne (Finset.univ : Finset I) ρ) :
    D.IsRelevantCodimOne (Finset.univ \ indexPart ρ) (oldPart ρ) := by
  rcases hrel with ⟨hcard, hrest⟩
  have hcard' : ρ.card + 1 = Fintype.card I := by
    change ρ.card + 1 = (Finset.univ : Finset I).card at hcard
    simpa using hcard
  have hcodim := codim_card_complement ρ hcard'
  refine ⟨hcodim, ?_⟩
  rcases hrest with hρ | ⟨B, hBboundary, hρB⟩
  · change ρ ∈ complex D Finset.univ at hρ
    have hsimp := (mem_complex_iff D Finset.univ ρ).mp hρ
    rw [IsSimplex, if_pos rfl] at hsimp
    obtain ⟨A, σ, K, hσ, hKA, _, rfl⟩ := hsimp
    simp only [oldPart_oldSimplex_union_indexSimplex,
      indexPart_oldSimplex_union_indexSimplex] at hcodim ⊢
    have hAC : A ⊆ Finset.univ \ K := by
      intro i hiA
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      intro hiK
      exact (Finset.mem_sdiff.mp (hKA hiK)).2 hiA
    have hσle : σ.card ≤ A.card := D.dimension A hσ
    have hAle : A.card ≤ (Finset.univ \ K).card := Finset.card_le_card hAC
    by_cases hAcard : A.card = (Finset.univ \ K).card
    · left
      have hACeq : A = Finset.univ \ K :=
        Finset.eq_of_subset_of_card_le hAC (by omega)
      simpa [hACeq] using hσ
    · right
      have hAcard' : A.card = σ.card := by omega
      refine ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAC, ?_⟩, hσ⟩
      omega
  · have hBdata := Finset.mem_filter.mp hBboundary
    have hBne : B ≠ Finset.univ := by
      intro hBuniv
      rw [hBuniv, Finset.card_univ] at hBdata
      omega
    change ρ ∈ complex D B at hρB
    have hsimp := (mem_complex_iff D B ρ).mp hρB
    rw [IsSimplex, if_neg hBne] at hsimp
    obtain ⟨K, hKB, hρeq⟩ := hsimp
    have hKcard : K.card = B.card := by
      rw [hρeq, card_indexSimplex] at hcard'
      rw [Finset.card_univ] at hBdata
      omega
    have hKBeq : K = B := Finset.eq_of_subset_of_card_le hKB (by omega)
    subst ρ
    subst K
    rw [oldPart_indexSimplex, indexPart_indexSimplex] at hcodim ⊢
    right
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩,
      (D.complex ∅).empty_mem'⟩
    simpa using hcodim

private theorem envelope_top_coface_iff (D : SimplexFamily I V)
    {ρ ω : Finset (V ⊕ I)} (hcard : ρ.card + 1 = Fintype.card I) :
    (ω ∈ complex D Finset.univ ∧ ω.card = (Finset.univ : Finset I).card ∧ ρ ⊆ ω) ↔
      (∃ σ : Finset V,
        D.IsTopSimplex (Finset.univ \ indexPart ρ) σ ∧ oldPart ρ ⊆ σ ∧
          ω = oldSimplex σ ∪ indexSimplex (indexPart ρ)) ∨
      (∃ B, B.Nonempty ∧
        B ∈ SimplexFamily.boundaryIndices (Finset.univ \ indexPart ρ) ∧
          oldPart ρ ∈ D.complex B ∧
          ω = oldSimplex (oldPart ρ) ∪ indexSimplex (Finset.univ \ B)) := by
  have hcodim := codim_card_complement ρ hcard
  have hCnonempty : (Finset.univ \ indexPart ρ).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hCempty
    rw [hCempty] at hcodim
    simp at hcodim
  constructor
  · rintro ⟨hω, hωcard, hρω⟩
    obtain ⟨A, hA, htopA, hindex⟩ :=
      (isTopSimplex_univ_iff D ω).mp ⟨hω, hωcard⟩
    have hτsub : oldPart ρ ⊆ oldPart ω := by
      intro v hv
      have hvρ : Sum.inl v ∈ ρ := by simpa [oldPart] using hv
      have hvω := hρω hvρ
      simpa [oldPart] using hvω
    have hKsub : indexPart ρ ⊆ indexPart ω := by
      intro i hi
      have hiρ : Sum.inr i ∈ ρ := by simpa [indexPart] using hi
      have hiω := hρω hiρ
      simpa [indexPart] using hiω
    have hAC : A ⊆ Finset.univ \ indexPart ρ := by
      intro i hiA
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      intro hiK
      have hiIndex := hKsub hiK
      rw [hindex] at hiIndex
      exact (Finset.mem_sdiff.mp hiIndex).2 hiA
    have hτle : (oldPart ρ).card ≤ (oldPart ω).card := Finset.card_le_card hτsub
    have hAle : A.card ≤ (Finset.univ \ indexPart ρ).card := Finset.card_le_card hAC
    have hApart : (oldPart ω).card = A.card := htopA.2
    by_cases hAcard : A.card = (Finset.univ \ indexPart ρ).card
    · left
      have hAeq : A = Finset.univ \ indexPart ρ :=
        Finset.eq_of_subset_of_card_le hAC (by omega)
      refine ⟨oldPart ω, ⟨by simpa [hAeq] using htopA.1, by omega⟩, hτsub, ?_⟩
      have hdecomp := old_index_decomposition ω
      simpa [hindex, hAeq] using hdecomp
    · right
      have hAcard' : A.card = (oldPart ρ).card := by omega
      have hτeq : oldPart ρ = oldPart ω :=
        Finset.eq_of_subset_of_card_le hτsub (by omega)
      refine ⟨A, hA, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAC, by omega⟩,
        by simpa [hτeq] using htopA.1, ?_⟩
      have hdecomp := old_index_decomposition ω
      simpa [hτeq, hindex] using hdecomp
  · rintro (⟨σ, htopσ, hτσ, hωeq⟩ |
      ⟨B, hBnonempty, hBboundary, hτB, hωeq⟩)
    · rw [hωeq]
      have henvtop := (isTopSimplex_univ_iff D
          (oldSimplex σ ∪ indexSimplex (indexPart ρ))).mpr
        ⟨Finset.univ \ indexPart ρ, hCnonempty, by simpa using htopσ, by simp⟩
      refine ⟨henvtop.1, henvtop.2, ?_⟩
      intro z hz
      rw [old_index_decomposition ρ] at hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_union_left _ (Finset.image_mono Sum.inl hτσ hz)
      · exact Finset.mem_union_right _ hz
    · rw [hωeq]
      have hBdata := Finset.mem_filter.mp hBboundary
      have hBsub : B ⊆ Finset.univ \ indexPart ρ :=
        Finset.mem_powerset.mp hBdata.1
      have hBcard : B.card = (oldPart ρ).card := by omega
      have hKB : indexPart ρ ⊆ Finset.univ \ B := by
        intro i hiK
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ i, ?_⟩
        intro hiB
        exact (Finset.mem_sdiff.mp (hBsub hiB)).2 hiK
      have henvtop := (isTopSimplex_univ_iff D
          (oldSimplex (oldPart ρ) ∪ indexSimplex (Finset.univ \ B))).mpr
        ⟨B, hBnonempty, ⟨by simpa using hτB, by simpa using hBcard.symm⟩, by simp⟩
      refine ⟨henvtop.1, henvtop.2, ?_⟩
      intro z hz
      rw [old_index_decomposition ρ] at hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_union_left _ hz
      · exact Finset.mem_union_right _ (Finset.image_mono Sum.inr hKB hz)

private theorem incidence_univ_of_oldPart_nonempty (D : SimplexFamily I V)
    {ρ : Finset (V ⊕ I)} (hcard : ρ.card + 1 = Fintype.card I)
    (hτ : (oldPart ρ).Nonempty) :
    (family D).cofaceCount Finset.univ ρ +
        (family D).boundaryMembershipCount Finset.univ ρ =
      D.cofaceCount (Finset.univ \ indexPart ρ) (oldPart ρ) +
        D.boundaryMembershipCount (Finset.univ \ indexPart ρ) (oldPart ρ) := by
  let R := (((D.complex (Finset.univ \ indexPart ρ)).topSimplices
    (Finset.univ \ indexPart ρ).card).filter (fun σ ↦ oldPart ρ ⊆ σ))
  let S := (SimplexFamily.boundaryIndices (Finset.univ \ indexPart ρ)).filter
    (fun B ↦ oldPart ρ ∈ D.complex B)
  let T := ((complex D Finset.univ).topSimplices (Finset.univ : Finset I).card).filter
    (fun ω ↦ ρ ⊆ ω)
  let f : Finset V → Finset (V ⊕ I) :=
    fun σ ↦ oldSimplex σ ∪ indexSimplex (indexPart ρ)
  let g : Finset I → Finset (V ⊕ I) :=
    fun B ↦ oldSimplex (oldPart ρ) ∪ indexSimplex (Finset.univ \ B)
  have hT : T = R.image f ∪ S.image g := by
    ext ω
    constructor
    · intro hωT
      have hωT' := Finset.mem_filter.mp hωT
      have htopraw := Finset.mem_filter.mp hωT'.1
      have hclass := (envelope_top_coface_iff D hcard).mp
        ⟨(FiniteSimplicialComplex.mem_simplices_iff (complex D Finset.univ) ω).mp
            htopraw.1, htopraw.2, hωT'.2⟩
      rcases hclass with ⟨σ, htopσ, hτσ, hωeq⟩ |
        ⟨B, _, hBboundary, hτB, hωeq⟩
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨σ, Finset.mem_filter.mpr ⟨?_, hτσ⟩, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨(FiniteSimplicialComplex.mem_simplices_iff
              (D.complex (Finset.univ \ indexPart ρ)) σ).mpr htopσ.1, htopσ.2⟩
        · exact hωeq.symm
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr
          ⟨B, Finset.mem_filter.mpr ⟨hBboundary, hτB⟩, hωeq.symm⟩
    · intro hω
      rcases Finset.mem_union.mp hω with hω | hω
      · obtain ⟨σ, hσR, hσω⟩ := Finset.mem_image.mp hω
        have hσR' := Finset.mem_filter.mp hσR
        have htopraw := Finset.mem_filter.mp hσR'.1
        have htopσ : D.IsTopSimplex (Finset.univ \ indexPart ρ) σ :=
          ⟨(FiniteSimplicialComplex.mem_simplices_iff
            (D.complex (Finset.univ \ indexPart ρ)) σ).mp htopraw.1, htopraw.2⟩
        have hclass := (envelope_top_coface_iff D hcard).mpr
          (Or.inl ⟨σ, htopσ, hσR'.2, hσω.symm⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨(FiniteSimplicialComplex.mem_simplices_iff (complex D Finset.univ) ω).mpr
            hclass.1, hclass.2.1⟩, hclass.2.2⟩
      · obtain ⟨B, hBS, hBω⟩ := Finset.mem_image.mp hω
        have hBS' := Finset.mem_filter.mp hBS
        have hBdata := Finset.mem_filter.mp hBS'.1
        have hcodim := codim_card_complement ρ hcard
        have hBcard : B.card = (oldPart ρ).card := by omega
        have hBnonempty : B.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hBempty
          subst B
          have : (oldPart ρ).card = 0 := by simpa using hBcard.symm
          exact hτ.ne_empty (Finset.card_eq_zero.mp this)
        have hclass := (envelope_top_coface_iff D hcard).mpr
          (Or.inr ⟨B, hBnonempty, hBS'.1, hBS'.2, hBω.symm⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨(FiniteSimplicialComplex.mem_simplices_iff (complex D Finset.univ) ω).mpr
            hclass.1, hclass.2.1⟩, hclass.2.2⟩
  have hf : Function.Injective f := by
    intro σ τ h
    have hold := congrArg oldPart h
    simpa [f] using hold
  have hg : Function.Injective g := by
    intro B C h
    have hindex := congrArg indexPart h
    have hcomp : Finset.univ \ B = Finset.univ \ C := by simpa [g] using hindex
    ext i
    have hi := congrArg (fun K : Finset I ↦ i ∈ K) hcomp
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
    tauto
  have hdisj : Disjoint (R.image f) (S.image g) := by
    rw [Finset.disjoint_left]
    intro ω hωR hωS
    obtain ⟨σ, hσR, hσω⟩ := Finset.mem_image.mp hωR
    obtain ⟨B, hBS, hBω⟩ := Finset.mem_image.mp hωS
    have hold := congrArg oldPart (hσω.trans hBω.symm)
    have hσeq : σ = oldPart ρ := by simpa [f, g] using hold
    have hσR' := Finset.mem_filter.mp hσR
    have htopraw := Finset.mem_filter.mp hσR'.1
    have hcodim := codim_card_complement ρ hcard
    rw [hσeq] at htopraw
    omega
  have hTcard : T.card = R.card + S.card := by
    rw [hT, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ hf, Finset.card_image_of_injective _ hg]
  have hboundaryZero :
      (family D).boundaryMembershipCount Finset.univ ρ = 0 := by
    unfold SimplexFamily.boundaryMembershipCount
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro B hB
    have hB' := Finset.mem_filter.mp hB
    have hBdata := Finset.mem_filter.mp hB'.1
    have hBne : B ≠ Finset.univ := by
      intro hBuniv
      rw [hBuniv, Finset.card_univ] at hBdata
      omega
    have hρB := hB'.2
    change ρ ∈ complex D B at hρB
    have hsimp := (mem_complex_iff D B ρ).mp hρB
    rw [IsSimplex, if_neg hBne] at hsimp
    obtain ⟨K, _, hρeq⟩ := hsimp
    have hold := congrArg oldPart hρeq
    have : oldPart ρ = ∅ := by simpa using hold
    exact hτ.ne_empty this
  change T.card + (family D).boundaryMembershipCount Finset.univ ρ =
    R.card + S.card
  omega

private theorem incidence_univ_of_oldPart_empty (D : SimplexFamily I V)
    {ρ : Finset (V ⊕ I)} (hcard : ρ.card + 1 = Fintype.card I)
    (hτ : oldPart ρ = ∅) :
    (family D).cofaceCount Finset.univ ρ +
        (family D).boundaryMembershipCount Finset.univ ρ =
      D.cofaceCount (Finset.univ \ indexPart ρ) (oldPart ρ) +
        D.boundaryMembershipCount (Finset.univ \ indexPart ρ) (oldPart ρ) := by
  let R := (((D.complex (Finset.univ \ indexPart ρ)).topSimplices
    (Finset.univ \ indexPart ρ).card).filter (fun σ ↦ oldPart ρ ⊆ σ))
  let T := ((complex D Finset.univ).topSimplices (Finset.univ : Finset I).card).filter
    (fun ω ↦ ρ ⊆ ω)
  let f : Finset V → Finset (V ⊕ I) :=
    fun σ ↦ oldSimplex σ ∪ indexSimplex (indexPart ρ)
  have hcodim := codim_card_complement ρ hcard
  have hCcard : (Finset.univ \ indexPart ρ).card = 1 := by
    rw [hτ] at hcodim
    simpa using hcodim.symm
  have hT : T = R.image f := by
    ext ω
    constructor
    · intro hωT
      have hωT' := Finset.mem_filter.mp hωT
      have htopraw := Finset.mem_filter.mp hωT'.1
      have hclass := (envelope_top_coface_iff D hcard).mp
        ⟨(FiniteSimplicialComplex.mem_simplices_iff (complex D Finset.univ) ω).mp
            htopraw.1, htopraw.2, hωT'.2⟩
      rcases hclass with ⟨σ, htopσ, hτσ, hωeq⟩ |
        ⟨B, hBnonempty, hBboundary, _, _⟩
      · apply Finset.mem_image.mpr
        refine ⟨σ, Finset.mem_filter.mpr ⟨?_, hτσ⟩, hωeq.symm⟩
        exact Finset.mem_filter.mpr
          ⟨(FiniteSimplicialComplex.mem_simplices_iff
            (D.complex (Finset.univ \ indexPart ρ)) σ).mpr htopσ.1, htopσ.2⟩
      · have hBdata := Finset.mem_filter.mp hBboundary
        have hBcard : B.card = 0 := by omega
        exact (hBnonempty.ne_empty (Finset.card_eq_zero.mp hBcard)).elim
    · intro hω
      obtain ⟨σ, hσR, hσω⟩ := Finset.mem_image.mp hω
      have hσR' := Finset.mem_filter.mp hσR
      have htopraw := Finset.mem_filter.mp hσR'.1
      have htopσ : D.IsTopSimplex (Finset.univ \ indexPart ρ) σ :=
        ⟨(FiniteSimplicialComplex.mem_simplices_iff
          (D.complex (Finset.univ \ indexPart ρ)) σ).mp htopraw.1, htopraw.2⟩
      have hclass := (envelope_top_coface_iff D hcard).mpr
        (Or.inl ⟨σ, htopσ, hσR'.2, hσω.symm⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨(FiniteSimplicialComplex.mem_simplices_iff (complex D Finset.univ) ω).mpr
          hclass.1, hclass.2.1⟩, hclass.2.2⟩
  have hf : Function.Injective f := by
    intro σ τ h
    have hold := congrArg oldPart h
    simpa [f] using hold
  have hTcard : T.card = R.card := by
    rw [hT, Finset.card_image_of_injective _ hf]
  have hρeq : ρ = indexSimplex (indexPart ρ) := by
    have hdecomp := old_index_decomposition ρ
    simpa [hτ, oldSimplex] using hdecomp
  have hKboundary : indexPart ρ ∈
      SimplexFamily.boundaryIndices (Finset.univ : Finset I) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    have hsplit := card_oldPart_add_card_indexPart ρ
    rw [hτ] at hsplit
    simp at hsplit
    rw [Finset.card_univ]
    omega
  have hEnvelopeBoundary :
      (family D).boundaryMembershipCount Finset.univ ρ = 1 := by
    unfold SimplexFamily.boundaryMembershipCount
    have hset : (SimplexFamily.boundaryIndices (Finset.univ : Finset I)).filter
        (fun B ↦ ρ ∈ (family D).complex B) = {indexPart ρ} := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hBboundary, hρB⟩
        have hBdata := Finset.mem_filter.mp hBboundary
        have hBne : B ≠ Finset.univ := by
          intro hBuniv
          rw [hBuniv, Finset.card_univ] at hBdata
          omega
        change ρ ∈ complex D B at hρB
        have hsimp := (mem_complex_iff D B ρ).mp hρB
        rw [IsSimplex, if_neg hBne] at hsimp
        obtain ⟨K, hKB, hρK⟩ := hsimp
        have hKcard : K.card = B.card := by
          rw [hρK, card_indexSimplex] at hcard
          rw [Finset.card_univ] at hBdata
          omega
        have hKBeq : K = B := Finset.eq_of_subset_of_card_le hKB (by omega)
        have hKi : K = indexPart ρ :=
          indexSimplex_injective (hρK.symm.trans hρeq)
        exact hKBeq.symm.trans hKi
      · intro hB
        subst B
        refine ⟨hKboundary, ?_⟩
        change ρ ∈ complex D (indexPart ρ)
        apply (mem_complex_iff D (indexPart ρ) ρ).mpr
        have hKne : indexPart ρ ≠ Finset.univ := by
          intro hKuniv
          have hKdata := Finset.mem_filter.mp hKboundary
          rw [hKuniv, Finset.card_univ] at hKdata
          omega
        rw [IsSimplex, if_neg hKne]
        exact ⟨indexPart ρ, Finset.Subset.rfl, hρeq⟩
    rw [hset]
    simp
  have hOriginalBoundary :
      D.boundaryMembershipCount (Finset.univ \ indexPart ρ) (oldPart ρ) = 1 := by
    unfold SimplexFamily.boundaryMembershipCount
    have hset : (SimplexFamily.boundaryIndices (Finset.univ \ indexPart ρ)).filter
        (fun B ↦ oldPart ρ ∈ D.complex B) = {∅} := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hBboundary, _⟩
        have hBdata := Finset.mem_filter.mp hBboundary
        apply Finset.card_eq_zero.mp
        omega
      · intro hB
        subst B
        refine ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩, ?_⟩
        · simpa using hCcard.symm
        · simp [hτ]
    rw [hset]
    simp
  change T.card + (family D).boundaryMembershipCount Finset.univ ρ =
    R.card + D.boundaryMembershipCount (Finset.univ \ indexPart ρ) (oldPart ρ)
  omega

/-- Theorem 1.5: envelopes preserve pseudo-simplices. -/
theorem pseudo_family {D : SimplexFamily I V} (hD : D.IsPseudoSimplex) :
    (family D).IsPseudoSimplex := by
  intro A ρ hrel
  by_cases hA : A = Finset.univ
  · subst A
    have hcard : ρ.card + 1 = Fintype.card I := by
      have hcard' := hrel.1
      change ρ.card + 1 = (Finset.univ : Finset I).card at hcard'
      simpa using hcard'
    have hrelD := relevant_univ_to_original D hrel
    have hcount := hD (Finset.univ \ indexPart ρ) (oldPart ρ) hrelD
    by_cases hτ : (oldPart ρ).Nonempty
    · rw [incidence_univ_of_oldPart_nonempty D hcard hτ]
      exact hcount
    · have hτempty : oldPart ρ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hτ
      rw [incidence_univ_of_oldPart_empty D hcard hτempty]
      exact hcount
  · exact pseudo_family_proper D hA ρ hrel

/-- Theorem 1.6: envelopes preserve chain-simplices. -/
theorem chain_family {D : SimplexFamily I V} (hD : D.IsChainSimplex) :
    (family D).IsChainSimplex := by
  rw [SimplexFamily.isChainSimplex_iff_incidenceParity]
  intro A ρ hcard
  by_cases hA : A = Finset.univ
  · subst A
    have hcardI : ρ.card + 1 = Fintype.card I := by
      simpa using hcard
    have hcodim := codim_card_complement ρ hcardI
    have hparityD :=
      (SimplexFamily.isChainSimplex_iff_incidenceParity D).mp hD
        (Finset.univ \ indexPart ρ) (oldPart ρ) hcodim
    have hcount :
        (family D).cofaceCount Finset.univ ρ +
            (family D).boundaryMembershipCount Finset.univ ρ =
          D.cofaceCount (Finset.univ \ indexPart ρ) (oldPart ρ) +
            D.boundaryMembershipCount (Finset.univ \ indexPart ρ) (oldPart ρ) := by
      by_cases hτ : (oldPart ρ).Nonempty
      · exact incidence_univ_of_oldPart_nonempty D hcardI hτ
      · exact incidence_univ_of_oldPart_empty D hcardI
          (Finset.not_nonempty_iff_eq_empty.mp hτ)
    have hcountCast := congrArg (fun n : ℕ ↦ (n : ZMod 2)) hcount
    have hsum :
        ((family D).cofaceCount Finset.univ ρ : ZMod 2) +
            ((family D).boundaryMembershipCount Finset.univ ρ : ZMod 2) = 0 := by
      calc
        ((family D).cofaceCount Finset.univ ρ : ZMod 2) +
              ((family D).boundaryMembershipCount Finset.univ ρ : ZMod 2) =
            (D.cofaceCount (Finset.univ \ indexPart ρ) (oldPart ρ) : ZMod 2) +
              (D.boundaryMembershipCount
                (Finset.univ \ indexPart ρ) (oldPart ρ) : ZMod 2) := by
          simpa only [Nat.cast_add] using hcountCast
        _ = (D.boundaryMembershipCount
              (Finset.univ \ indexPart ρ) (oldPart ρ) : ZMod 2) +
              (D.boundaryMembershipCount
                (Finset.univ \ indexPart ρ) (oldPart ρ) : ZMod 2) := by
          rw [hparityD]
        _ = 0 := CharTwo.add_self_eq_zero _
    calc
      ((family D).cofaceCount Finset.univ ρ : ZMod 2) =
          -((family D).boundaryMembershipCount Finset.univ ρ : ZMod 2) :=
        eq_neg_of_add_eq_zero_left hsum
      _ = ((family D).boundaryMembershipCount Finset.univ ρ : ZMod 2) :=
        ZMod.neg_eq_self_mod_two _
  · by_cases hrel : (family D).IsRelevantCodimOne A ρ
    · obtain ⟨B, hBboundary, rfl⟩ := relevant_proper_has_index D hA hrel
      obtain ⟨hr, hs⟩ := proper_incidence_counts D hA hBboundary
      simp [hr, hs]
    · have hr : (family D).cofaceCount A ρ = 0 := by
        unfold SimplexFamily.cofaceCount
        rw [Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro τ hτ
        have hτ' := Finset.mem_filter.mp hτ
        have htop : τ ∈ ((family D).complex A).simplices ∧ τ.card = A.card := by
          simpa [FiniteSimplicialComplex.topSimplices] using hτ'.1
        apply hrel
        refine ⟨hcard, Or.inl ?_⟩
        exact (FiniteSimplicialComplex.mem_simplices_iff ((family D).complex A) ρ).mp
          (((family D).complex A).downward_closed htop.1 hτ'.2)
      have hs : (family D).boundaryMembershipCount A ρ = 0 := by
        unfold SimplexFamily.boundaryMembershipCount
        rw [Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro B hB
        have hB' := Finset.mem_filter.mp hB
        exact hrel ⟨hcard, Or.inr ⟨B, hB'.1, hB'.2⟩⟩
      simp [hr, hs]

end Envelope

end BeyondSperner
