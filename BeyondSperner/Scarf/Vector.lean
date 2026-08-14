import BeyondSperner.Scarf.Generalized
import BeyondSperner.Coloring.Vector

/-!
# The vector Scarf theorem

This file completes the last passage in Section 7.  Lemma 7.3 and the
associated chain-simplex are used through `GeneralizedScarf`; the only
additional step is the realizability bridge that turns its good
oriented-matroid basis into an actual linear basis and an actual
nonnegative linear combination.

The finite type `M` is the label-level encoding of the finite vector set
in the paper.  `Framework.vector_injective` makes this encoding faithful:
finite sets of labels and finite sets of represented vectors have no
hidden multiplicities.
-/

namespace BeyondSperner

open Classical
open Set

namespace VectorScarf

variable {I X M : Type*} [Fintype I] [Fintype X] [Fintype M]
  [Nonempty X] [DecidableEq I] [DecidableEq X] [DecidableEq M]
  [LinearOrder I]

/-- A coloring of the old ground set by vector labels other than `b`. -/
abbrev Coloring (F : VectorColoring.Framework I M) :=
  X → {m : M // m ≠ F.distinguished}

/-- The label map on `X ⊕ I`, extending the coloring by the standard
basis labels. -/
def extendedLabeling (F : VectorColoring.Framework I M)
    (c : Coloring (X := X) F) :
    X ⊕ I → M :=
  Sum.elim (fun x ↦ (c x).1) F.basis

/-- The vector-valued map `φ` in the paper's statement. -/
def vectorMap (F : VectorColoring.Framework I M)
    (c : Coloring (X := X) F) :
    X ⊕ I → I → ℝ :=
  fun x ↦ F.vector (extendedLabeling F c x)

omit [Fintype X] [Nonempty X] [DecidableEq I] [DecidableEq X] [DecidableEq M] [LinearOrder I] in @[simp]
theorem vectorMap_inl (F : VectorColoring.Framework I M)
    (c : Coloring (X := X) F)
    (x : X) :
    vectorMap F c (Sum.inl x) = F.vector (c x).1 :=
  rfl

omit [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq M] [LinearOrder I] in @[simp]
theorem vectorMap_inr (F : VectorColoring.Framework I M)
    (c : Coloring (X := X) F)
    (i : I) :
    vectorMap F c (Sum.inr i) = Pi.single i 1 := by
  change F.vector (F.basis i) = Pi.single i 1
  rw [F.basis_vector]
  ext j
  by_cases hij : i = j <;> simp [hij]

/-- The finite label set underlying the vector image `φ(S)`. -/
def colorImage (F : VectorColoring.Framework I M)
    (c : Coloring (X := X) F)
    (S : Finset (X ⊕ I)) : Finset M :=
  S.image (extendedLabeling F c)

/-- The literal finite vector set `φ(S)`. -/
noncomputable def vectorImage (F : VectorColoring.Framework I M)
    (c : Coloring (X := X) F)
    (S : Finset (X ⊕ I)) : Finset (I → ℝ) :=
  F.vectorImage (colorImage F c S)

omit [Fintype X] [Nonempty X] [DecidableEq I] [DecidableEq X] [LinearOrder I] in theorem mem_vectorImage_iff
    (F : VectorColoring.Framework I M) (c : Coloring (X := X) F)
    (S : Finset (X ⊕ I)) (w : I → ℝ) :
    w ∈ vectorImage F c S ↔
      ∃ x ∈ S, vectorMap F c x = w := by
  constructor
  · intro hw
    obtain ⟨m, hm, hmw⟩ := Finset.mem_image.mp hw
    obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hm
    refine ⟨x, hx, ?_⟩
    change F.vector (extendedLabeling F c x) = w
    rw [hxm]
    exact hmw
  · rintro ⟨x, hx, hxw⟩
    apply Finset.mem_image.mpr
    refine ⟨extendedLabeling F c x, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · exact hxw

/-- The literal vector conclusion of the Scarf theorem following Lemma
7.3.  The basis is indexed by the finite image set, and its coercion is
proved equal to the represented vector family. -/
def IsSolution (orders : IndexedLinearOrders I X)
    (F : VectorColoring.Framework I M) (c : Coloring (X := X) F)
    (S : Finset (X ⊕ I)) : Prop :=
  orders.extend.IsDominant S Finset.univ ∧
    S.card = Fintype.card I ∧
      ∃ B : Module.Basis (vectorImage F c S : Set (I → ℝ)) ℝ (I → ℝ),
        (∀ w, B w = w.1) ∧
          ∃ q : {w : I → ℝ // w ∈ vectorImage F c S} → ℝ,
            (∀ w, 0 ≤ q w) ∧
              ∑ w, q w • w.1 = F.vector F.distinguished

/-- The vector Scarf theorem stated after Lemma 7.3.

The proof uses the already checked dominant-set conversion, then invokes
the single realizability bridge shared with Theorem 7.2. -/
theorem vectorScarf
    (orders : IndexedLinearOrders I X)
    (F : VectorColoring.Framework I M)
    (hbounded : Bornology.IsBounded F.nonnegativeSolutions)
    (c : Coloring (X := X) F) :
    ∃ S : Finset (X ⊕ I), IsSolution orders F c S := by
  let MF : MatroidColoring.Framework I M := F.toMatroidFramework hbounded
  let : Nonempty I := MF.index_nonempty
  obtain ⟨S, hDominant, hCard, hGood⟩ :=
    GeneralizedScarf.generalizedScarf orders MF c
  let T : Finset M := colorImage F c S
  have hbNotT : F.distinguished ∉ T := by
    intro hb
    change F.distinguished ∈ S.image (extendedLabeling F c) at hb
    obtain ⟨x, _, hxb⟩ := Finset.mem_image.mp hb
    cases x with
    | inl x => exact (c x).2 hxb
    | inr i => exact F.distinguished_notMem_basis ⟨i, hxb⟩
  obtain ⟨B, hB, q, hqNonneg, hqCombination⟩ :=
    F.exists_literalVectorBasis_and_nonnegativeCombination
      hbounded T hbNotT hGood
  exact ⟨S, hDominant, hCard, B, hB,
    q, hqNonneg, hqCombination⟩

section RawStatement

/-- Raw data for the paper's direct `φ : X ⊔ I → ℝ^I` formulation.

The two exclusions involving `b` are made explicit.  They are exactly what
is needed for the standard-basis labels and the old coloring to land in
`M \ {b}`; the paper uses them implicitly when it invokes the vector framework
with the restriction of `φ` as a coloring into `A = M - b`. -/
structure RawData (I X : Type*) [Fintype I] [Fintype X] [DecidableEq I] where
  phi : X ⊕ I → I → ℝ
  b : I → ℝ
  b_ne_zero : b ≠ 0
  b_nonneg : ∀ i, 0 ≤ b i
  phi_inr : ∀ i, phi (Sum.inr i) = Pi.single i 1
  old_ne_b : ∀ x, phi (Sum.inl x) ≠ b
  b_ne_basis : ∀ i, b ≠ Pi.single i 1

namespace RawData

variable (R : RawData I X)

/-- The finite vector set `φ(X ⊔ I) ∪ {b}` used in the paper. -/
noncomputable def labels : Finset (I → ℝ) :=
  Finset.univ.image R.phi ∪ {R.b}

/-- Labels are literally the vectors in the finite set above. -/
abbrev Label := {w : I → ℝ // w ∈ R.labels}

/-- The label represented by the `i`-th standard basis vector. -/
noncomputable def basisLabel (i : I) : R.Label :=
  ⟨Pi.single i 1, by
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨Sum.inr i, Finset.mem_univ _, R.phi_inr i⟩⟩

omit [Nonempty X] [DecidableEq X] [LinearOrder I] in @[simp]
theorem basisLabel_val (i : I) :
    (R.basisLabel i : I → ℝ) = Pi.single i 1 :=
  rfl

/-- The standard basis vectors, regarded as distinct labels. -/
noncomputable def basisEmbedding : I ↪ R.Label where
  toFun := R.basisLabel
  inj' := by
    intro i j hij
    by_contra hne
    have hji : j ≠ i := fun h ↦ hne h.symm
    have hv := congrFun (congrArg Subtype.val hij) i
    simp [hji] at hv

/-- The distinguished label represented by `b`. -/
noncomputable def distinguishedLabel : R.Label :=
  ⟨R.b, Finset.mem_union_right _ (by simp)⟩

omit [Nonempty X] [DecidableEq X] [LinearOrder I] in @[simp]
theorem distinguishedLabel_val :
    (R.distinguishedLabel : I → ℝ) = R.b :=
  rfl

/-- Automatically package raw `φ`-data as the vector framework used by
Theorem 7.2. -/
noncomputable def toFramework : VectorColoring.Framework I R.Label where
  vector := Subtype.val
  vector_injective := Subtype.val_injective
  basis := R.basisEmbedding
  distinguished := R.distinguishedLabel
  distinguished_notMem_basis := by
    rintro ⟨i, hi⟩
    exact R.b_ne_basis i (congrArg Subtype.val hi).symm
  distinguished_ne_zero := R.b_ne_zero
  basis_vector := by
    intro i
    rw [show R.basisEmbedding i = R.basisLabel i by rfl]
    ext j
    by_cases hij : i = j <;>
      simp [hij]
  distinguishedCoordinates := R.b
  distinguishedCoordinates_nonneg := R.b_nonneg
  distinguished_eq_sum := by
    change R.b = ∑ i, R.b i • Pi.single i 1
    funext j
    simp [Pi.single_apply]

/-- The raw old-point map is a coloring by labels other than `b`. -/
noncomputable def coloring : Coloring (X := X) R.toFramework :=
  fun x ↦ ⟨⟨R.phi (Sum.inl x), by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨Sum.inl x, Finset.mem_univ _, rfl⟩⟩, by
      intro h
      apply R.old_ne_b x
      exact congrArg Subtype.val h⟩

omit [Nonempty X] [DecidableEq X] [LinearOrder I] in @[simp]
theorem toFramework_vector (m : R.Label) :
    R.toFramework.vector m = m.1 :=
  rfl

omit [Nonempty X] [DecidableEq X] [LinearOrder I] in @[simp]
theorem coloring_vector (x : X) :
    R.toFramework.vector (R.coloring x).1 = R.phi (Sum.inl x) :=
  rfl

omit [Nonempty X] [DecidableEq X] [LinearOrder I] in
/-- The packaged vector map is exactly the original `φ`. -/
theorem vectorMap_eq_phi (x : X ⊕ I) :
    vectorMap R.toFramework R.coloring x = R.phi x := by
  cases x with
  | inl x =>
      rw [vectorMap_inl, R.coloring_vector]
  | inr i =>
      rw [vectorMap_inr]
      exact (R.phi_inr i).symm

/-- The literal finite set `φ(S)` in the raw statement. -/
noncomputable def vectorImage (S : Finset (X ⊕ I)) : Finset (I → ℝ) :=
  S.image R.phi

/-- The paper's final vector Scarf conclusion written directly in terms
of the original `φ`. -/
def IsSolution (orders : IndexedLinearOrders I X)
    (S : Finset (X ⊕ I)) : Prop :=
  orders.extend.IsDominant S Finset.univ ∧
    S.card = Fintype.card I ∧
      ∃ B : Module.Basis (R.vectorImage S : Set (I → ℝ)) ℝ (I → ℝ),
        (∀ w, B w = w.1) ∧
          ∃ q : {w : I → ℝ // w ∈ R.vectorImage S} → ℝ,
            (∀ w, 0 ≤ q w) ∧
              ∑ w, q w • w.1 = R.b

/-- Direct raw-`φ` form of the vector Scarf theorem.

The boundedness assumption is stated here rather than hidden in ambient
notation: it is the hypothesis on equation (30) needed by Theorem 7.2. -/
theorem scarf
    (orders : IndexedLinearOrders I X)
    (hbounded : Bornology.IsBounded R.toFramework.nonnegativeSolutions) :
    ∃ S : Finset (X ⊕ I), R.IsSolution orders S := by
  obtain ⟨S, hS⟩ := vectorScarf orders R.toFramework hbounded R.coloring
  have hImage :
      VectorScarf.vectorImage R.toFramework R.coloring S = R.vectorImage S := by
    ext w
    rw [mem_vectorImage_iff]
    simp only [RawData.vectorImage, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, hxw⟩
      exact ⟨x, hx, (R.vectorMap_eq_phi x).symm.trans hxw⟩
    · rintro ⟨x, hx, hxw⟩
      exact ⟨x, hx, R.vectorMap_eq_phi x |>.trans hxw⟩
  refine ⟨S, ?_⟩
  unfold VectorScarf.IsSolution at hS
  rw [hImage] at hS
  unfold RawData.IsSolution
  simpa [toFramework] using hS

end RawData

end RawStatement

end VectorScarf

end BeyondSperner
