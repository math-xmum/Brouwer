-- Section prelude excerpt for BrouwerBench prompts.
-- This is prompt context, not a standalone Lean file.

section Brouwer.ProductRetraction

variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Inhabited I]
variable (card : I -> Nat+)

abbrev BigSimplex : Type :=
  stdSimplex Real (Fin (total_card card))

abbrev ProductSimplices : Type :=
  (i : I) -> stdSimplex Real (Fin (card i))

noncomputable def prefix_sum (i : I) : Nat :=
  sum j in Finset.univ.filter (fun j => j < i), (card j : Nat)

-- Split a flat big-simplex coordinate into a block and an in-block coordinate.
noncomputable def index_split (k : Fin (total_card card)) :
    Sigma fun i => Fin (card i) :=
  Classical.choose (index_split_existence card k)

-- Combine a block and in-block coordinate into one flat big-simplex coordinate.
noncomputable def index_combine (p : Sigma fun i => Fin (card i)) :
    Fin (total_card card) :=
  ⟨prefix_sum card p.1 + (p.2 : Nat), by
    -- proof that the combined index is below total_card
    sorry⟩

noncomputable def blockWeight (i : I) : Real :=
  (card i : Real) / (total_card card : Real)

noncomputable def blockSum (i : I) (x : BigSimplex card) : Real :=
  sum j : Fin (card i), x.1 (index_combine card ⟨i, j⟩)

noncomputable def uniformProduct : ProductSimplices card :=
  fun i => ⟨fun _ => (1 : Real) / (card i : Real), by
    -- nonnegative coordinates and sum one
    sorry⟩

noncomputable def z_uniform : BigSimplex card :=
  ⟨fun _ => (1 : Real) / (total_card card : Real), by
    -- nonnegative coordinates and sum one
    sorry⟩

noncomputable def deficit (x : BigSimplex card) : Real :=
  sum i, max (0 : Real) ((blockWeight card i) - blockSum card i x)

noncomputable def tPush (x : BigSimplex card) : Real :=
  deficit card x / (1 + deficit card x)

noncomputable def pushTowardsZ (x : BigSimplex card) : BigSimplex card :=
  ⟨fun k =>
      (1 - tPush card x) * x.1 k +
      (tPush card x) * (z_uniform card).1 k,
    by
      -- convex combination of x and the uniform point
      sorry⟩

noncomputable def project_to_product (x : BigSimplex card) :
    ProductSimplices card :=
  fun i =>
    let y := pushTowardsZ card x
    let s := blockSum card i y
    ⟨fun j => y.1 (index_combine card ⟨i, j⟩) / s, by
      -- positivity of s makes blockwise normalization valid
      sorry⟩

noncomputable def embed_from_product (y : ProductSimplices card) :
    BigSimplex card :=
  ⟨fun k =>
      let p := index_split card k
      (y p.1).1 p.2 * (card p.1 : Real) / (total_card card : Real),
    by
      -- block weights make the embedded vector sum to one
      sorry⟩

end Brouwer.ProductRetraction
