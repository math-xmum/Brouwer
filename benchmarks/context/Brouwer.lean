-- Section prelude excerpt for BrouwerBench prompts.
-- This is prompt context, not a standalone Lean file.

-- Integer grid points of the standard simplex at denominator l.
abbrev TT (n : PNat) (l : PNat) :=
  {x : PiFinset fun (_ : Fin n) => Fin (l + 1) |
    sum i, (x i : Nat) = l}

def TTtostdSimplex (x : TT n l) : stdSimplex Real (Fin n) :=
  -- The actual definition maps i to x i / l and proves nonnegativity and sum one.
  ⟨fun i => x i / l, by
    constructor
    · intro i
      exact div_nonneg (by positivity) (by positivity)
    · -- sum_i x_i / l = 1 because sum_i x_i = l
      sorry⟩

instance TT.CoestdSimplex : CoeOut (TT n l) (stdSimplex Real (Fin n)) where
  coe := TTtostdSimplex

-- Coordinate-indexed lexicographic order used to instantiate Scarf.
abbrev TT.Ilt (i : Fin n) (x y : TT n l) : Prop :=
  toLex (x i, x) < toLex (y i, y)

instance TT.ILO : IndexedLOrder (Fin n) (TT n l) where
  IST := fun i => linearOrderOfSTO (TT.Ilt i)

-- Grid coloring induced by a continuous self-map of the simplex.
def Fcolor
    (f : stdSimplex Real (Fin n) -> stdSimplex Real (Fin n))
    (x : TT n l) : Fin n :=
  stdSimplex.pick x (f x)

-- At grid level l' + 1, Scarf gives a colorful room for Fcolor.
def room_seq
    (f : stdSimplex Real (Fin n) -> stdSimplex Real (Fin n))
    (l' : Nat) :=
  -- A member of the colorful-cell filter returned by Scarf.
  Classical.choice (IndexedLOrder.Scarf (c := Fcolor f))

-- Pick an actual grid point from the colorful room.
def room_point_seq
    (f : stdSimplex Real (Fin n) -> stdSimplex Real (Fin n))
    (l' : Nat) :=
  pick_colorful_point (Finset.mem_filter.mp (room_seq f l').2).2

-- Subsequence packages used in the limit proof.
def gpkg
    (f : stdSimplex Real (Fin n) -> stdSimplex Real (Fin n)) :=
  Classical.choice (constant_index_set_nonempty f)

abbrev g1
    (f : stdSimplex Real (Fin n) -> stdSimplex Real (Fin n)) :=
  (gpkg f).1.2

def hpkg
    (f : stdSimplex Real (Fin n) -> stdSimplex Real (Fin n)) :=
  Classical.choice (hpkg_aux f)
