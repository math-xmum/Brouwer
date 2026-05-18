-- Section prelude excerpt for BrouwerBench prompts.
-- This is prompt context, not a standalone Lean file.

class IndexedLOrder (I T : Type*) where
  IST : I -> LinearOrder T

-- Local notation in Gametheory/Scarf.lean:
--   lhs <[i] rhs  means (IST i).lt lhs rhs
--   lhs <=[i] rhs means (IST i).le lhs rhs

namespace IndexedLOrder

variable {T : Type*} [Inhabited T]
variable {I : Type*} [IST : IndexedLOrder I T]
variable (sigma : Finset T) (C : Finset I)

def isDominant : Prop :=
  forall y, exists i in C, forall x in sigma, y <=[i] x

abbrev mini {sigma : Finset T} (h2 : sigma.Nonempty) (i : I) : T :=
  @Finset.min' _ (IST i) _ h2

abbrev isCell : Prop :=
  isDominant sigma C

abbrev isRoom : Prop :=
  isCell sigma C /\ C.card = sigma.card

abbrev isDoor : Prop :=
  isCell sigma C /\ C.card = sigma.card + 1

abbrev isOutsideDoor (tau : Finset T) (D : Finset I) : Prop :=
  IST.isDoor tau D /\ tau = Finset.empty

abbrev isInternalDoor (tau : Finset T) (D : Finset I) : Prop :=
  IST.isDoor tau D /\ tau.Nonempty

variable [DecidableEq T] [DecidableEq I]

inductive isDoorof
    (tau : Finset T) (D : Finset I) (sigma : Finset T) (C : Finset I) : Prop
  | idoor
      (h0 : isCell sigma C) (h1 : isDoor tau D)
      (x : T) (hx : x notin tau) (hins : insert x tau = sigma) (hD : D = C)
  | odoor
      (h0 : isCell sigma C) (h1 : isDoor tau D)
      (j : I) (hj : j notin C) (htau : tau = sigma) (hD : D = insert j C)

variable (c : T -> I) (sigma : Finset T) (C : Finset I)

def isColorful : Prop :=
  IST.isCell sigma C /\ sigma.image c = C

def isNearlyColorful : Prop :=
  IST.isCell sigma C /\ (C \ sigma.image c).card = 1

def isTypedNC (i : I) (sigma : Finset T) (C : Finset I) : Prop :=
  IST.isCell sigma C /\ (C \ sigma.image c) = {i}

abbrev colorful : Finset (Finset T × Finset I) :=
  Finset.filter (fun x => IST.isColorful c x.1 x.2) Finset.univ

abbrev dbcountingset (i : I) :
    Finset ((Finset T × Finset I) × (Finset T × Finset I)) :=
  Finset.filter
    (fun x =>
      isTypedNC c i x.1.1 x.1.2 /\
      isDoorof x.1.1 x.1.2 x.2.1 x.2.2)
    Finset.univ

end IndexedLOrder
