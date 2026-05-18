-- Section prelude excerpt for BrouwerBench prompts.
-- This is prompt context, not a standalone Lean file.

structure Game where
  I : Type*
  HI : Inhabited I
  SS : I -> Type*
  HSS : (i : I) -> Inhabited (SS i)
  g : I -> ((i : I) -> SS i) -> Real

attribute [instance] Game.HI Game.HSS

namespace Game

def NashEquilibrium (G : Game) (x : (i : G.I) -> G.SS i) : Prop :=
  forall (i : G.I) (y : (i : G.I) -> G.SS i),
    (forall j : G.I, i != j -> x j = y j) ->
    G.g i x >= G.g i y

end Game

structure FinGame extends Game where
  FinI : Fintype I
  FinSS : (i : I) -> Fintype (SS i)

attribute [instance] FinGame.FinI FinGame.FinSS

namespace FinGame

abbrev mixedS (G : FinGame) :=
  (i : G.I) -> stdSimplex Real (G.SS i)

def mixed_g (G : FinGame) (i : G.I) (m : (i : G.I) -> stdSimplex Real (G.SS i)) : Real :=
  sum s : ((j : G.I) -> G.SS j),
    (prod j, m j (s j)) * (G.g i s)

def mixedNashEquilibrium (G : FinGame) (x : G.mixedS) : Prop :=
  forall (i : G.I), forall (y : stdSimplex Real (G.SS i)),
    G.mixed_g i x >= G.mixed_g i (Function.update x i y)

noncomputable abbrev g_function
    (G : FinGame) (i : G.I) (sigma : G.mixedS) (a : G.SS i) : Real :=
  sigma i a +
  max 0 (G.mixed_g i (Function.update sigma i (stdSimplex.pure a)) -
         G.mixed_g i sigma)

noncomputable abbrev nash_map_aux
    (G : FinGame) (sigma : G.mixedS) (i : G.I) (a : G.SS i) : Real :=
  g_function G i sigma a /
  sum b : G.SS i, g_function G i sigma b

noncomputable def nash_map (G : FinGame) (sigma : G.mixedS) : G.mixedS :=
  fun i => ⟨nash_map_aux G sigma i, nash_map_cert sigma i⟩

end FinGame
