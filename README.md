# Game Theory Formalization in Lean

This repository contains a formalization of fundamental theorems in game theory using the Lean proof assistant. The main goal is to prove the existence of Nash Equilibria in finite games.

## Core Concepts and Theorems

The proof of Nash's theorem relies on Brouwer's fixed-point theorem. This repository builds up the necessary mathematical framework from scratch.

### Files

-   `Gametheory/Simplex1.lean`: Defines the standard simplex (`stdSimplex`), which represents the space of mixed strategies for a player.
-   `Gametheory/Scarf.lean`: Provides the formalization of Scarf's Lemma, a combinatorial result used for a constructive proof of Brouwer's fixed-point theorem.
-   `Gametheory/Brouwer.lean`: Proves Brouwer's fixed-point theorem for a single simplex, using the machinery from `Scarf.lean`.
-   `Gametheory/Brouwer_product.lean`: Extends Brouwer's theorem to a product of simplices (`Brouwer_Product`), which is the space of strategy profiles for all players in a game.
-   `Gametheory/Nash.lean` & `Gametheory/Nash1.lean`: Defines finite games (`FinGame`) and Nash Equilibrium (`NashEquilibrium`). It then uses `Brouwer_Product` to prove the main result: the existence of a mixed strategy Nash Equilibrium (`ExistsNashEq`) for any finite game.

## Proof Strategy

1.  **Simplex Definition**: Start by defining the mathematical space for probabilities, the simplex.
2.  **Brouwer's Fixed-Point Theorem**:
    -   Prove Scarf's Lemma, a combinatorial result.
    -   Use Scarf's Lemma to give a constructive proof of Brouwer's theorem for a single simplex.
    -   Generalize the theorem to a product of simplices using a retraction argument.
3.  **Nash's Theorem**:
    -   Define a finite game, players, strategies, and payoffs.
    -   Define the concept of a mixed strategy Nash Equilibrium.
    -   Construct a continuous function (the `nash_map`) from the space of strategy profiles to itself.
    -   Show that a fixed point of this function is a Nash Equilibrium.
    -   Apply the Brouwer's fixed-point theorem for product spaces to guarantee the existence of such a fixed point.

## References

-   The formalizations of Scarf's Lemma (`Gametheory/Scarf.lean`) and Brouwer's fixed-point theorem (`Gametheory/Brouwer.lean`, `Gametheory/Brouwer_product.lean`) are based on Nikolai V. Ivanov, "Beyond Sperner's Lemma".
-   For Nash's theorem, the reference is John Nash, "Non-Cooperative Games" (1951).

