# gemma3:12b brouwerbench_v1 Report

## Summary

- Model: `gemma3:12b`
- Dataset: `data/brouwerbench_v1.jsonl`
- Raw results: `results/brouwerbench_v1__gemma3_12b.jsonl`
- Manual scores: `scores/brouwerbench_v1__gemma3_12b.manual.jsonl`
- Tasks: 80
- Score: 89/160 (55.6%)
- Total elapsed: 822.82s
- Average elapsed per task: 10.29s
- Decode speed: 22.42 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 24 | 25/48 | 52.1% |
| Brouwer | 20 | 21/40 | 52.5% |
| Brouwer_product | 18 | 24/36 | 66.7% |
| Nash | 18 | 19/36 | 52.8% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 7 | 5/14 | 35.7% |
| proof_dependency | 28 | 34/56 | 60.7% |
| parity_argument | 4 | 5/8 | 62.5% |
| theorem_summary | 3 | 4/6 | 66.7% |
| construction_role | 17 | 20/34 | 58.8% |
| analysis_step | 11 | 11/22 | 50.0% |
| endpoint_connection | 10 | 10/20 | 50.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 1/2 | Defines dominance, cells, rooms, and doors accurately, but does not connect the refinements to the room-door parity setup. |
| `scarf_002` | Scarf | proof_dependency | 1/2 | Identifies the minimum-image representation, but does not explicitly derive sigma.card <= C.card or its later cardinality role. |
| `scarf_003` | Scarf | definition_role | 1/2 | Distinguishes the point-insertion and color-insertion constructors, but omits their door-room incidence-counting role. |
| `scarf_004` | Scarf | definition_role | 1/2 | Explains colorful, nearly colorful, and typed missing color, but misses the fixed-type parity-counting purpose. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Mentions colorful implies room and point extraction, but not the nonempty/cardinality sandwich needed for pick_colorful_point. |
| `scarf_006` | Scarf | parity_argument | 1/2 | Identifies typed door-room incidences and outside/internal parity, but misses the room-side split into colorful versus non-colorful rooms. |
| `scarf_007` | Scarf | proof_dependency | 2/2 | Correctly explains that the outside-door filter is a singleton and hence has odd cardinality. |
| `scarf_008` | Scarf | parity_argument | 1/2 | States that parity gives oddness of the colorful-room filter, but does not explain the odd-plus-even count equation or nonemptiness extraction. |
| `scarf_009` | Scarf | theorem_summary | 1/2 | States existence of a colorful cell, but treats default/Inhabited only vaguely and does not explain odd-cardinality extraction. |
| `brouwer_001` | Brouwer | construction_role | 1/2 | Connects Scarf to grid-level colorful rooms and room_point_seq, but does not explain the Fcolor coordinate choice. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Mentions a finite-image constant subsequence, but confuses colors with the room index set and misses why fixed C is needed for estimates. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Correctly says outside-C coordinates tend to zero, but does not connect this to inequalities on C and the final simplex equality. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness and vanishing diameter, but only vaguely explains how diameter transfers room-level inequalities to the limit. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Mentions coordinate inequalities and limiting behavior, but misses the colored witnesses and continuity/diameter transfer mechanism. |
| `brouwer_006` | Brouwer | theorem_summary | 1/2 | Mentions convergence, subsequence, and diameter packages, but misses Scarf/coloring and the continuity transfer. |
| `product_001` | Brouwer_product | definition_role | 0/2 | Mentions pushing toward the uniform point, but misses block deficits, positive block sums, and projection normalization. |
| `product_002` | Brouwer_product | proof_dependency | 2/2 | Correctly identifies projection after embedding as the left inverse/retraction needed to convert the lifted fixed point into a product fixed point. |
| `product_003` | Brouwer_product | theorem_summary | 2/2 | Gives the lifted map, continuity composition, Brouwer fixed point, projection back, and project_embed_id endpoint. |
| `nash_001` | Nash | definition_role | 0/2 | Only describes finite players and pure strategy types; it misses mixed profiles as products of simplices, expected payoff, and no-deviation. |
| `nash_002` | Nash | construction_role | 1/2 | Explains normalization and continuity for Brouwer, but does not clearly identify the payoff-improvement construction. |
| `nash_003` | Nash | endpoint_connection | 1/2 | Mentions a fixed point of nash_map leading to mixedNashEquilibrium, but misses pure-deviation contradiction and mixed_g_linear. |
| `scarf_010` | Scarf | proof_dependency | 2/2 | Correctly connects internal_door_two_rooms to size-two fibers and even internal-door contribution. |
| `scarf_011` | Scarf | proof_dependency | 1/2 | Recognizes the nearly-colorful/colorful dichotomy, but does not preserve the same typed missing color through the incidence. |
| `scarf_012` | Scarf | parity_argument | 1/2 | Mentions two doors/fibers for non-colorful nearly colorful rooms, but incorrectly suggests the whole dbcountingset has cardinality 2. |
| `brouwer_007` | Brouwer | construction_role | 2/2 | Correctly explains TT as the finite integer grid, TTtostdSimplex division by l, and indexed orders for Scarf. |
| `brouwer_008` | Brouwer | analysis_step | 1/2 | Mentions coordinate bounds and the two named limit lemmas, but does not clearly explain rescaling to diameter shrinkage and outside-C vanishing. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Explains extracting a subsequence with constant C, but not how fixed C supports outside-C and inside-C estimates. |
| `brouwer_010` | Brouwer | analysis_step | 1/2 | Mentions coordinate inequalities/equality, but bypasses the simplex sum-one argument that forces equality. |
| `product_004` | Brouwer_product | construction_role | 1/2 | Explains flat-to-block indexing, but omits inverse lemmas and their role in block sums and retraction proofs. |
| `product_005` | Brouwer_product | construction_role | 1/2 | Identifies blockWeight scaling, but does not explain whole-simplex sum one and projection recovery. |
| `product_006` | Brouwer_product | proof_dependency | 2/2 | Correctly explains that projection divides by blockSum and needs a positive nonzero denominator for continuity. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Sets up the tPush case split, but misses the zero-deficit argument in the tPush = 0 branch. |
| `nash_004` | Nash | proof_dependency | 1/2 | States the linear decomposition of mixed deviations, but does not explain the convex-average bound from pure deviations. |
| `nash_005` | Nash | construction_role | 2/2 | Explains that reindexing and simplex equivalences transport the finite game space to the Brouwer-compatible representation and back. |
| `nash_006` | Nash | construction_role | 0/2 | Incorrectly says simplex validity is not explicitly proved and relies on continuity, missing nonnegativity, denominator positivity, and sum-one normalization. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Mentions fixedness and inequalities, but not the key contradiction between sum_g > 1 and sum_g = 1. |
| `scarf_013` | Scarf | proof_dependency | 2/2 | Correctly explains outside doors as empty tau with singleton color and the singleton-counting consequence. |
| `scarf_014` | Scarf | proof_dependency | 2/2 | Correctly says the two-room fact is packaged as a size-two fiber, giving even internal-door count. |
| `scarf_015` | Scarf | proof_dependency | 2/2 | Correctly combines outside-door-to-typed-nearly-colorful with classification of adjacent rooms as typed nearly colorful or colorful. |
| `scarf_016` | Scarf | endpoint_connection | 0/2 | Does not explain odd cardinality, positive cardinality/nonempty filter, or default-based extraction of an element. |
| `brouwer_011` | Brouwer | construction_role | 1/2 | Mentions stdSimplex.pick and the coordinate inequality, but gives the wrong reason for existence and adds an irrelevant distinctness claim. |
| `brouwer_012` | Brouwer | proof_dependency | 1/2 | Identifies fixed C and g1 but does not explain inside-C/outside-C coordinate estimates. |
| `brouwer_013` | Brouwer | analysis_step | 1/2 | Identifies y_seq as a colored witness idea, but does not clearly explain the y_i <= f(y)_i inequality and transfer to z by diameter plus continuity. |
| `brouwer_014` | Brouwer | analysis_step | 1/2 | Mentions outside-C zero and nonnegativity, but does not reconstruct the sum-one mass argument that forces coordinate equality. |
| `brouwer_015` | Brouwer | endpoint_connection | 1/2 | Names the two endpoint roles of C, but does not explain how the inside/outside split yields extensional equality f z = z. |
| `product_008` | Brouwer_product | proof_dependency | 1/2 | Mentions positivity and blockWeight, but misses why zero deficit is needed when the positive push term vanishes. |
| `product_009` | Brouwer_product | analysis_step | 2/2 | Correctly identifies division by blockSum and the need for positivity/nonzero denominator in project_continuous. |
| `product_010` | Brouwer_product | construction_role | 2/2 | Correctly connects embedded block sums to deficit zero, push identity, and recovery of y by projection. |
| `product_011` | Brouwer_product | endpoint_connection | 2/2 | Correctly explains applying single-simplex Brouwer to f_lifted on BigSimplex, projecting back, and using project_embed_id. |
| `nash_008` | Nash | construction_role | 2/2 | Correctly identifies max 0 as the positive payoff-improvement term from pure deviations, giving nonnegative weights for normalization. |
| `nash_009` | Nash | analysis_step | 1/2 | Mentions denominator positivity, nonnegativity, and nash_map_cert, but does not clearly establish the sum-one packaging. |
| `nash_010` | Nash | endpoint_connection | 1/2 | Mentions linearity and pure strategies, but not the weighted-sum bound showing pure-deviation bounds imply mixed-deviation bounds. |
| `nash_011` | Nash | endpoint_connection | 2/2 | Identifies self_div_lemma as forcing sum_g = 1 and contradicting H1 sum_g > 1. |
| `nash_012` | Nash | construction_role | 1/2 | Recognizes reindexing via phi/phi_inv for fixed-point transport, but misstates the issue as infinite-dimensional and misses ProductSimplices. |
| `scarf_017` | Scarf | proof_dependency | 1/2 | Mentions subset and superset dominance transfer, but does not connect the two moves to idoor versus odoor. |
| `scarf_018` | Scarf | endpoint_connection | 0/2 | Confuses the door-side cell fact with being a door and states the room lemma as making the door a room. |
| `scarf_019` | Scarf | construction_role | 0/2 | Misstates M_set and m_element as a minimal below-all construction and misses the adjacent-room extension role. |
| `scarf_020` | Scarf | proof_dependency | 0/2 | Treats M_set disjointness as a Finset insertion duplicate issue rather than distinct extension candidates. |
| `scarf_021` | Scarf | proof_dependency | 1/2 | States the image-cardinality alternatives but not the injective or collision door regimes. |
| `scarf_022` | Scarf | proof_dependency | 1/2 | Recognizes propagation of typed near-colorfulness to the door, but misses the typed parity fiber and overstates isDoorof. |
| `scarf_023` | Scarf | parity_argument | 2/2 | Correctly says a nearly colorful room has two incident NC doors and therefore contributes an even pair. |
| `scarf_024` | Scarf | proof_dependency | 0/2 | Replaces the two m_element candidates with an incorrect claim about minima, so exhaustiveness is not explained. |
| `brouwer_016` | Brouwer | construction_role | 1/2 | Mentions TT.Ilt_keyprop and indexed comparison, but misses total-order tie breaking for Scarf. |
| `brouwer_017` | Brouwer | proof_dependency | 1/2 | Connects dominance to estimates broadly, but misstates size_bound_key as a direct simplex-distance bound. |
| `brouwer_018` | Brouwer | construction_role | 1/2 | Explains the discrete-grid to simplex bridge, but omits denominator rescaling and the simplex certificate. |
| `brouwer_019` | Brouwer | analysis_step | 1/2 | Points to outside-C shrinkage but misdescribes the statement as a distance bound independent of l. |
| `brouwer_020` | Brouwer | analysis_step | 1/2 | Explains shrinking rooms near z, but misses the colored-witness transfer to the representative limit. |
| `product_012` | Brouwer_product | definition_role | 0/2 | Misdescribes BigSimplex and ProductSimplices as semi-space intersections rather than flattened versus blockwise simplices. |
| `product_013` | Brouwer_product | construction_role | 2/2 | Correctly identifies the [0,1] bound as the convex-combination condition for pushTowardsZ. |
| `product_014` | Brouwer_product | proof_dependency | 1/2 | Mentions convex block sums before projection, but does not explain positivity of the normalization denominator. |
| `product_015` | Brouwer_product | proof_dependency | 1/2 | Explains positive blockWeight in the push lemmas, but omits its division role in projection. |
| `product_016` | Brouwer_product | construction_role | 1/2 | States division by blockSum, but not the per-block sum-one ProductSimplices result. |
| `product_017` | Brouwer_product | proof_dependency | 2/2 | Correctly links projection and embedding continuity to continuity of the lifted map for Brouwer. |
| `product_018` | Brouwer_product | endpoint_connection | 1/2 | Uses project_embed_id in the endpoint discussion, but the rewrite direction and final expression are not stated correctly. |
| `nash_013` | Nash | definition_role | 2/2 | Correctly states the unilateral mixed-strategy deviation with Function.update and mixed_g payoff. |
| `nash_014` | Nash | construction_role | 1/2 | Mentions mixed_g packaging, but incorrectly says FinGame2MixedGame keeps the original strategy types. |
| `nash_015` | Nash | proof_dependency | 1/2 | Connects cg to quotient continuity for nash_map, but omits denominator-sum and nonzero details. |
| `nash_016` | Nash | proof_dependency | 1/2 | Recognizes a maximizing pure strategy bounds deviations, but omits the weighted-sum argument and H t. |
| `nash_017` | Nash | analysis_step | 0/2 | Misidentifies wsum_magic_ineq as a sigma-versus-g_function inequality and misses the payoff witness. |
| `nash_018` | Nash | endpoint_connection | 1/2 | Recognizes conjugated fixed-point transport, but does not explain the phi inverse identities in G.mixedS. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
