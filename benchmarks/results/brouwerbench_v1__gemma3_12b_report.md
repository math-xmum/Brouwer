# gemma3:12b brouwerbench_v1 Report

## Summary

- Model: `gemma3:12b`
- Dataset: `benchmarks/data/brouwerbench_v1.jsonl`
- Raw results: `benchmarks/results/brouwerbench_v1__gemma3_12b.jsonl`
- Manual scores: `benchmarks/scores/brouwerbench_v1__gemma3_12b.manual.jsonl`
- Tasks: 54
- Score: 63/108 (58.3%)
- Total elapsed: 459.24s
- Average elapsed per task: 8.50s
- Decode speed: 27.09 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 16 | 19/32 | 59.4% |
| Brouwer | 15 | 16/30 | 53.3% |
| Brouwer_product | 11 | 15/22 | 68.2% |
| Nash | 12 | 13/24 | 54.2% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 3/10 | 30.0% |
| proof_dependency | 17 | 24/34 | 70.6% |
| parity_argument | 3 | 3/6 | 50.0% |
| theorem_summary | 3 | 2/6 | 33.3% |
| construction_role | 11 | 14/22 | 63.6% |
| analysis_step | 8 | 9/16 | 56.2% |
| endpoint_connection | 7 | 8/14 | 57.1% |

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
| `scarf_009` | Scarf | theorem_summary | 0/2 | Misstates the theorem as a tautological existence claim and gives an incorrect reason for Inhabited I/default. |
| `brouwer_001` | Brouwer | construction_role | 1/2 | Connects Scarf to grid-level colorful rooms and room_point_seq, but does not explain the Fcolor coordinate choice. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Mentions a finite-image constant subsequence, but confuses colors with the room index set and misses why fixed C is needed for estimates. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Correctly says outside-C coordinates tend to zero, but does not connect this to inequalities on C and the final simplex equality. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness and vanishing diameter, but only vaguely explains how diameter transfers room-level inequalities to the limit. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Mentions coordinate inequalities and limiting behavior, but misses the colored witnesses and continuity/diameter transfer mechanism. |
| `brouwer_006` | Brouwer | theorem_summary | 1/2 | Uses some formal names and convergence language, but omits the discretization, Scarf colorful rooms, and shrinking-diameter bridge. |
| `product_001` | Brouwer_product | definition_role | 0/2 | Mentions pushing toward the uniform point, but misses block deficits, positive block sums, and projection normalization. |
| `product_002` | Brouwer_product | proof_dependency | 2/2 | Correctly identifies projection after embedding as the left inverse/retraction needed to convert the lifted fixed point into a product fixed point. |
| `product_003` | Brouwer_product | theorem_summary | 1/2 | Describes the lifted map and continuity, but omits the projection-back and project_embed_id retraction step. |
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
| `brouwer_012` | Brouwer | proof_dependency | 1/2 | Identifies fixed C and subsequence g1, but omits their later inside-C/outside-C proof roles. |
| `brouwer_013` | Brouwer | analysis_step | 1/2 | Identifies y_seq as a colored witness idea, but does not clearly explain the y_i <= f(y)_i inequality and transfer to z by diameter plus continuity. |
| `brouwer_014` | Brouwer | analysis_step | 1/2 | Mentions outside-C zero and nonnegativity, but does not reconstruct the sum-one mass argument that forces coordinate equality. |
| `brouwer_015` | Brouwer | endpoint_connection | 1/2 | Names the two endpoint roles of C, but does not explain how the inside/outside split yields extensional equality f z = z. |
| `product_008` | Brouwer_product | proof_dependency | 1/2 | Mentions positivity and blockWeight, but misses why zero deficit is needed when the positive push term vanishes. |
| `product_009` | Brouwer_product | analysis_step | 2/2 | Correctly identifies division by blockSum and the need for positivity/nonzero denominator in project_continuous. |
| `product_010` | Brouwer_product | construction_role | 2/2 | Correctly connects embedded block sums to deficit zero, push identity, and recovery of y by projection. |
| `product_011` | Brouwer_product | endpoint_connection | 2/2 | Correctly explains applying single-simplex Brouwer to f_lifted on BigSimplex, projecting back, and using project_embed_id. |
| `nash_008` | Nash | construction_role | 2/2 | Correctly identifies max 0 as the positive payoff-improvement term from pure deviations, giving nonnegative weights for normalization. |
| `nash_009` | Nash | analysis_step | 1/2 | Explains denominator positivity from one_le_sum_g, but misses nonnegativity and the sum-one/nash_map_cert packaging. |
| `nash_010` | Nash | endpoint_connection | 1/2 | Mentions linearity and pure strategies, but not the weighted-sum bound showing pure-deviation bounds imply mixed-deviation bounds. |
| `nash_011` | Nash | endpoint_connection | 2/2 | Correctly states the contradiction between H1's sum_g > 1 and fixedness/self_div_lemma forcing sum_g = 1. |
| `nash_012` | Nash | construction_role | 1/2 | Recognizes reindexing via phi/phi_inv for fixed-point transport, but misstates the issue as infinite-dimensional and misses ProductSimplices. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
