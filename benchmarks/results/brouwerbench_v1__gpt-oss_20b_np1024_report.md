# gpt-oss:20b brouwerbench_v1 Report

## Summary

- Model: `gpt-oss:20b`
- Dataset: `benchmarks/data/brouwerbench_v1.jsonl`
- Raw results: `benchmarks/results/brouwerbench_v1__gpt-oss_20b_np1024.jsonl`
- Manual scores: `benchmarks/scores/brouwerbench_v1__gpt-oss_20b_np1024.manual.jsonl`
- Tasks: 54
- Score: 81/108 (75.0%)
- Total elapsed: 880.62s
- Average elapsed per task: 16.31s
- Decode speed: 46.98 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 16 | 27/32 | 84.4% |
| Brouwer | 15 | 21/30 | 70.0% |
| Brouwer_product | 11 | 16/22 | 72.7% |
| Nash | 12 | 17/24 | 70.8% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 7/10 | 70.0% |
| proof_dependency | 17 | 27/34 | 79.4% |
| parity_argument | 3 | 5/6 | 83.3% |
| theorem_summary | 3 | 4/6 | 66.7% |
| construction_role | 11 | 19/22 | 86.4% |
| analysis_step | 8 | 10/16 | 62.5% |
| endpoint_connection | 7 | 9/14 | 64.3% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 2/2 | Correctly explains dominance, cell/room/door hierarchy, and cardinality conditions. |
| `scarf_002` | Scarf | proof_dependency | 1/2 | Identifies the minimum-image/cardinality-bound role, but incorrectly suggests image gives a bijection/cardinality equality. |
| `scarf_003` | Scarf | definition_role | 1/2 | Explains point insertion and index insertion, but does not connect the constructors to incidence counting. |
| `scarf_004` | Scarf | definition_role | 2/2 | Correctly distinguishes colorful, nearly colorful, and typed missing-color predicates and connects typedness to counting. |
| `scarf_005` | Scarf | proof_dependency | 2/2 | Correctly explains that room_of_colorful supplies room/cardinality/nonempty structure needed for pick_colorful_point. |
| `scarf_006` | Scarf | parity_argument | 1/2 | Recognizes incidence counting and outside/internal parity, but the partition and typed_colorful_room_odd role are imprecise. |
| `scarf_007` | Scarf | proof_dependency | 2/2 | Correctly explains the singleton outside-door filter and odd cardinality. |
| `scarf_008` | Scarf | parity_argument | 2/2 | Correctly identifies parity_lemma as the arithmetic step forcing an odd, hence nonempty, colorful-room count. |
| `scarf_009` | Scarf | theorem_summary | 2/2 | Correctly states colorful nonemptiness and explains the use of Inhabited I/default for typed_colorful_room_odd. |
| `brouwer_001` | Brouwer | construction_role | 2/2 | Correctly connects Fcolor on finite grids, Scarf colorful rooms, room_seq, and room_point_seq. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Understands finite-image subsequence extraction, but treats the stabilized object as a single color rather than the room color set C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Correctly notes outside-C coordinates tend to zero, but does not explain how this pairs with inside-C inequalities to force the fixed point. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Identifies compactness and shrinking diameter, but overstates diameter as giving common-room membership rather than transferring inequalities. |
| `brouwer_005` | Brouwer | proof_dependency | 2/2 | Correctly explains the finite colored-witness inequality and its passage to the limit using continuity. |
| `brouwer_006` | Brouwer | theorem_summary | 1/2 | Covers grid/Scarf/subsequence at a high level, but the answer is truncated before the full diameter/continuity/sum argument. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Explains deficit/tPush/pushTowardsZ as block correction, but misses that the key goal is positive block sums for normalization. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | States the projection-embedding retraction role, but only gestures at the lifted map and project-back fixed-point transfer. |
| `product_003` | Brouwer_product | theorem_summary | 1/2 | Mentions f_lifted, continuity, Brouwer, and projection back, but uses the retraction identity in the wrong direction. |
| `nash_001` | Nash | definition_role | 1/2 | Describes finite mixed strategies and expected payoff, but omits the unilateral-deviation Nash condition. |
| `nash_002` | Nash | construction_role | 1/2 | Explains normalization, continuity, and fixed points, but does not clearly identify payoff-improvement weights. |
| `nash_003` | Nash | endpoint_connection | 1/2 | Connects Brouwer.mixedGame and a fixed point of nash_map, but misses the pure-deviation contradiction and mixed_g_linear extension. |
| `scarf_010` | Scarf | proof_dependency | 2/2 | Correctly connects internal doors, two incident rooms, size-two fibers, and evenness. |
| `scarf_011` | Scarf | proof_dependency | 2/2 | Correctly states the typed nearly colorful versus colorful partition with the same missing type. |
| `scarf_012` | Scarf | parity_argument | 2/2 | Correctly explains two nearly colorful doors, the size-two fiber, and even incidence contribution. |
| `brouwer_007` | Brouwer | construction_role | 2/2 | Correctly explains TT finite grids, division by l, and indexed orders for Scarf. |
| `brouwer_008` | Brouwer | analysis_step | 1/2 | Recognizes quantitative grid estimates, but misstates size_bound_in/out and misses the outside-C role. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Explains stabilizing a constant C subsequence, but misses the outside-C vanishing and inside-C inequalities that require it. |
| `brouwer_010` | Brouwer | analysis_step | 2/2 | Correctly explains outside-C zero, sum-one constraints, coordinate inequalities, and extensionality. |
| `product_004` | Brouwer_product | construction_role | 2/2 | Correctly explains flat indices, block/local indices, inverse lemmas, and their role in blockwise constructions. |
| `product_005` | Brouwer_product | construction_role | 2/2 | Correctly explains blockWeight scaling, sum-to-one preservation, block sums, and project_embed_id. |
| `product_006` | Brouwer_product | proof_dependency | 2/2 | Correctly identifies division by blockSum, continuity of numerator/denominator, positive denominator, and division continuity. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Recognizes the tPush case split and blockWeight positivity, but gets the tPush=0 branch wrong by missing zero deficit. |
| `nash_004` | Nash | proof_dependency | 2/2 | Correctly explains mixed_g_linear as the convex-combination bridge from pure to mixed deviations. |
| `nash_005` | Nash | construction_role | 1/2 | Captures representation transport broadly, but misses Fintype.equivFin/ProductSimplices and gives an inaccurate single-simplex description. |
| `nash_006` | Nash | construction_role | 2/2 | Correctly explains g_function nonnegativity, denominator at least one, normalization, and nash_map_cert. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Mentions H1 and fixed-point contradiction, but the explanation of self_div_lemma and the contradiction is not correct. |
| `scarf_013` | Scarf | proof_dependency | 2/2 | Correctly characterizes outside doors as empty tau with singleton color and uniqueness for the count. |
| `scarf_014` | Scarf | proof_dependency | 2/2 | Correctly explains that internal_door_two_rooms becomes a size-two fiber and hence an even contribution. |
| `scarf_015` | Scarf | proof_dependency | 2/2 | Correctly explains NC_of_outsidedoor and NC_or_C_of_door as the typed parity classification bridge. |
| `scarf_016` | Scarf | endpoint_connection | 0/2 | Incorrectly treats typed nearly colorful as colorful and misses odd cardinality, positive cardinality, choice, and default. |
| `brouwer_011` | Brouwer | construction_role | 2/2 | Correctly explains stdSimplex.pick selecting a coordinate/color with x_i <= f(x)_i. |
| `brouwer_012` | Brouwer | proof_dependency | 1/2 | Explains fixed C and subsequence g1, but misses outside-C vanishing and inside-C coordinate inequalities. |
| `brouwer_013` | Brouwer | analysis_step | 1/2 | Explains y_seq as carrying finite inequalities through diameter and continuity, but does not identify the colored witness role clearly. |
| `brouwer_014` | Brouwer | analysis_step | 1/2 | Mentions outside-C zero, nonnegativity, and sum one, but does not clearly explain how equality of sums forces coordinate equality. |
| `brouwer_015` | Brouwer | endpoint_connection | 2/2 | Correctly explains C's inside-C inequality role, outside-C zero role, and the extensionality endpoint. |
| `product_008` | Brouwer_product | proof_dependency | 1/2 | Identifies why tPush=0 loses the positive push term, but misses the zero-deficit argument that gives blockWeight <= blockSum. |
| `product_009` | Brouwer_product | analysis_step | 2/2 | Correctly identifies the blockSum denominator, nonzero positivity, and division-continuity issue. |
| `product_010` | Brouwer_product | construction_role | 2/2 | Correctly explains embedded block sums, blockWeight, deficit zero, push identity, and recovery of y. |
| `product_011` | Brouwer_product | endpoint_connection | 1/2 | Mentions BigSimplex, f_lifted, projection back, and project_embed_id, but misnames the applied theorem on the lifted map. |
| `nash_008` | Nash | construction_role | 1/2 | Correctly identifies positive payoff improvement from a pure deviation, but omits normalization into nash_map weights. |
| `nash_009` | Nash | analysis_step | 1/2 | Explains denominator positivity, nonnegativity, and sum one, but omits nash_map_cert packaging. |
| `nash_010` | Nash | endpoint_connection | 2/2 | Correctly explains mixed_g_linear as a weighted-sum bridge from pure to arbitrary mixed deviations. |
| `nash_011` | Nash | endpoint_connection | 2/2 | Correctly states H1's sum_g > 1 contradiction with self_div_lemma forcing sum_g = 1 at a fixed point. |
| `nash_012` | Nash | construction_role | 2/2 | Correctly explains reindexing via phi/phi_inv into ProductSimplices and transporting the fixed point back. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
