# qwen3:8b brouwerbench_v1 Report

## Summary

- Model: `qwen3:8b`
- Dataset: `data/brouwerbench_v1.jsonl`
- Raw results: `results/brouwerbench_v1__qwen3_8b.jsonl`
- Manual scores: `scores/brouwerbench_v1__qwen3_8b.manual.jsonl`
- Tasks: 54
- Score: 69/108 (63.9%)
- Total elapsed: 256.40s
- Average elapsed per task: 4.75s
- Decode speed: 41.53 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 16 | 21/32 | 65.6% |
| Brouwer | 15 | 17/30 | 56.7% |
| Brouwer_product | 11 | 14/22 | 63.6% |
| Nash | 12 | 17/24 | 70.8% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 5 | 5/10 | 50.0% |
| proof_dependency | 17 | 26/34 | 76.5% |
| parity_argument | 3 | 3/6 | 50.0% |
| theorem_summary | 3 | 3/6 | 50.0% |
| construction_role | 11 | 16/22 | 72.7% |
| analysis_step | 8 | 9/16 | 56.2% |
| endpoint_connection | 7 | 7/14 | 50.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 1/2 | Gets the cell/room/door cardinality hierarchy right, but states dominance imprecisely. |
| `scarf_002` | Scarf | proof_dependency | 2/2 | Correctly connects minima, image representation, and cardinality control. |
| `scarf_003` | Scarf | definition_role | 1/2 | Distinguishes point insertion and color insertion, but does not explain the incidence-counting role. |
| `scarf_004` | Scarf | definition_role | 1/2 | Explains image, missing color, and typed missing color, but only gestures at counting rather than the fixed-type parity role. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Identifies room_of_colorful as prerequisite structure for picking a point, but misses the nonempty/cardinality sandwich. |
| `scarf_006` | Scarf | parity_argument | 1/2 | Recognizes door-room incidences and outside/internal parity, but misses the non-colorful-room side and colorful-room oddness. |
| `scarf_007` | Scarf | proof_dependency | 2/2 | Correctly identifies the singleton outside-door filter and odd cardinality. |
| `scarf_008` | Scarf | parity_argument | 1/2 | Mentions odd/even parity and existence, but does not state the exact colorful-room count forced to be odd and nonempty. |
| `scarf_009` | Scarf | theorem_summary | 1/2 | States the colorful-cell conclusion, but gives the wrong reason for Inhabited I and misses the default type in typed_colorful_room_odd. |
| `brouwer_001` | Brouwer | construction_role | 2/2 | Correctly explains Fcolor on grids, Scarf colorful rooms, room_seq, and room_point_seq. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Understands finite-image subsequence extraction, but treats the stabilized object as a coloring rather than the room color set C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Correctly says outside-C coordinates tend to zero, but misses how this pairs with coordinate inequalities to force equality. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Identifies compactness as giving a convergent subsequence, but misstates vanishing diameter as directly giving a fixed point. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Captures the broad finite-to-limit bridge, but does not clearly explain the per-color witness and transfer of x_i <= f(x)_i. |
| `brouwer_006` | Brouwer | theorem_summary | 1/2 | Gives the top-level limiting strategy, but misses Scarf/coloring details and treats key lemmas too generically. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Explains deficit/tPush/pushTowardsZ as a retraction device, but does not clearly state positivity of block sums for normalization. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | States projection-after-embedding identity, but misses the exact lifted-map and project-back mechanism. |
| `product_003` | Brouwer_product | theorem_summary | 1/2 | Mentions f_lifted and continuity, but incorrectly describes applying Brouwer in product space and omits project_embed_id at the endpoint. |
| `nash_001` | Nash | definition_role | 1/2 | Mentions finite games and mixed_g, but misses mixedS structure and the unilateral-deviation Nash condition. |
| `nash_002` | Nash | construction_role | 1/2 | Explains normalization and continuity for fixed points, but does not clearly identify payoff-improvement weights. |
| `nash_003` | Nash | endpoint_connection | 1/2 | Connects Brouwer.mixedGame and fixed point broadly, but misses profitable pure deviations and mixed_g_linear. |
| `scarf_010` | Scarf | proof_dependency | 1/2 | Gets the two-rooms-even intuition, but misses the fiber-over-door packaging in dbcountingset. |
| `scarf_011` | Scarf | proof_dependency | 2/2 | Correctly states the typed nearly colorful versus colorful dichotomy with the same missing type. |
| `scarf_012` | Scarf | parity_argument | 1/2 | Identifies two doors and evenness, but does not explain the two-element fiber in dbcountingset. |
| `brouwer_007` | Brouwer | construction_role | 2/2 | Correctly describes TT finite grids, division by l, and indexed orders for Scarf. |
| `brouwer_008` | Brouwer | analysis_step | 1/2 | Recognizes coordinate bounds and diameter control, but misstates the roles of size_bound_in/out and misses outside-C vanishing. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Identifies a constant-C subsequence, but misses the outside-C and inside-C coordinate estimates that require stabilization. |
| `brouwer_010` | Brouwer | analysis_step | 1/2 | Names the final coordinate lemmas, but misstates outside-C zero and does not cleanly explain the sum-one/extensionality argument. |
| `product_004` | Brouwer_product | construction_role | 1/2 | Explains flat-to-block indexing, but misses inverse lemmas and sum-changing as the key formal role. |
| `product_005` | Brouwer_product | construction_role | 1/2 | Connects scaling to blockWeight and project_embed_id, but misses the sum-to-one preservation argument. |
| `product_006` | Brouwer_product | proof_dependency | 2/2 | Correctly identifies division by blockSum, positivity/nonzero denominator, and continuity of projection. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Recognizes the case split for positivity, but gets the tPush = 0 branch wrong and misses zero deficit. |
| `nash_004` | Nash | proof_dependency | 2/2 | Correctly explains mixed_g_linear as a weighted-sum reduction from mixed deviations to pure deviations. |
| `nash_005` | Nash | construction_role | 1/2 | Captures representation transport broadly, but omits Fintype.equivFin, map_simplex, and the precise ProductSimplices shape. |
| `nash_006` | Nash | construction_role | 2/2 | Correctly explains nonnegative g_function values, denominator at least one, normalization, and nash_map_cert. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Mentions self_div_lemma and no pure deviations, but misses the sum_g > 1 versus fixed-point normalization contradiction. |
| `scarf_013` | Scarf | proof_dependency | 2/2 | Correctly characterizes outside doors as empty tau with singleton color and explains uniqueness for counting. |
| `scarf_014` | Scarf | proof_dependency | 2/2 | Correctly explains that the two-room incidence becomes a size-two fiber and hence an even count. |
| `scarf_015` | Scarf | proof_dependency | 2/2 | Correctly combines outside-door-to-nearly-colorful and adjacent-room classification into the typed parity setup. |
| `scarf_016` | Scarf | endpoint_connection | 0/2 | Confuses an odd filtered set with an element of colorful; misses positive cardinality, nonemptiness, choice, and default. |
| `brouwer_011` | Brouwer | construction_role | 2/2 | Correctly explains stdSimplex.pick selecting a coordinate/color with x_i <= f(x)_i. |
| `brouwer_012` | Brouwer | proof_dependency | 1/2 | Mentions fixed C and subsequence, but misses outside-C vanishing and inside-C coordinate inequalities. |
| `brouwer_013` | Brouwer | analysis_step | 1/2 | Identifies y_seq as carrying finite inequalities through diameter and continuity, but misses the colored-witness role and z-specific limit. |
| `brouwer_014` | Brouwer | analysis_step | 1/2 | Mentions outside-C zero, nonnegativity, and sum one, but does not explain how they force outside mass zero and coordinate equality. |
| `brouwer_015` | Brouwer | endpoint_connection | 0/2 | Misdescribes C as a compact subset and says z lies outside C; misses the inside/outside coordinate split. |
| `product_008` | Brouwer_product | proof_dependency | 2/2 | Correctly explains why the tPush = 0 branch needs zero deficit and blockWeight positivity. |
| `product_009` | Brouwer_product | analysis_step | 2/2 | Correctly identifies the blockSum denominator, continuity, and nonzero/positive denominator problem. |
| `product_010` | Brouwer_product | construction_role | 1/2 | Mentions block sums matching block weights and identity, but does not clearly state deficit zero, push identity, and recovery of y. |
| `product_011` | Brouwer_product | endpoint_connection | 1/2 | Explains BigSimplex, projection back, and project_embed_id, but omits the lifted map f_lifted. |
| `nash_008` | Nash | construction_role | 1/2 | Correctly identifies positive payoff improvement from a pure deviation, but omits normalization into nash_map weights. |
| `nash_009` | Nash | analysis_step | 1/2 | Explains positive denominator and nonnegative normalized coordinates, but omits nash_map_cert and the explicit sum-one proof. |
| `nash_010` | Nash | endpoint_connection | 2/2 | Correctly explains mixed_g_linear as a weighted-sum bridge from pure to mixed deviations. |
| `nash_011` | Nash | endpoint_connection | 2/2 | Correctly states the contradiction between H1's sum_g > 1 and self_div_lemma forcing sum_g = 1 at a fixed point. |
| `nash_012` | Nash | construction_role | 2/2 | Correctly explains reindexing via phi/phi_inv into ProductSimplices to apply Brouwer_Product and transport the fixed point back. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
