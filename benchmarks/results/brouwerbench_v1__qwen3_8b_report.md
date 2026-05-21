# qwen3:8b brouwerbench_v1 Report

## Summary

- Model: `qwen3:8b`
- Dataset: `data/brouwerbench_v1.jsonl`
- Raw results: `results/brouwerbench_v1__qwen3_8b.jsonl`
- Manual scores: `scores/brouwerbench_v1__qwen3_8b.manual.jsonl`
- Tasks: 80
- Score: 101/160 (63.1%)
- Total elapsed: 428.07s
- Average elapsed per task: 5.35s
- Decode speed: 38.05 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 24 | 30/48 | 62.5% |
| Brouwer | 20 | 22/40 | 55.0% |
| Brouwer_product | 18 | 25/36 | 69.4% |
| Nash | 18 | 24/36 | 66.7% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 7 | 8/14 | 57.1% |
| proof_dependency | 28 | 38/56 | 67.9% |
| parity_argument | 4 | 5/8 | 62.5% |
| theorem_summary | 3 | 4/6 | 66.7% |
| construction_role | 17 | 23/34 | 67.6% |
| analysis_step | 11 | 13/22 | 59.1% |
| endpoint_connection | 10 | 10/20 | 50.0% |

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
| `scarf_009` | Scarf | theorem_summary | 1/2 | States colorful Nonempty, but only loosely explains default/Inhabited and misses the odd-cardinality extraction. |
| `brouwer_001` | Brouwer | construction_role | 2/2 | Correctly explains Fcolor on grids, Scarf colorful rooms, room_seq, and room_point_seq. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Understands finite-image subsequence extraction, but treats the stabilized object as a coloring rather than the room color set C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Correctly says outside-C coordinates tend to zero, but misses how this pairs with coordinate inequalities to force equality. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Identifies compactness as giving a convergent subsequence, but misstates vanishing diameter as directly giving a fixed point. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Captures the broad finite-to-limit bridge, but does not clearly explain the per-color witness and transfer of x_i <= f(x)_i. |
| `brouwer_006` | Brouwer | theorem_summary | 1/2 | Covers grid rooms, subsequence, diameter, and fixed-point goal, but omits the continuity/coordinate-transfer step. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Explains deficit/tPush/pushTowardsZ as a retraction device, but does not clearly state positivity of block sums for normalization. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | States projection-after-embedding identity, but misses the exact lifted-map and project-back mechanism. |
| `product_003` | Brouwer_product | theorem_summary | 2/2 | Correctly covers f_lifted, continuity, Brouwer on the lifted map, projection back, and project_embed_id. |
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
| `brouwer_012` | Brouwer | proof_dependency | 1/2 | Mentions fixed C and subsequence g1, but misses inside-C inequalities and outside-C vanishing. |
| `brouwer_013` | Brouwer | analysis_step | 1/2 | Identifies y_seq as carrying finite inequalities through diameter and continuity, but misses the colored-witness role and z-specific limit. |
| `brouwer_014` | Brouwer | analysis_step | 1/2 | Mentions outside-C zero, nonnegativity, and sum one, but does not explain how they force outside mass zero and coordinate equality. |
| `brouwer_015` | Brouwer | endpoint_connection | 0/2 | Misdescribes C as a compact subset and says z lies outside C; misses the inside/outside coordinate split. |
| `product_008` | Brouwer_product | proof_dependency | 2/2 | Correctly explains why the tPush = 0 branch needs zero deficit and blockWeight positivity. |
| `product_009` | Brouwer_product | analysis_step | 2/2 | Correctly identifies the blockSum denominator, continuity, and nonzero/positive denominator problem. |
| `product_010` | Brouwer_product | construction_role | 1/2 | Mentions block sums matching block weights and identity, but does not clearly state deficit zero, push identity, and recovery of y. |
| `product_011` | Brouwer_product | endpoint_connection | 1/2 | Explains BigSimplex, projection back, and project_embed_id, but omits the lifted map f_lifted. |
| `nash_008` | Nash | construction_role | 1/2 | Correctly identifies positive payoff improvement from a pure deviation, but omits normalization into nash_map weights. |
| `nash_009` | Nash | analysis_step | 2/2 | Explains positive denominator, nonnegative normalized coordinates, and nash_map_cert packaging as a simplex point. |
| `nash_010` | Nash | endpoint_connection | 2/2 | Correctly explains mixed_g_linear as a weighted-sum bridge from pure to mixed deviations. |
| `nash_011` | Nash | endpoint_connection | 2/2 | Correctly states the contradiction between H1 sum_g > 1 and self_div_lemma forcing sum_g = 1 at a fixed point. |
| `nash_012` | Nash | construction_role | 2/2 | Correctly explains reindexing via phi/phi_inv into ProductSimplices to apply Brouwer_Product and transport the fixed point back. |
| `scarf_017` | Scarf | proof_dependency | 1/2 | Identifies the subset and enlarged-index monotonicity ideas, but does not tie them cleanly to the idoor and odoor cases. |
| `scarf_018` | Scarf | endpoint_connection | 1/2 | Separates the cell conclusion from the room conclusion, but blurs which endpoint is the door and which is the adjacent room. |
| `scarf_019` | Scarf | construction_role | 1/2 | Recognizes M_set and m_element as maximal-order witnesses, but does not explain the extension candidate that yields an adjacent room. |
| `scarf_020` | Scarf | proof_dependency | 1/2 | Connects disjointness to keeping the two rooms distinct, but treats M_set too loosely and misses the equal-minimum extension mechanism. |
| `scarf_021` | Scarf | proof_dependency | 1/2 | States the two image-cardinality cases, but does not explain the injective versus collision split for door construction. |
| `scarf_022` | Scarf | proof_dependency | 1/2 | Says typed near-colorfulness passes from room to door, but misses the fixed-type dbcountingset fiber used by parity. |
| `scarf_023` | Scarf | parity_argument | 2/2 | Correctly links the two distinct nearly colorful doors of a room to paired incidence contributions and evenness. |
| `scarf_024` | Scarf | proof_dependency | 1/2 | Understands that the lemma rules out extra idoor neighbors, but omits the two m_element candidates that make exhaustiveness precise. |
| `brouwer_016` | Brouwer | construction_role | 1/2 | Explains the total indexed order needed for Scarf, but misses the tie-breaking and TT.Ilt_keyprop coordinate bridge. |
| `brouwer_017` | Brouwer | proof_dependency | 1/2 | Connects dominance to analytic closeness broadly, but misstates size_bound_key and omits the minima-to-size_bound_in/out bridge. |
| `brouwer_018` | Brouwer | construction_role | 1/2 | Gets the finite-grid to continuous-simplex bridge, but does not mention rescaling by l or the simplex certificate. |
| `brouwer_019` | Brouwer | analysis_step | 1/2 | Mentions outside-C bounds and refined denominators, but misdescribes the bound before the zero-limit conclusion. |
| `brouwer_020` | Brouwer | analysis_step | 1/2 | Explains shrinking room diameter and a common limit, but misses the colored-witness to representative inequality transfer. |
| `product_012` | Brouwer_product | definition_role | 2/2 | Correctly distinguishes the flattened BigSimplex from the blockwise product representation and names the embed/project bridge. |
| `product_013` | Brouwer_product | construction_role | 2/2 | Correctly explains the interval bound as the convex-combination condition preserving the simplex during the push. |
| `product_014` | Brouwer_product | proof_dependency | 2/2 | Correctly describes the old block mass and target blockWeight decomposition and its positivity role before projection. |
| `product_015` | Brouwer_product | proof_dependency | 1/2 | Explains positive blockWeight from positive cardinalities, but does not connect that positivity to the projection division. |
| `product_016` | Brouwer_product | construction_role | 1/2 | Identifies normalization by blockSum, but does not spell out the per-block sum-one ProductSimplices output. |
| `product_017` | Brouwer_product | proof_dependency | 1/2 | Mentions continuity of projection and embedding for Brouwer, but does not reconstruct the full project-f-embed lifted composite. |
| `product_018` | Brouwer_product | endpoint_connection | 1/2 | Recognizes that project_embed_id is the endpoint identity, but overstates the inverse relationship and misses the one-sided rewrite. |
| `nash_013` | Nash | definition_role | 1/2 | Explains unilateral mixed deviations and mixed_g, but does not mention the Function.update representation. |
| `nash_014` | Nash | construction_role | 1/2 | Identifies simplex strategy spaces in the mixed extension, but misses the expected-payoff package and endpoint interpretation. |
| `nash_015` | Nash | proof_dependency | 1/2 | Notes continuity of g_function feeding nash_map continuity, but omits denominator sums and continuity of division. |
| `nash_016` | Nash | proof_dependency | 1/2 | Names the maximizing pure strategy, but misses the weighted-average bound and the use of H t for arbitrary mixed deviations. |
| `nash_017` | Nash | analysis_step | 1/2 | Mentions a nonzero coordinate and payoff inequality, but misses zero improvement and the self-division equation. |
| `nash_018` | Nash | endpoint_connection | 1/2 | Recognizes phi/phi_inv fixed-point transport, but reverses the conjugation direction and omits the inverse-identity rewrite. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
