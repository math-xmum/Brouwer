# kimina-prover:7b brouwerbench_v1 Report

## Summary

- Model: `kimina-prover:7b`
- Dataset: `data/brouwerbench_v1.jsonl`
- Raw results: `results/brouwerbench_v1__kimina-prover_7b.jsonl`
- Manual scores: `scores/brouwerbench_v1__kimina-prover_7b.manual.jsonl`
- Tasks: 80
- Score: 58/160 (36.2%)
- Total elapsed: 986.41s
- Average elapsed per task: 12.33s
- Decode speed: 39.01 tokens/s

## Scores By Section

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| Scarf | 24 | 14/48 | 29.2% |
| Brouwer | 20 | 12/40 | 30.0% |
| Brouwer_product | 18 | 14/36 | 38.9% |
| Nash | 18 | 18/36 | 50.0% |

## Scores By Task Type

| Group | Tasks | Score | Percent |
|---|---:|---:|---:|
| definition_role | 7 | 6/14 | 42.9% |
| proof_dependency | 28 | 20/56 | 35.7% |
| parity_argument | 4 | 1/8 | 12.5% |
| theorem_summary | 3 | 1/6 | 16.7% |
| construction_role | 17 | 16/34 | 47.1% |
| analysis_step | 11 | 9/22 | 40.9% |
| endpoint_connection | 10 | 5/20 | 25.0% |

## Item Scores

| ID | Section | Type | Score | Note |
|---|---|---|---:|---|
| `scarf_001` | Scarf | definition_role | 0/2 | Misstates the dominance quantifier and confuses the cardinality conditions for isCell/isRoom/isDoor. |
| `scarf_002` | Scarf | proof_dependency | 1/2 | Mentions minima and the eventual cardinality bound, but misses the image-of-C mechanism and gives an incorrect proof story. |
| `scarf_003` | Scarf | definition_role | 1/2 | Recognizes point insertion versus index insertion, but confuses the constructors and misses incidence counting. |
| `scarf_004` | Scarf | definition_role | 1/2 | Partially distinguishes image/missing/typed variants, but confuses colors with dominance and misses the parity role. |
| `scarf_005` | Scarf | proof_dependency | 1/2 | Says room_of_colorful is used before picking a point, but misses the nonempty/cardinality sandwich. |
| `scarf_006` | Scarf | parity_argument | 0/2 | Hallucinates unrelated near-critical/square counts and does not describe dbcountingset incidences. |
| `scarf_007` | Scarf | proof_dependency | 0/2 | Replaces the outside-door singleton count with an unrelated handshaking-style graph argument. |
| `scarf_008` | Scarf | parity_argument | 1/2 | Mentions odd/even reasoning and existence broadly, but misses the exact colorful-room count and nonempty-filter step. |
| `scarf_009` | Scarf | theorem_summary | 0/2 | Gives a largely incorrect pigeonhole/same-color account and misses default/Inhabited extraction. |
| `brouwer_001` | Brouwer | construction_role | 0/2 | Describes iterating f and compactness rather than Scarf, Fcolor, finite grids, and room_point_seq. |
| `brouwer_002` | Brouwer | proof_dependency | 1/2 | Mentions a finite-image constant subsequence, but gives an incorrect iteration/cycle story and misses constant C. |
| `brouwer_003` | Brouwer | analysis_step | 1/2 | Correctly says outside-C coordinates tend to zero, but misses the inside-C coordinate inequalities and final equality role. |
| `brouwer_004` | Brouwer | analysis_step | 1/2 | Mentions compactness/convergent subsequence and vanishing diameter, but misses transfer of colored-point inequalities. |
| `brouwer_005` | Brouwer | proof_dependency | 1/2 | Recognizes finite rooms leading to coordinate inequalities at the limit, but misses colored witnesses and continuity details. |
| `brouwer_006` | Brouwer | theorem_summary | 0/2 | Describes an incorrect counting/pigeonhole proof rather than the Scarf-room, subsequence, diameter, and continuity strategy. |
| `product_001` | Brouwer_product | definition_role | 1/2 | Partially explains deficit, tPush, pushTowardsZ, and blockSum, but misses positive block sums as the normalization prerequisite. |
| `product_002` | Brouwer_product | proof_dependency | 1/2 | Identifies projection/embedding as a retraction idea, but confuses directions and omits the lifted-map transfer. |
| `product_003` | Brouwer_product | theorem_summary | 1/2 | Mentions f_lifted and continuity, but drifts into componentwise fixed points and misses the project_embed_id retraction step. |
| `nash_001` | Nash | definition_role | 1/2 | Describes mixed strategies as products of simplices and expected payoff, but omits mixedS details and unilateral deviations. |
| `nash_002` | Nash | construction_role | 1/2 | Mentions payoff-improvement/best-response intuition, normalization, continuity, and fixed point, but incorrectly frames pure equilibrium. |
| `nash_003` | Nash | endpoint_connection | 0/2 | Describes game structures but misses Brouwer.mixedGame, nash_map fixed point, pure deviations, and mixed_g_linear. |
| `scarf_010` | Scarf | proof_dependency | 1/2 | Gets the two-rooms-even intuition, but misses the fiber-over-internal-door packaging and adds unrelated hypergraph claims. |
| `scarf_011` | Scarf | proof_dependency | 0/2 | Hallucinates a pigeonhole/coloring argument and does not state the typed nearly colorful versus colorful partition. |
| `scarf_012` | Scarf | parity_argument | 0/2 | Does not explain two nearly colorful doors or the size-two fiber; gives an unrelated pairing argument. |
| `brouwer_007` | Brouwer | construction_role | 1/2 | Mentions TT finite grids and indexed order, but misses the division-by-l coercion and adds incorrect finite-repetition reasoning. |
| `brouwer_008` | Brouwer | analysis_step | 0/2 | Misstates the size-bound lemmas as finite-search bounds and misses dominance, diameter, and outside-C vanishing. |
| `brouwer_009` | Brouwer | proof_dependency | 1/2 | Mentions stabilizing a constant color pattern/subsequence, but misses outside-C and inside-C coordinate estimates. |
| `brouwer_010` | Brouwer | analysis_step | 0/2 | Gives a generic fixed-point statement and misses outside-C zero, sum one, coordinate inequalities, and extensionality. |
| `product_004` | Brouwer_product | construction_role | 1/2 | Explains flat-to-block index translation and inverse functions, but misses the sum-changing/blockSum role. |
| `product_005` | Brouwer_product | construction_role | 1/2 | Mentions blockWeight scaling and block-sum equality, but confuses the formula and misses sum-to-one/project_embed_id recovery. |
| `product_006` | Brouwer_product | proof_dependency | 0/2 | Incorrectly claims projection is not continuous in product topology and misses the Continuous.div denominator argument. |
| `product_007` | Brouwer_product | proof_dependency | 1/2 | Recognizes the tPush case split and blockWeight positivity, but misses zero deficit and misstates the tPush=0 branch. |
| `nash_004` | Nash | proof_dependency | 1/2 | Explains linearity of expected payoff generally, but does not clearly state the convex weighted sum of pure deviations. |
| `nash_005` | Nash | construction_role | 1/2 | Mentions reindex/map_simplex representation changes, but misses Fintype.equivFin, ProductSimplices, and fixed-point transport. |
| `nash_006` | Nash | construction_role | 1/2 | Mentions g_function, nonnegativity, and one_le_sum_g, but misses normalization to sum one and nash_map_cert. |
| `nash_007` | Nash | endpoint_connection | 1/2 | Mentions H1 and a fixed-point contradiction, but the mechanism is incorrect and omits sum_g=1 from self_div_lemma. |
| `scarf_013` | Scarf | proof_dependency | 2/2 | Correctly identifies outside doors as empty point set with singleton color and uniqueness up to the fixed type. |
| `scarf_014` | Scarf | proof_dependency | 0/2 | Hallucinates an unrelated parity/counting theorem and does not explain fiber_size_internal_door. |
| `scarf_015` | Scarf | proof_dependency | 1/2 | Partially identifies NC_of_outsidedoor and NC_or_C_of_door, but misclassifies the room alternatives and misses colorful partition. |
| `scarf_016` | Scarf | endpoint_connection | 0/2 | Incorrectly claims filters are automatically nonempty and misses odd positive cardinality, choice, and default. |
| `brouwer_011` | Brouwer | construction_role | 0/2 | Explains Fcolor via Brouwer fixed points rather than stdSimplex.pick and the x_i <= f(x)_i coordinate. |
| `brouwer_012` | Brouwer | proof_dependency | 0/2 | Gives a generic dense-grid contradiction story and does not connect gpkg to fixed C and g1. |
| `brouwer_013` | Brouwer | analysis_step | 2/2 | Correctly explains y_seq as selecting colored witnesses and using diameter control plus continuity to pass inequalities to the limit. |
| `brouwer_014` | Brouwer | analysis_step | 0/2 | Hallucinates Borsuk-Ulam/origin arguments and misses outside-C zero, nonnegativity, sum one, and coordinate equality. |
| `brouwer_015` | Brouwer | endpoint_connection | 0/2 | Misdescribes C as a barrier/attracting region and misses the inside/outside coordinate split. |
| `product_008` | Brouwer_product | proof_dependency | 1/2 | Mentions tPush=0, deficit, blockWeight, and positivity, but the zero-deficit argument is wrong. |
| `product_009` | Brouwer_product | analysis_step | 1/2 | Recognizes a division-by-blockSum denominator issue, but incorrectly claims the denominator is always one. |
| `product_010` | Brouwer_product | construction_role | 1/2 | Mentions blockSum/blockWeight/deficit, but gives an incorrect construction and does not explain recovering y. |
| `product_011` | Brouwer_product | endpoint_connection | 1/2 | Mentions BigSimplex, f_lifted, and projecting back, but omits project_embed_id and has a loose endpoint equation. |
| `nash_008` | Nash | construction_role | 2/2 | Correctly explains the max term as positive payoff improvement from pure deviation and connects it to nash_map normalization. |
| `nash_009` | Nash | analysis_step | 2/2 | Explains one_le_sum_g, g_function_noneg, normalization, and nash_map_cert despite extra irrelevant proof text. |
| `nash_010` | Nash | endpoint_connection | 1/2 | Gives the linearity-of-expectation intuition, but does not clearly formulate mixed_g_linear as a weighted sum of pure-deviation payoffs. |
| `nash_011` | Nash | endpoint_connection | 1/2 | Starts with the right sum_g contradiction but omits the fixed-point/nonzero-coordinate mechanism and adds unrelated material. |
| `nash_012` | Nash | construction_role | 1/2 | Broadly describes transporting to a product of simplices and fixed point, but misses reindexing, phi_inv, and ProductSimplices specifics. |
| `scarf_017` | Scarf | proof_dependency | 1/2 | Recognizes subset and superset dominance moves, but reverses details and never ties them cleanly to the idoor and odoor constructors. |
| `scarf_018` | Scarf | endpoint_connection | 0/2 | Misstates the cell and room roles as nonempty versus empty sets and misses the door-side versus room-side incidence distinction. |
| `scarf_019` | Scarf | construction_role | 1/2 | Identifies M_set and m_element as maximal candidate machinery, but does not explain the extension witness for an adjacent room accurately. |
| `scarf_020` | Scarf | proof_dependency | 0/2 | Mentions disjointness but replaces the distinct extension-candidate argument with unrelated set-union claims. |
| `scarf_021` | Scarf | proof_dependency | 1/2 | Gets the two cardinality regimes in broad form, but misses the injective-versus-collision split used by doors_of_NCroom. |
| `scarf_022` | Scarf | proof_dependency | 0/2 | Talks about typed operations generically and never explains propagation of the fixed missing type back to the counted door fiber. |
| `scarf_023` | Scarf | parity_argument | 0/2 | States an odd-door story instead of the two-door fiber and even non-colorful-room incidence contribution. |
| `scarf_024` | Scarf | proof_dependency | 2/2 | Correctly says any inserted-room neighbor is forced to one of the two m_element candidates, giving the needed exhaustiveness. |
| `brouwer_016` | Brouwer | construction_role | 1/2 | Recognizes lexicographic indexed orders on the grid, but misses tie-breaking to a linear order and the coordinate key property. |
| `brouwer_017` | Brouwer | proof_dependency | 0/2 | Invents a distance argument about images of f and does not connect dominance to size_bound_in or size_bound_out. |
| `brouwer_018` | Brouwer | construction_role | 2/2 | Correctly explains TT grid points being rescaled into the standard simplex so finite rooms feed the limiting Brouwer argument. |
| `brouwer_019` | Brouwer | analysis_step | 0/2 | Replaces the bounded-numerator over growing-denominator mechanism with incorrect coordinate equalities. |
| `brouwer_020` | Brouwer | analysis_step | 1/2 | States that room diameters shrink on refined grids, but misses size_bound_in and the witness-to-representative limit transfer. |
| `product_012` | Brouwer_product | definition_role | 1/2 | Identifies the product-versus-single-simplex representation gap, but omits the flattened block coordinates and embed/project bridge. |
| `product_013` | Brouwer_product | construction_role | 2/2 | Correctly uses the tPush interval bounds to explain convex combination and preservation of simplex coordinates. |
| `product_014` | Brouwer_product | proof_dependency | 1/2 | States the pushed block-sum formula and positivity motivation, but does not reconstruct the blockWeight denominator argument before projection. |
| `product_015` | Brouwer_product | proof_dependency | 0/2 | Gives an incorrect sign-flip story and misses Nat+ positivity, blockWeight_pos, and division by nonzero block mass. |
| `product_016` | Brouwer_product | construction_role | 0/2 | Says normalization lands in a product simplex but gives a wrong zero-block account instead of blockSum division and sum-one blocks. |
| `product_017` | Brouwer_product | proof_dependency | 0/2 | Offers generic continuity language and never identifies the project-f-embed lifted map required by single-simplex Brouwer. |
| `product_018` | Brouwer_product | endpoint_connection | 0/2 | Confuses f with a retraction and does not explain the one-sided project-after-embed rewrite at the endpoint. |
| `nash_013` | Nash | definition_role | 1/2 | Explains unilateral mixed deviations and expected payoff broadly, but omits Function.update and the mixed_g specialization. |
| `nash_014` | Nash | construction_role | 0/2 | Answers with g_function and nash_map instead of the mixed-game package built by FinGame2MixedGame. |
| `nash_015` | Nash | proof_dependency | 2/2 | Correctly connects cg to coordinate numerators, finite denominator sums, nonzero division, and continuity of nash_map. |
| `nash_016` | Nash | proof_dependency | 0/2 | Does not explain the maximizing pure response or its weighted-average bound for arbitrary mixed deviations. |
| `nash_017` | Nash | analysis_step | 1/2 | Recognizes a weighted payoff witness and a payoff inequality, but misses the nonzero-coordinate and self_div_lemma contradiction mechanism. |
| `nash_018` | Nash | endpoint_connection | 1/2 | Says conjugation lets Brouwer run on a simplex and fixed points correspond back, but omits phi, ProductSimplices, and the pullback rewrite. |

## Takeaways

- Definition-role questions are usually answered at the right abstraction level.
- The model often misses proof-specific mechanisms unless the prompt forces exact Lean names.
- Product and Nash endpoint questions are useful stress tests because generic answers are easy but incomplete.
